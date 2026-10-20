#!/usr/bin/env python3
"""Sequential, cache-aware validation for the semantic architecture migration."""
from pathlib import Path
import argparse,hashlib,json,os,re,resource,shlex,subprocess,sys,time,graphlib
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1]
OUT=ROOT/'results/architecture';OUT.mkdir(parents=True,exist_ok=True)
M=json.loads((HERE/'migration.json').read_text());REF=ROOT/M['reference']
METRICS=[]

def run(label,cmd,cwd=HERE,env=None):
 start=time.monotonic();before=resource.getrusage(resource.RUSAGE_CHILDREN)
 with (OUT/(label+'.log')).open('w') as log:
  result=subprocess.run(cmd,cwd=cwd,env=env,stdout=log,stderr=subprocess.STDOUT)
 after=resource.getrusage(resource.RUSAGE_CHILDREN)
 record=dict(label=label,command=cmd,cwd=str(cwd.relative_to(ROOT)),exit_code=result.returncode,wall_seconds=time.monotonic()-start,user_seconds=after.ru_utime-before.ru_utime,system_seconds=after.ru_stime-before.ru_stime,max_rss_kib=after.ru_maxrss)
 METRICS.append(record);(OUT/'stages.json').write_text(json.dumps(METRICS,indent=2)+'\n');print(json.dumps(record),flush=True)
 if result.returncode:
  print((OUT/(label+'.log')).read_text()[-6000:]);raise RuntimeError('Failed stage: '+label)
 return (OUT/(label+'.log')).read_text()

def serial_environment():
 env=os.environ.copy()
 real=Path(subprocess.check_output(['lean','--print-prefix'],cwd=REF,text=True).strip()).resolve()
 gate=ROOT/'.cache/architecture-serial-toolchain';gate.mkdir(exist_ok=True)
 for p in real.iterdir():
  if p.name!='bin' and not (gate/p.name).exists():(gate/p.name).symlink_to(p)
 (gate/'bin').mkdir(exist_ok=True)
 for p in (real/'bin').iterdir():
  if p.name!='lean' and not (gate/'bin'/p.name).exists():(gate/'bin'/p.name).symlink_to(p)
 wrapper=gate/'bin/lean'
 text='#!/usr/bin/env bash\nset -euo pipefail\nexec flock '+shlex.quote(str(ROOT/'.cache/architecture-compile.lock'))+' '+shlex.quote(str(real/'bin/lean'))+' "$@"\n'
 if not wrapper.exists() or wrapper.read_text()!=text:wrapper.write_text(text);wrapper.chmod(0o755)
 env.update(LEAN_SYSROOT=str(gate),LAKE_OVERRIDE_LEAN='true')
 return env

def static_checks():
 # All prior source and tooling remains recoverable and unchanged, including
 # the original strict comparator and its fixed exception policy.
 frozen=['experiments/kl','experiments/kl-signed-ranks','experiments/kl-kernel-transport','scripts','provenance']
 run('frozen-tree',['git','diff','--exit-code',M['reference_commit'],'--',*frozen],ROOT)
 extra=subprocess.check_output(['git','ls-files','--others','--exclude-standard','--',*frozen],cwd=ROOT,text=True)
 if extra.strip():raise RuntimeError('Untracked files in frozen reference: '+extra)
 run('baseline-identity',[sys.executable,'scripts/verify.py'],ROOT)
 run('source-transport',[sys.executable,'migrate.py','--check'])
 run('source-coverage',[sys.executable,'source_check.py'])
 modules=M['modules'];legacy=set(M['legacy_shims'])
 for n,x in modules.items():
  for dep in x['imports']:
   if dep in legacy:raise RuntimeError('Semantic implementation imports a legacy shim: '+n+' -> '+dep)
  if n.startswith(('OAI.Algebra.','OAI.LinearAlgebra.','OAI.Data.','OAI.RingTheory.','OAI.Order.')):
   if any(d.startswith(('OAI.RepresentationTheory.','OAI.GroupTheory.','OAI.Combinatorics.MomentGraph.')) for d in x['imports']):
    raise RuntimeError('Foundational module imports a domain application: '+n)
  if n.startswith('OAI.GroupTheory.Coxeter.') and any(d.startswith('OAI.RepresentationTheory.') for d in x['imports']):
   raise RuntimeError('Coxeter object layer imports a representation application: '+n)
  if n.startswith('OAI.Combinatorics.MomentGraph.') and not n.startswith('OAI.Combinatorics.MomentGraph.Bruhat.'):
   if any(d.startswith(('OAI.GroupTheory.','OAI.RepresentationTheory.')) for d in x['imports']):raise RuntimeError('General sheaf API imports a concrete model: '+n)
 list(graphlib.TopologicalSorter({n:set(x['imports']) for n,x in modules.items()}).static_order())
 # No new mathematical declaration can hide in a file outside the deterministic products.
 allowed=set(M['fixed'])|{n.replace('.','/')+'.lean' for n in modules}|{n.replace('.','/')+'.lean' for n in legacy}|{'OAI/Architecture.lean','PublicTypes.lean','ImportChecks.lean'}
 actual={str(p.relative_to(HERE)) for p in HERE.rglob('*.lean') if '.lake' not in p.parts}
 if actual-allowed:raise RuntimeError('Unlisted Lean source: '+str(actual-allowed))
 for p in (HERE/'OAI').rglob('*.lean'):
  if re.search(r'\b(sorry|admit|unsafe)\b',p.read_text()):raise RuntimeError('Unexpected proof bypass token: '+str(p))


def main():
 parser=argparse.ArgumentParser();parser.add_argument('--static',action='store_true');parser.add_argument('--refresh-reference',action='store_true',help='Re-export the warm reference and verify its committed snapshot');parser.add_argument('--checks-only',action='store_true',help='Require all OAI artifacts warm, then verify interfaces without rebuilding them');args=parser.parse_args()
 static_checks()
 if args.static:return
 packages=HERE/'.lake/packages';packages.parent.mkdir(exist_ok=True)
 if not packages.exists():packages.symlink_to('../../kl/.lake/packages')
 if packages.resolve()!=(ROOT/'experiments/kl/.lake/packages').resolve():raise RuntimeError('Unexpected dependency checkout; expected the verified shared baseline')
 env=serial_environment()
 run('lean-version',['lake','env','lean','--version'],env=env)
 run('mathlib-ready',['lake','--no-build','build','Mathlib'],env=env)
 if args.checks_only:run('oai-ready',['lake','--no-build','build','OAI'],env=env)
 else:run('library-build',['lake','build','OAI'],env=env)
 for file in ('ImportChecks','KernelChecks','CompatChecks','BoundaryChecks','Audit'):
  run(file,['lake','env','lean',file+'.lean'],env=env)
 audit=(OUT/'Audit.log').read_text();records=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",audit,re.S)
 if len(records)!=16:raise RuntimeError('Expected sixteen complete axiom closures, got '+str(len(records)))
 allowed={'propext','Quot.sound','Classical.choice'}
 for theorem,axioms in records:
  found=set(re.findall(r'[A-Za-z_][A-Za-z_.]*',axioms))
  if not found<=allowed:raise RuntimeError('Disallowed axiom for '+theorem+': '+str(found-allowed))
  if theorem=='OAI.KLInvariance.combinatorial_invariance' and found!=allowed:raise RuntimeError('Unexpected main theorem axiom closure')
 # The reference snapshot avoids a second full library build on fresh workers.
 # --refresh-reference checks it using the identical exporter in the warm old environment.
 snapshot=json.loads((HERE/'reference-public-types.json').read_text())
 if snapshot['reference_commit']!=M['reference_commit'] or snapshot['exporter_sha256']!=hashlib.sha256((HERE/'PublicTypes.lean').read_bytes()).hexdigest():
  raise RuntimeError('Reference type snapshot provenance mismatch')
 if args.refresh_reference:
  run('reference-ready',['lake','--no-build','build','OAI'],REF,env)
  source=(HERE/'PublicTypes.lean').read_text();baseline=OUT/'ReferenceTypes.lean'
  baseline.write_text(source.replace('import OAI.Architecture','import OAI.RepresentationTheory.KazhdanLusztig.Invariance',1))
  run('reference-types',['lake','env','lean',str(baseline)],REF,dict(env,LEAN_TYPES_OUT=str(OUT/'reference-types.tsv')))
  run('reference-snapshot-check',[sys.executable,'compare_types.py','reference-public-types.json',str(OUT/'reference-types.tsv')])
 run('migrated-types',['lake','env','lean','PublicTypes.lean'],env=dict(env,LEAN_TYPES_OUT=str(OUT/'migrated-types.tsv')))
 run('type-comparison',[sys.executable,'compare_types.py','reference-public-types.json',str(OUT/'migrated-types.tsv')])
 run('comparator-tests',[sys.executable,'test_compare_types.py'])
 run('warm-build',['lake','build','OAI'],env=env)
 print('Semantic migration validation passed.',flush=True)
if __name__=='__main__':main()
