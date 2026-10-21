#!/usr/bin/env python3
"""Sequential, cache-aware validation for the semantic architecture migration."""
from pathlib import Path
import argparse,hashlib,json,os,re,resource,shlex,subprocess,sys,time,graphlib
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1]
OUT=ROOT/'results/for-mathlib';OUT.mkdir(parents=True,exist_ok=True)
M=json.loads((HERE/'migration.json').read_text());REF=ROOT/M['reference']
METRICS=[]

def run(label,cmd,cwd=HERE,env=None):
 start=time.monotonic();before=resource.getrusage(resource.RUSAGE_CHILDREN)
 with (OUT/(label+'.log')).open('w') as log:
  result=subprocess.run(cmd,cwd=cwd,env=env,stdout=log,stderr=subprocess.STDOUT)
 after=resource.getrusage(resource.RUSAGE_CHILDREN)
 record=dict(label=label,command=cmd,cwd=str(cwd.relative_to(ROOT)),exit_code=result.returncode,wall_seconds=time.monotonic()-start,user_seconds=after.ru_utime-before.ru_utime,system_seconds=after.ru_stime-before.ru_stime,children_max_rss_kib_so_far=after.ru_maxrss)
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
 frozen=['experiments/kl','experiments/kl-signed-ranks','experiments/kl-kernel-transport','experiments/kl-architecture','scripts','provenance']
 run('frozen-tree',['git','diff','--exit-code',M['publication_checkpoint'],'--',*frozen],ROOT)
 extra=subprocess.check_output(['git','ls-files','--others','--exclude-standard','--',*frozen],cwd=ROOT,text=True)
 if extra.strip():raise RuntimeError('Untracked files in frozen reference: '+extra)
 run('baseline-identity',[sys.executable,'scripts/verify.py'],ROOT)
 run('source-transport',[sys.executable,'migrate.py','--check'])
 run('source-coverage',[sys.executable,'source_check.py'])
 run('classification-and-boundaries',[sys.executable,'analyze.py'])
 if M.get('expected_public_count')!=3902:raise RuntimeError('Expected fixed coverage of 3902 public declarations')
 modules=M['modules'];legacy=set(M['legacy_shims'])
 old_exporter=(ROOT/M['previous_experiment']/'PublicTypes.lean').read_text()
 expected_exporter=old_exporter.replace('if moduleName.toString.startsWith "OAI." then',
   'if moduleName.toString.startsWith "OAI." || moduleName.toString.startsWith "ForMathlib." then')
 if expected_exporter==old_exporter or (HERE/'PublicTypes.lean').read_text()!=expected_exporter:
  raise RuntimeError('Only the ForMathlib owned-module selector may differ in the exporter')
 old_snapshot=json.loads((ROOT/M['previous_experiment']/'reference-public-types.json').read_text())
 new_snapshot=json.loads((HERE/'reference-public-types.json').read_text())
 for snapshot in (old_snapshot,new_snapshot):snapshot.pop('exporter_sha256')
 if old_snapshot!=new_snapshot:raise RuntimeError('Changed reference declaration snapshot or type policy')
 previous=json.loads((ROOT/M['previous_experiment']/'migration.json').read_text())
 for key in ('reference','reference_commit','source_hashes','fixed','units','instance_annotations'):
  if M[key]!=previous[key]:raise RuntimeError('Changed inherited source/provenance field: '+key)
 used=[u for x in modules.values() for u in x['units']]
 if len(used)!=len(set(used)) or set(used)!={u['id'] for u in M['units']}:
  raise RuntimeError('Source units must be allocated exactly once')
 known=set(modules)|{'ForMathlib.LinearAlgebra.KernelTransport','OAI.KL.Compatibility.KernelTransport'}
 if any(d not in known for x in modules.values() for d in x['imports']):raise RuntimeError('Unknown implementation dependency')
 old_names=set(previous['modules'])|{'OAI.LinearAlgebra.KernelTransport','OAI.RepresentationTheory.KazhdanLusztig.KernelTransportCompat'}
 mapping=M['module_renames'];splits=M.get('split_module_imports',{})
 if set(mapping)&set(splits) or set(mapping)|set(splits)!=old_names:
  raise RuntimeError('Incomplete or ambiguous previous module import map')
 if any(d not in known for d in mapping.values()) or any(not ds or any(d not in known for d in ds) for ds in splits.values()):
  raise RuntimeError('Import map targets an absent implementation')
 assessment=json.loads((HERE/'upstream-assessment.json').read_text())
 if {x['module'] for x in assessment['modules']}!=set(previous['modules']) or len(assessment['modules'])!=len(previous['modules']):
  raise RuntimeError('Incomplete prior-module assessment coverage')
 for name in ('compare_types.py','test_compare_types.py','source_check.py'):
  if (HERE/name).read_bytes()!=(ROOT/M['previous_experiment']/name).read_bytes():
   raise RuntimeError('Changed inherited verification policy: '+name)
 for n,x in modules.items():
  for dep in x['imports']:
   if dep in legacy:raise RuntimeError('Implementation imports a compatibility entry: '+n+' -> '+dep)
   if n.startswith('ForMathlib.') and not dep.startswith('ForMathlib.'):
    raise RuntimeError('ForMathlib imports project implementation: '+n+' -> '+dep)
  if n.startswith(('ForMathlib.Algebra.','ForMathlib.LinearAlgebra.','ForMathlib.Analysis.','ForMathlib.RingTheory.','ForMathlib.Order.')):
   if any(d.startswith(('ForMathlib.RepresentationTheory.','ForMathlib.GroupTheory.','ForMathlib.Combinatorics.MomentGraph.')) for d in x['imports']):
    raise RuntimeError('General support imports domain theory: '+n)
  if n.startswith('ForMathlib.GroupTheory.Coxeter.') and any(d.startswith('ForMathlib.RepresentationTheory.') for d in x['imports']):
   raise RuntimeError('Coxeter object layer imports representation theory: '+n)
  if n.startswith('ForMathlib.Combinatorics.MomentGraph.') and not n.startswith('ForMathlib.Combinatorics.MomentGraph.Bruhat.'):
   if any(d.startswith(('ForMathlib.GroupTheory.','ForMathlib.RepresentationTheory.')) for d in x['imports']):raise RuntimeError('General sheaf interface imports a Coxeter model: '+n)
 list(graphlib.TopologicalSorter({n:set(x['imports']) for n,x in modules.items()}).static_order())
 # No new mathematical declaration can hide in a file outside the deterministic products.
 allowed={M['fixed_destinations'].get(p,p) for p in M['fixed']}|{n.replace('.','/')+'.lean' for n in modules}|{n.replace('.','/')+'.lean' for n in legacy}|{'OAI/Architecture.lean','PublicTypes.lean','ImportChecks.lean','DomainImportChecks.lean','ForMathlibChecks.lean','ForMathlib.lean'}
 actual={str(p.relative_to(HERE)) for p in HERE.rglob('*.lean') if '.lake' not in p.parts}
 if actual-allowed:raise RuntimeError('Unlisted Lean source: '+str(actual-allowed))
 for p in list((HERE/'OAI').rglob('*.lean'))+list((HERE/'ForMathlib').rglob('*.lean')):
  if re.search(r'\b(sorry|admit|unsafe)\b',p.read_text()):raise RuntimeError('Unexpected proof bypass token: '+str(p))


def main():
 parser=argparse.ArgumentParser();parser.add_argument('--static',action='store_true');parser.add_argument('--refresh-reference',action='store_true',help='Re-export the warm reference and verify its committed snapshot');parser.add_argument('--checks-only',action='store_true',help='Require all OAI artifacts warm, then verify interfaces without rebuilding them');args=parser.parse_args()
 static_checks()
 if args.static:return
 packages=HERE/'.lake/packages';packages.parent.mkdir(exist_ok=True)
 if not packages.exists() and not packages.is_symlink():packages.symlink_to('../../kl/.lake/packages')
 if packages.resolve()!=(ROOT/'experiments/kl/.lake/packages').resolve():raise RuntimeError('Unexpected dependency checkout; expected the verified shared baseline')
 env=serial_environment()
 run('lean-version',['lake','env','lean','--version'],env=env)
 run('mathlib-ready',['lake','--no-build','build','Mathlib'],env=env)
 if args.checks_only:run('oai-ready',['lake','--no-build','build','ForMathlib','OAI'],env=env)
 else:run('library-build',['lake','build','ForMathlib','OAI'],env=env)
 for file in ('ForMathlibChecks','ImportChecks','DomainImportChecks','KernelChecks','CompatChecks','BoundaryChecks','Audit'):
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
 if snapshot.get('schema')!=3 or snapshot.get('public_count')!=3902 or len(snapshot.get('types',{}))!=3902:raise RuntimeError('Incomplete reference public-type coverage')
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
 run('warm-build',['lake','build','ForMathlib','OAI'],env=env)
 print('ForMathlib staging and project-layout validation passed.',flush=True)
if __name__=='__main__':main()
