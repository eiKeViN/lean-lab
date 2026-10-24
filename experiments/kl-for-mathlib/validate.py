#!/usr/bin/env python3
"""Sequential, cache-aware validation for the semantic architecture migration."""
from pathlib import Path
import argparse,hashlib,json,os,re,resource,shlex,subprocess,sys,time,graphlib
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1]
OUT=ROOT/'results/for-mathlib';OUT.mkdir(parents=True,exist_ok=True)
sys.path.insert(0,str(ROOT/'scripts'))
from baseline import snapshot, configuration
sys.path.insert(0,str(HERE))
from source_partitions import expand_units
M=json.loads((HERE/'migration.json').read_text())
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
 real=Path(subprocess.check_output(['lean','--print-prefix'],cwd=HERE,text=True).strip()).resolve()
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
 # Historical trees are immutable Git objects, not maintained experiments.
 projects={p.name for p in (ROOT/'experiments').iterdir() if p.is_dir() and not p.name.startswith('.')}
 if projects!={'kl-for-mathlib'}:raise RuntimeError('Expected the single maintained Lean project: '+repr(projects))
 run('baseline-identity',[sys.executable,'scripts/verify.py'],ROOT)
 run('baseline-export',[sys.executable,'scripts/baseline.py','--export-out',str(OUT/'baseline-types.tsv')],ROOT)
 run('baseline-snapshot-check',[sys.executable,'compare_types.py','reference-public-types.json',str(OUT/'baseline-types.tsv')])
 run('source-transport',[sys.executable,'migrate.py','--check'])
 run('source-coverage',[sys.executable,'source_check.py'])
 run('classification-and-boundaries',[sys.executable,'analyze.py'])
 run('proof-evolution-source',[sys.executable,'proof_evolution.py','--check'])
 from module_integration import policy as module_policy, generated_checks
 from module_rollout import policy as rollout_policy, generated_checks as rollout_checks
 from attach_module import policy as attach_policy, generated_checks as attach_checks
 from module_next import policy as next_policy, generated_checks as next_checks
 from module_final import policy as final_policy
 from module_all import policy as all_policy
 all_policy()
 final_policy()
 next_policy()
 attach_policy()
 rollout_policy()
 module_policy()
 for path,text in {**generated_checks(),**rollout_checks(),**attach_checks(),**next_checks()}.items():
  if (HERE/path).read_text()!=text:raise RuntimeError('Changed generated module audit: '+path)
 if M.get('expected_public_count')!=3902:raise RuntimeError('Expected fixed coverage of 3902 public declarations')
 from proof_evolution import active_modules
 modules=active_modules(M['modules']);legacy=set(M['legacy_shims'])
 policy=snapshot('architecture')
 if policy.commit!=M['publication_checkpoint'] or policy.prefix!=M['policy_git_prefix']:raise RuntimeError('Unexpected policy Git baseline')
 source=snapshot('transport')
 if source.commit!=M['reference_commit'] or source.prefix!=M['reference']:raise RuntimeError('Unexpected source Git baseline')
 old_exporter=policy.read_text('PublicTypes.lean')
 expected_exporter=old_exporter.replace('if moduleName.toString.startsWith "OAI." then',
   'if moduleName.toString.startsWith "OAI." || moduleName.toString.startsWith "ForMathlib." then')
 if expected_exporter==old_exporter or (HERE/'PublicTypes.lean').read_text()!=expected_exporter:
  raise RuntimeError('Only the ForMathlib owned-module selector may differ in the exporter')
 old_snapshot=json.loads(policy.read_text('reference-public-types.json'))
 new_snapshot=json.loads((HERE/'reference-public-types.json').read_text())
 for record in (old_snapshot,new_snapshot):record.pop('exporter_sha256')
 if old_snapshot!=new_snapshot:raise RuntimeError('Changed reference declaration snapshot or type policy')
 previous=json.loads(policy.read_text('migration.json'))
 for key in ('reference','reference_commit','source_hashes','fixed','units','instance_annotations'):
  if M[key]!=previous[key]:raise RuntimeError('Changed inherited source/provenance field: '+key)
 expanded=expand_units(M['units'],M.get('unit_partitions',{}),source.read_text)
 used=[u for x in modules.values() for u in x['units']]
 if len(used)!=len(set(used)) or set(used)!={u['id'] for u in expanded}:
  raise RuntimeError('Source units must be allocated exactly once')
 known=set(modules)|{'ForMathlib.LinearAlgebra.KernelTransport','OAI.KL.Compatibility.KernelTransport'}
 if M.get('entrypoints')!={'OAI.KL':['OAI.KL.Invariance.Main']}:
  raise RuntimeError('Expected the stable KL theorem entrypoint')
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
 for name in ('compare_types.py','test_compare_types.py'):
  if (HERE/name).read_bytes()!=policy.read_bytes(name):
   raise RuntimeError('Changed inherited verification policy: '+name)
 expected_coverage=policy.read_text('source_check.py').replace('import json,re','import json,re,sys')
 expected_coverage=expected_coverage.replace('HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1]\n',
   'HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1]\nsys.path.insert(0,str(ROOT/"scripts"))\nfrom baseline import snapshot\n')
 expected_coverage=expected_coverage.replace("source=(ROOT/m['reference']/f).read_text()", "source=snapshot('transport').read_text(f)")
 if (HERE/'source_check.py').read_text()!=expected_coverage:raise RuntimeError('Source coverage must retain the historical algorithm with only Git I/O adapted')
 snapshot_data=json.loads((HERE/'reference-public-types.json').read_text())
 export=configuration()['reference_export']
 if snapshot_data['reference_commit']!=M['reference_commit'] or snapshot_data['exporter_sha256']!=hashlib.sha256((HERE/'PublicTypes.lean').read_bytes()).hexdigest() or export['exporter_sha256']!=snapshot_data['exporter_sha256']:
  raise RuntimeError('Reference type/exporter provenance mismatch')
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
  if n.startswith('ForMathlib.Combinatorics.MomentGraph.Sheaf.'):
   if any(d.startswith(('ForMathlib.Algebra.Module.Graded.','ForMathlib.Combinatorics.MomentGraph.GradedSheaf.','ForMathlib.Combinatorics.MomentGraph.Boundary.')) for d in x['imports']):
    raise RuntimeError('Ordinary sheaf core imports graded construction: '+n)
  if n.startswith('ForMathlib.Combinatorics.MomentGraph.') and not n.startswith('ForMathlib.Combinatorics.MomentGraph.Bruhat.'):
   if any(d.startswith(('ForMathlib.GroupTheory.','ForMathlib.RepresentationTheory.')) for d in x['imports']):raise RuntimeError('General sheaf interface imports a Coxeter model: '+n)
 list(graphlib.TopologicalSorter({n:set(x['imports']) for n,x in modules.items()}).static_order())
 # Compatibility imports may retain other compatibility entries, but never cycles
 # or absent targets; implementations still may not depend on these umbrellas.
 for n,ds in M['legacy_shims'].items():
  if n.startswith('ForMathlib.') and any(d.startswith('OAI.') for d in ds):
   raise RuntimeError('ForMathlib compatibility entry imports the project: '+n)
  if any(d not in known|legacy|{'Mathlib'} for d in ds):
   raise RuntimeError('Unknown compatibility dependency: '+n)
 combined={n:set(x['imports']) for n,x in modules.items()}
 combined.update({n:set(ds)-{'Mathlib'} for n,ds in M['legacy_shims'].items()})
 list(graphlib.TopologicalSorter(combined).static_order())
 # No new mathematical declaration can hide in a file outside the deterministic products.
 allowed={'SemanticApiChecks.lean','ApiEvolutionChecks.lean'}|{M['fixed_destinations'].get(p,p) for p in M['fixed']}|{n.replace('.','/')+'.lean' for n in modules}|{n.replace('.','/')+'.lean' for n in legacy}|{n.replace('.','/')+'.lean' for n in M['entrypoints']}|{'ModernAllTypes.lean','ModernAllCompat.lean','ModernAllConsumer.lean','ModernOrdinaryAllCompat.lean','ModernStructureCompat.lean','ModernFinalTypes.lean','ModernFinalCompat.lean','ModernNextTypes.lean','ModernNextConsumer.lean','StalkEquationCompat.lean','ModernAttachTypes.lean','ModernAttachConsumer.lean','SafeImportChecks.lean','ModernCoordinateChecks.lean','ModernCoordinateMathlibChecks.lean','ModernRolloutTypes.lean','ImplementationImports.lean','ImplementationPublicTypes.lean','ImplementationSemanticCorpus.lean','LegacyKernelEntryChecks.lean','ModernPublicTypes.lean','ModernCompatChecks.lean','SemanticCorpus.lean','PilotChecks.lean','PilotAudit.lean','StalkCharacterImportChecks.lean','CoreSheafImportChecks.lean','GradedSupportImportChecks.lean','ProjectEntryChecks.lean','WeightedSumImportChecks.lean','ScaledEvaluationImportChecks.lean','ResponsibilityCompatChecks.lean','OAI/Architecture.lean','PublicTypes.lean','ImportChecks.lean','DomainImportChecks.lean','ForMathlibChecks.lean','ForMathlib.lean'}
 actual={str(p.relative_to(HERE)) for p in HERE.rglob('*.lean') if '.lake' not in p.parts}
 if actual-allowed:raise RuntimeError('Unlisted Lean source: '+str(actual-allowed))
 for p in list((HERE/'OAI').rglob('*.lean'))+list((HERE/'ForMathlib').rglob('*.lean')):
  if re.search(r'\b(sorry|admit|unsafe)\b',p.read_text()):raise RuntimeError('Unexpected proof bypass token: '+str(p))


def check_axioms(text):
 records=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",text,re.S)
 expected=re.findall(r'^#print axioms ([A-Za-z0-9_.]+)$',(HERE/'Audit.lean').read_text(),re.M)
 if len(expected)!=16 or len(records)!=16 or len({n for n,_ in records})!=16 or {n for n,_ in records}!=set(expected):
  raise RuntimeError('Expected exactly the sixteen named axiom closures')
 allowed={'propext','Quot.sound','Classical.choice'}
 for name,axioms in records:
  found=set(re.findall(r'[A-Za-z_][A-Za-z_.]*',axioms))
  if not found<=allowed:raise RuntimeError('Disallowed axiom for '+name+': '+str(found-allowed))
  if name=='OAI.KLInvariance.combinatorial_invariance' and found!=allowed:raise RuntimeError('Unexpected main theorem axiom closure')


def main():
 parser=argparse.ArgumentParser();parser.add_argument('--static',action='store_true');parser.add_argument('--verify-baseline',action='store_true',help='Verify immutable source history and retained kernel-export evidence without historical Lean checkouts');parser.add_argument('--checks-only',action='store_true',help='Require all OAI artifacts warm, then verify interfaces without rebuilding them');args=parser.parse_args()
 static_checks()
 if args.static or args.verify_baseline:return
 packages=HERE/'.lake/packages'
 if packages.is_symlink() or not packages.is_dir():raise RuntimeError('Run scripts/setup.sh: dependencies must be owned by the maintained project')
 env=serial_environment()
 run('lean-version',['lake','env','lean','--version'],env=env)
 run('mathlib-ready',['lake','--no-build','build','Mathlib'],env=env)
 if args.checks_only:run('oai-ready',['lake','--no-build','build','ForMathlib','OAI'],env=env)
 else:run('library-build',['lake','build','ForMathlib','OAI'],env=env)
 for file in ('ApiEvolutionChecks','SemanticApiChecks','PilotChecks','PilotAudit','StalkCharacterImportChecks','CoreSheafImportChecks','GradedSupportImportChecks','ProjectEntryChecks','WeightedSumImportChecks','ScaledEvaluationImportChecks','ResponsibilityCompatChecks','ForMathlibChecks','ImportChecks','DomainImportChecks','KernelChecks','CompatChecks','ModernCompatChecks','ModernCoordinateChecks','ModernCoordinateMathlibChecks','SafeImportChecks','ModernAttachConsumer','ModernNextConsumer','ModernFinalCompat','ModernAllCompat','ModernAllConsumer','ModernStructureCompat','LegacyKernelEntryChecks','BoundaryChecks','Audit'):
  run(file,['lake','env','lean',file+'.lean'],env=env)
 from semantic_api import check_axioms as semantic_axioms
 semantic_axioms((OUT/'SemanticApiChecks.log').read_text())
 from api_evolution import check_axioms as evolution_axioms
 evolution_axioms((OUT/'ApiEvolutionChecks.log').read_text())
 run('semantic-api-regressions',[sys.executable,'test_semantic_api.py'])
 run('api-evolution-regressions',[sys.executable,'test_api_evolution.py'])
 check_axioms((OUT/'Audit.log').read_text())
 from proof_evolution import check_pilot_axioms
 check_pilot_axioms((OUT/'PilotAudit.log').read_text())
 run('implementation-imports',['lake','env','lean','-o','.lake/build/lib/lean/ImplementationImports.olean','ImplementationImports.lean'],env=env)
 run('migrated-types',['lake','env','lean','ImplementationPublicTypes.lean'],env=dict(env,LEAN_TYPES_OUT=str(OUT/'migrated-types.tsv')))
 run('api-evolution-full-records',[sys.executable,'api_evolution.py',str(OUT/'migrated-types.tsv')])
 run('semantic-api-main-comparison',[sys.executable,'semantic_api.py',str(OUT/'migrated-types.tsv')])
 run('final105-full-records',[sys.executable,'module_all.py',str(OUT/'migrated-types.tsv')])
 from semantic_api import modern_exporter
 run('final105-modern-types',['lake','env','lean',modern_exporter(OUT/'semantic-api-modern-types.lean')],env=dict(env,LEAN_TYPES_OUT=str(OUT/'all-modern-types.tsv')))
 run('final105-modern-comparison',[sys.executable,'check_all_public.py',str(OUT/'all-modern-types.tsv')])
 run('final105-regressions',[sys.executable,'test_module_all.py'])
 run('type-comparison',[sys.executable,'proof_evolution.py','--compare',str(OUT/'migrated-types.tsv')])
 run('full-record-compatibility',[sys.executable,'attach_module.py','--compare-full',str(OUT/'migrated-types.tsv')])
 run('attach-modern-types',['lake','env','lean','ModernAttachTypes.lean'],env=dict(env,LEAN_TYPES_OUT=str(OUT/'attach-modern-types.tsv')))
 run('attach-modern-comparison',[sys.executable,'attach_checks.py',str(OUT/'attach-modern-types.tsv')])
 run('attach-regressions',[sys.executable,'test_attach_module.py'])
 run('next-full-records',[sys.executable,'module_next.py','--compare-full',str(OUT/'migrated-types.tsv')])
 run('next-modern-types',['lake','env','lean','ModernNextTypes.lean'],env=dict(env,LEAN_TYPES_OUT=str(OUT/'next-modern-types.tsv')))
 run('next-modern-comparison',[sys.executable,'module_next.py','--compare-public',str(OUT/'next-modern-types.tsv')])
 run('next-regressions',[sys.executable,'test_module_next.py'])
 run('final-full-records',[sys.executable,'module_final.py','--compare-full',str(OUT/'migrated-types.tsv')])
 run('final-modern-types',['lake','env','lean','ModernFinalTypes.lean'],env=dict(env,LEAN_TYPES_OUT=str(OUT/'final-modern-types.tsv')))
 run('final-modern-comparison',[sys.executable,'module_final.py','--compare-public',str(OUT/'final-modern-types.tsv')])
 run('final-regressions',[sys.executable,'test_module_final.py'])
 run('modern-public-types',['lake','env','lean','ModernPublicTypes.lean'],env=dict(env,LEAN_TYPES_OUT=str(OUT/'modern-public-types.tsv')))
 run('modern-public-comparison',[sys.executable,'module_integration.py','--compare',str(OUT/'modern-public-types.tsv')])
 run('rollout-public-types',['lake','env','lean','ModernRolloutTypes.lean'],env=dict(env,LEAN_TYPES_OUT=str(OUT/'rollout-public-types.tsv')))
 run('rollout-public-comparison',[sys.executable,'module_rollout.py','--compare',str(OUT/'rollout-public-types.tsv')])
 run('rollout-tests',[sys.executable,'test_module_rollout.py'])
 run('module-integration-tests',[sys.executable,'test_module_integration.py'])
 run('comparator-tests',[sys.executable,'test_compare_types.py'])
 run('source-partition-tests',[sys.executable,'test_source_partitions.py'])
 run('proof-evolution-tests',[sys.executable,'test_proof_evolution.py'])
 run('warm-build',['lake','build','ForMathlib','OAI'],env=env)
 print('ForMathlib staging and project-layout validation passed.',flush=True)
if __name__=='__main__':main()
