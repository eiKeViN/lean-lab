#!/usr/bin/env python3
"""Serial controlled olean builds. Never deletes or writes shared build artifacts."""
from pathlib import Path
import datetime,hashlib,json,os,platform,resource,shutil,statistics,subprocess,time
HERE=Path(__file__).resolve().parent;ROOT=HERE.parent
os.chdir(ROOT)
meta=json.loads((HERE/'accounting.json').read_text())
run=ROOT/'logs/cost-20261102'/datetime.datetime.now(datetime.timezone.utc).strftime('run-%Y%m%dT%H%M%S%fZ')
run.mkdir(parents=True)
baseenv=dict(os.environ);baseenv.pop('LEAN_PATH',None)
lean=shutil.which('lean');assert lean and 'lean-4.35.0-linux' in lean
version=subprocess.check_output([lean,'--version'],text=True);assert 'version 4.35.0,' in version
allpaths=subprocess.check_output(['lake','env','printenv','LEAN_PATH'],text=True,env=baseenv).strip().split(os.pathsep)
upstream=[p for p in allpaths if Path(p).resolve()!=(ROOT/'.lake/build/lib/lean').resolve()]
for p,sha in meta['source_files'].items():assert hashlib.sha256((ROOT/p).read_bytes()).hexdigest()==sha,p
for name,sha in {'mathlib':'56a005855ea17e0b0958f73ec801ae140b0a1679','Physlib':'c5a908ba7a1ee474063626bdf0470af006f9812e'}.items():
 assert subprocess.check_output(['git','-C',str(ROOT/'.lake/packages'/name),'rev-parse','HEAD'],text=True).strip()==sha
records=[]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def execute(label,args,cwd,paths):
 env=dict(baseenv);env['LEAN_PATH']=os.pathsep.join([str(p) for p in paths]+upstream)
 start=time.perf_counter();cpu=resource.getrusage(resource.RUSAGE_CHILDREN)
 p=subprocess.run(args,cwd=cwd,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
 elapsed=time.perf_counter()-start;after=resource.getrusage(resource.RUSAGE_CHILDREN)
 rec={'label':label,'command':list(map(str,args)),'cwd':str(cwd),'LEAN_PATH':env['LEAN_PATH'],'exit_code':p.returncode,'wall_seconds':elapsed,'child_cpu_seconds':after.ru_utime+after.ru_stime-cpu.ru_utime-cpu.ru_stime}
 records.append(rec);(run/(label+'.log')).write_text(p.stdout);(run/(label+'.exit')).write_text(str(p.returncode)+'\n')
 (run/'commands.json').write_text(json.dumps(records,indent=2)+'\n')
 if p.returncode:print(p.stdout,flush=True);raise RuntimeError(label+' failed; see '+str(run))
 return rec,p.stdout
common=run/'baseline';(common/'CostStudy').mkdir(parents=True)
def compile_module(label,module,out,paths,variant=False):
 srcroot=HERE/('variants' if variant else 'sources');src=srcroot/'CostStudy'/(module+'.lean')
 target=out/'CostStudy'/(module+'.olean');target.parent.mkdir(parents=True,exist_ok=True)
 rec,_=execute(label,[lean,'CostStudy/'+module+'.lean','-o',str(target)],srcroot,[out]+list(paths))
 rec.update({'module':module,'source_sha256':sha(src),'artifact_sha256':sha(target),'artifact':str(target),'artifact_mtime_ns':target.stat().st_mtime_ns})
 return rec
compile_module('prepare-common','Common',common,[])
# Both basis modules and baseline consumers are prepared for audit and hot/edit scenarios.
bases={};seeds={}
for route in ['Native','Bridge']:
 bases[route]=common
 compile_module('prepare-'+route+'Base',route+'Base',bases[route],[common])
 seeds[route]=common
 compile_module('prepare-'+route+'Consumer',route+'Consumer',seeds[route],[bases[route],common])
# Build the common contract in measurement-only roots: both route results must have identical types.
contract='''import CostStudy.NativeConsumer
import CostStudy.BridgeConsumer
noncomputable section
open scoped BigOperators
open QuantumExperiments.PMFComparison
variable {I O : Type*} [Fintype O] {n : ℕ}
example (C : DMChannel I O) (is : Fin n → I) (g : Fin n → O → ℝ) :
    Finite.variance (C.on_fin I O is) (fun os => ∑ k, g k (os k)) =
      ∑ k, Finite.variance (C.symb_dist (is k)) (g k) := Finite.variance_on_fin C is g
example (C : DMChannel I O) (is : Fin n → I) (g : Fin n → O → ℝ) :
    Finite.variance (C.on_fin I O is) (fun os => ∑ k, g k (os k)) =
      ∑ k, Finite.variance (C.symb_dist (is k)) (g k) := Transport.variance_on_fin C is g
'''
(run/'Contract.lean').write_text(contract)
copy_paths=[common]
execute('contract-baseline',[lean,str(run/'Contract.lean')],run,copy_paths)
# Type comparison normalizes universe parameter spelling, binder names, and metadata only.
names=[r['name'] for r in meta['declarations']]
export=(HERE/'type_export.lean.inc').read_text().replace('STUDY_NAMES','['+', '.join('`'+n for n in names)+']')
axioms='\n'.join('#print axioms '+n for n in names)
for tag,imports in [('original','import PMFComparison.Finite\nimport PMFComparison.Transport\n'),('copies','import CostStudy.NativeConsumer\nimport CostStudy.BridgeConsumer\n')]:
 (run/(tag+'Audit.lean')).write_text(imports+export+'\n'+axioms+'\n')
outputs={}
_,outputs['original']=execute('audit-original',[lean,str(run/'originalAudit.lean')],run,[ROOT/'.lake/build/lib/lean'])
_,outputs['copies']=execute('audit-copies',[lean,str(run/'copiesAudit.lean')],run,copy_paths)
def types(output):return {x['name']:x['type'] for l in output.splitlines() if l.startswith('TYPEJSON ') for x in [json.loads(l[9:])]}
assert types(outputs['original'])==types(outputs['copies']), 'public type mismatch'
import re
def ax(output):return {n:[a.strip() for a in vals.split(',') if a.strip()] for n,vals in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",output,re.S)}
for output in outputs.values():
 assert set(ax(output))==set(names)
 assert all(set(v)<={'propext','Classical.choice','Quot.sound'} for v in ax(output).values())
print('PRECHECK PASS: copied bodies, 27 public types, contracts and axiom closures',flush=True)
cases=[]
# Three repeats, balanced across alternating route/scenario ordering; no concurrent compilers.
for repeat in range(3):
 scenarios=['route-cold','basis-hot','consumer-edit'] if repeat%2==0 else ['consumer-edit','basis-hot','route-cold']
 routes=['Native','Bridge'] if repeat%2==0 else ['Bridge','Native']
 for scenario in scenarios:
  for route in routes:
   label=f'r{repeat+1}-{scenario}-{route}';out=run/'outputs'/label
   out.mkdir(parents=True);steps=[];old={}
   def copy_module(module, src=common):
    (out/'CostStudy').mkdir(exist_ok=True)
    for f in (src/'CostStudy').glob(module+'.*'):
     if f.is_file():shutil.copy2(f,out/'CostStudy'/f.name)
   copy_module('Common')
   if scenario=='route-cold':
    assert not (out/'CostStudy'/(route+'Base.olean')).exists()
    steps.append(compile_module(label+'-base',route+'Base',out,[]))
    steps.append(compile_module(label+'-consumer',route+'Consumer',out,[]))
   elif scenario=='basis-hot':
    copy_module(route+'Base')
    steps.append(compile_module(label+'-consumer',route+'Consumer',out,[]))
   else:
    # Copy only this run's seed artifacts; shared/cache directories are never cleared.
    copy_module(route+'Base')
    copy_module(route+'Consumer')
    target=out/'CostStudy'/(route+'Consumer.olean')
    old={'consumer_source_sha256':sha(HERE/'sources/CostStudy'/(route+'Consumer.lean')),'consumer_artifact_sha256':sha(target),'consumer_artifact_mtime_ns':target.stat().st_mtime_ns,'basis_artifact_sha256':sha(bases[route]/'CostStudy'/(route+'Base.olean'))}
    steps.append(compile_module(label+'-consumer',route+'Consumer',out,[],variant=True))
    assert steps[0]['source_sha256']!=old['consumer_source_sha256']
    assert steps[0]['artifact_mtime_ns']!=old['consumer_artifact_mtime_ns']
    assert sha(bases[route]/'CostStudy'/(route+'Base.olean'))==old['basis_artifact_sha256']
   row={'repeat':repeat+1,'scenario':scenario,'route':route,'wall_seconds':sum(x['wall_seconds'] for x in steps),'cpu_seconds':sum(x['child_cpu_seconds'] for x in steps),'compiled_modules':[x['module'] for x in steps],'steps':steps,'before_edit':old}
   cases.append(row);(run/'cases.json').write_text(json.dumps(cases,indent=2)+'\n')
   print(label,round(row['wall_seconds'],3),flush=True)
# Audit actual edited products after timing: same contract and same public types/axioms.
auditroot=run/'edited-audit';shutil.copytree(common,auditroot)
for route in ['Native','Bridge']:
 for f in (run/'outputs'/f'r3-consumer-edit-{route}'/'CostStudy').glob(route+'Consumer.*'):
  shutil.copy2(f,auditroot/'CostStudy'/f.name)
edited=[auditroot]
execute('contract-edited',[lean,str(run/'Contract.lean')],run,edited)
_,editedout=execute('audit-edited',[lean,str(run/'copiesAudit.lean')],run,edited)
assert types(editedout)==types(outputs['original'])
assert set(ax(editedout))==set(names)
assert all(set(v)<={'propext','Classical.choice','Quot.sound'} for v in ax(editedout).values())
summary={}
for scenario in ['route-cold','basis-hot','consumer-edit']:
 summary[scenario]={}
 for route in ['Native','Bridge']:
  vals=[x['wall_seconds'] for x in cases if x['scenario']==scenario and x['route']==route]
  summary[scenario][route]={'raw_seconds':vals,'median':statistics.median(vals),'min':min(vals),'max':max(vals)}
report={'pass':True,'base_commit':meta['base_commit'],'lean':version.strip(),'platform':platform.platform(),'cpu_count':os.cpu_count(),'scenarios':summary,'cases':cases,'commands':records,'declaration_count':len(names),'original_copy_and_edited_types_identical':True,'axioms':ax(editedout),'total_process_wall_seconds':sum(r['wall_seconds'] for r in records),'method':'Serial direct Lean -o builds; common upstream union and Common cached, route-owned artifacts isolated. Not Lake scheduler or C compilation; no downloads, no cold OS caches, no whole-mathlib rebuild. Explicit controlled dependency invalidation for a same-type proof-body refactor.'}
(run/'report.json').write_text(json.dumps(report,indent=2)+'\n')
(HERE/'latest-run.txt').write_text(str(run)+'\n')
print('PASS',run,flush=True);print(json.dumps(summary,indent=2),flush=True)
