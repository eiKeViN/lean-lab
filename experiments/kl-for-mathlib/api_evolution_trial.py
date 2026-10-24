#!/usr/bin/env python3
"""Transport an equivalence by its inverse; freeze whole real downstream files.
Run with no other build. Only scratch artifacts are written; sources restore.
"""
import json,subprocess,time,os
from pathlib import Path
import api_evolution as a
from semantic_api_split_trial import setup_for
import validate
H=a.HERE;OUT=a.ROOT/'results/api-evolution/implementation-trial'
PROD='ForMathlib/Algebra/Module/CoefficientChange/Dual.lean'
CLIENTS=('ForMathlib/Algebra/Module/Graded/ModuleData/CoefficientChange/Basic.lean',
 'ForMathlib/Combinatorics/MomentGraph/GradedSheaf/Duality.lean',
 'ForMathlib/Combinatorics/MomentGraph/GradedSheaf/Uniqueness.lean')
def variant(source,repair):
 start=source.index(' @[expose] def mapEquiv ');end=source.index(' omit [Module k M]',start)
 head=source[start:end].split(' where\n',1)[0]
 inv='''LinearEquiv.ofBijective (map e f.symm.toLinearMap)
     ⟨map_injective e _ f.symm.injective, map_surjective e _ f.symm.surjective⟩'''
 source=source[:start]+head+' :=\n   ('+inv+').symm\n\n'+source[end:]
 if repair:
  start=source.index(' @[simp] theorem val_mapEquiv');end=source.index(' @[expose] def dualTo',start)
  block=source[start:end];assert block.count(':= by rfl')==1
  proof=''' := by
   let inv := '''+inv+'''
   have hi : map e f.symm.toLinearMap (mapEquiv e f m) = m := inv.apply_symm_apply m
   have hv := (val_map e f.symm.toLinearMap (mapEquiv e f m)).symm.trans
     (congrArg CoefficientChange.val hi)
   exact f.symm_apply_eq.mp hv

'''
  block=block[:block.index(' := by rfl')]+proof
  source=source[:start]+block+source[end:]
 return source

def main():
 OUT.mkdir(parents=True,exist_ok=True);overlay=OUT/'artifacts';env=validate.serial_environment()
 env['LEAN_PATH']=subprocess.check_output(['lake','env','printenv','LEAN_PATH'],cwd=H,env=env,text=True).strip()
 lean=str(Path(env['LEAN_SYSROOT'])/'bin/lean');shadows={};rows=[]
 snapshots={p:(H/p).read_bytes() for p in (PROD,*CLIENTS)}
 frozen={p:a.sha(snapshots[p]) for p in CLIENTS}
 artifacts={str(p):a.sha(p.read_bytes()) for source in (PROD,*CLIENTS)
  for p in (H/'.lake/build/lib/lean'/source).with_suffix('.olean').parent.glob(Path(source).stem+'.olean*') if p.is_file()}
 (OUT/'frozen-downstream.json').write_text(json.dumps(frozen,indent=2)+'\n')
 def run(label,source,expected,output=None):
  args=[source,'--setup',setup_for(source,OUT,label,shadows)]
  if output is not None:args+=['-o',str(output)]
  start=time.monotonic()
  with (OUT/(label+'.log')).open('w') as log:
   p=subprocess.run([lean]+args,cwd=H,env=env,stdout=log,stderr=subprocess.STDOUT)
  rows.append(dict(label=label,command=[lean]+args,exit_code=p.returncode,wall_seconds=time.monotonic()-start,
   source_sha256=a.sha((H/source).read_bytes()) if not Path(source).is_absolute() else a.sha(Path(source).read_bytes())))
  (OUT/'metrics.json').write_text(json.dumps(rows,indent=2)+'\n')
  if (p.returncode==0)!=expected:raise RuntimeError('Unexpected implementation trial outcome: '+label)
 try:
  source=snapshots[PROD].decode()
  (H/PROD).write_text(variant(source,False))
  (OUT/'definition-only.patch').write_text(''.join(__import__('difflib').unified_diff(source.splitlines(True),variant(source,False).splitlines(True),fromfile='production/'+PROD,tofile='variant/'+PROD)))
  run('changed-implementation-old-api-proof',PROD,False)
  modified=variant(source,True);(H/PROD).write_text(modified)
  (OUT/'modified-producer.lean').write_text(modified)
  (OUT/'api-proof.patch').write_text(''.join(__import__('difflib').unified_diff(variant(source,False).splitlines(True),modified.splitlines(True),fromfile='unrepaired-api/'+PROD,tofile='repaired-api/'+PROD)))
  dest=(overlay/PROD).with_suffix('.olean');dest.parent.mkdir(parents=True,exist_ok=True)
  run('changed-implementation-repaired-api',PROD,True,dest);shadows[PROD]=dest
  (H/PROD).write_bytes(snapshots[PROD])
  for i,path in enumerate(CLIENTS):
   assert a.sha((H/path).read_bytes())==frozen[path]
   dest=(overlay/path).with_suffix('.olean');dest.parent.mkdir(parents=True,exist_ok=True)
   run('frozen-new-client-'+str(i),path,True,dest);shadows[path]=dest
  run('ordinary-api-consumer','ApiEvolutionChecks.lean',True)
  a.check_axioms((OUT/'ordinary-api-consumer.log').read_text())
  (OUT/'axiom-closure-check.json').write_text(json.dumps(dict(passed=True,closures=17,allowed=['propext','Classical.choice','Quot.sound']),indent=2)+'\n')
  for i,path in enumerate(CLIENTS[1:]):
   (H/path).write_bytes(a.before(path));run('old-client-'+str(i),path,False)
   text=(OUT/('old-client-'+str(i)+'.log')).read_text()
   if 'object file' in text:raise RuntimeError('Old client failed from missing artifacts')
   (H/path).write_bytes(snapshots[path])
 finally:
  for p,b in snapshots.items():(H/p).write_bytes(b)
  state=dict(source_restored=all((H/p).read_bytes()==b for p,b in snapshots.items()),
   frozen_downstream_unchanged=all(a.sha((H/p).read_bytes())==h for p,h in frozen.items()),
   lake_artifacts_unchanged=all(a.sha(Path(p).read_bytes())==h for p,h in artifacts.items()),artifacts=artifacts)
  (OUT/'restoration.json').write_text(json.dumps(state,indent=2)+'\n')
  if not all(state[k] for k in ('source_restored','frozen_downstream_unchanged','lake_artifacts_unchanged')):raise RuntimeError('Restoration failed')
if __name__=='__main__':main()
