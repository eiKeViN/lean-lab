#!/usr/bin/env python3
"""Two isolated representation choices; freeze six whole production clients.
Run without other builds. Sources and formal Lake artifacts restore in finally.
"""
import difflib,json,subprocess,time
from pathlib import Path
import api_families as a
import validate
from semantic_api_split_trial import setup_for
H=a.HERE;OUT=a.ROOT/'results/api-families/trials'
PREFIX='ForMathlib/Combinatorics/MomentGraph/Sheaf/'
PROD=PREFIX+'Iso.lean'
CLIENTS=tuple(PREFIX+n+'.lean' for n in ('Pi','Products','Models','Pullback','Structure','Restriction'))
BACK='''LinearEquiv.ofBijective
     (LinearEquiv.piCongrRight (fun x => (j.vertex x).symm)).toLinearMap
     (LinearEquiv.piCongrRight (fun x => (j.vertex x).symm)).bijective'''
def variant(source,kind,repair):
 if kind=='inverse-bijection':
  old='  LinearEquiv.piCongrRight j.vertex\n'
  assert source.count(old)==1
  source=source.replace(old,'  ('+BACK+').symm\n',1)
  if repair:
   old='j.assignments f x = j.vertex x (f x) := by rfl'
   new='''j.assignments f x = j.vertex x (f x) := by
  let back := '''+BACK+'''
  have h : (j.vertex x).symm (j.assignments f x) = f x :=
    congrFun (back.apply_symm_apply f) x
  exact (j.vertex x).symm_apply_eq.mp h'''
   assert source.count(old)==1;source=source.replace(old,new,1)
 else:
  i=source.index('@[expose] def upwardKernel');j=source.index('/-- Local kernel constraints',i)
  head=source[i:j].split(' where\n')[0]
  source=source[:i]+head+''' :=
  ⨅ e : Outgoing (G := G) x, ⨅ (_ : e ∈ F),
    LinearMap.ker ((LinearMap.proj e).comp (B.stalkMap x))

'''+source[j:]
  if repair:
   old='v ∈ B.upwardKernel x F ↔ ∀ e ∈ F, B.stalkMap x v e = 0 := by rfl'
   new='''v ∈ B.upwardKernel x F ↔ ∀ e ∈ F, B.stalkMap x v e = 0 := by
  simp only [upwardKernel, Submodule.mem_iInf, LinearMap.mem_ker,
    LinearMap.comp_apply, LinearMap.proj_apply]'''
   assert source.count(old)==1;source=source.replace(old,new,1)
 return source

def main():
 env=validate.serial_environment();env['LEAN_PATH']=subprocess.check_output(['lake','env','printenv','LEAN_PATH'],cwd=H,env=env,text=True).strip()
 lean=str(Path(env['LEAN_SYSROOT'])/'bin/lean')
 snapshots={p:(H/p).read_bytes() for p in (PROD,*CLIENTS)}
 frozen={p:a.sha(snapshots[p]) for p in CLIENTS}
 artifacts={str(p):a.sha(p.read_bytes()) for source in snapshots
   for p in (H/'.lake/build/lib/lean'/source).with_suffix('.olean').parent.glob(Path(source).stem+'.olean*') if p.is_file()}
 for kind in ('inverse-bijection','kernel-intersection'):
  out=OUT/kind;out.mkdir(parents=True,exist_ok=True);shadows={};rows=[]
  (out/'frozen-downstream.json').write_text(json.dumps(frozen,indent=2)+'\n')
  def run(label,path,expected=None,output=None):
   args=[lean,path,'--setup',setup_for(path,out,label,shadows)]
   if output is not None:args+=['-o',str(output)]
   start=time.monotonic()
   with (out/(label+'.log')).open('w') as log:r=subprocess.run(args,cwd=H,env=env,stdout=log,stderr=subprocess.STDOUT)
   rows.append(dict(label=label,command=args,exit_code=r.returncode,wall_seconds=time.monotonic()-start,source_sha256=a.sha((H/path).read_bytes())))
   (out/'metrics.json').write_text(json.dumps(rows,indent=2)+'\n')
   if expected is not None and (r.returncode==0)!=expected:raise RuntimeError('Unexpected result: '+kind+'/'+label)
   if r.returncode and any(t in (out/(label+'.log')).read_text() for t in ('object file','unknown module prefix')):raise RuntimeError('Missing artifact: '+label)
   return r.returncode
  try:
   source=snapshots[PROD].decode();unrepaired=variant(source,kind,False);repaired=variant(source,kind,True)
   for label,old,new in [('definition-only',source,unrepaired),('api-proof',unrepaired,repaired)]:
    (out/(label+'.patch')).write_text(''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='before/'+PROD,tofile='after/'+PROD)))
   (H/PROD).write_text(unrepaired);run('changed-implementation-old-api',PROD,False)
   (H/PROD).write_text(repaired);(out/'modified-producer.lean').write_text(repaired)
   dest=(out/'artifacts'/PROD).with_suffix('.olean');dest.parent.mkdir(parents=True,exist_ok=True)
   run('changed-implementation-repaired-api',PROD,True,dest);shadows[PROD]=dest
   (H/PROD).write_bytes(snapshots[PROD])
   for i,path in enumerate(CLIENTS):
    assert a.sha((H/path).read_bytes())==frozen[path]
    dest=(out/'artifacts'/path).with_suffix('.olean');dest.parent.mkdir(parents=True,exist_ok=True)
    run('frozen-new-'+str(i),path,True,dest);shadows[path]=dest
   run('ordinary-api-client','ApiFamiliesChecks.lean',True)
   a.check_axioms((out/'ordinary-api-client.log').read_text())
   old_results={}
   for i,path in enumerate(CLIENTS):
    (H/path).write_bytes(a.before(path));old_results[path]=run('old-client-'+str(i),path)
    (H/path).write_bytes(snapshots[path])
   required=(PREFIX+'Structure.lean',) if kind=='inverse-bijection' else (PREFIX+'Models.lean',PREFIX+'Pullback.lean')
   assert all(old_results[p]!=0 for p in required),old_results
   (out/'comparison.json').write_text(json.dumps(dict(old_exit_codes=old_results,required_discriminating_clients=required,all_six_frozen_new_clients_passed=True,axiom_closures_checked=25),indent=2)+'\n')
  finally:
   for p,b in snapshots.items():(H/p).write_bytes(b)
   state=dict(source_restored=all((H/p).read_bytes()==b for p,b in snapshots.items()),frozen_downstream_unchanged=all(a.sha((H/p).read_bytes())==h for p,h in frozen.items()),lake_artifacts_unchanged=all(a.sha(Path(p).read_bytes())==h for p,h in artifacts.items()),artifacts=artifacts)
   (out/'restoration.json').write_text(json.dumps(state,indent=2)+'\n')
   assert all(state[k] for k in ('source_restored','frozen_downstream_unchanged','lake_artifacts_unchanged'))
if __name__=='__main__':main()
