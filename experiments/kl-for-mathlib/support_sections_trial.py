#!/usr/bin/env python3
"""Inverse-first support equivalence and associated corner control, on frozen clients.
Run only with no concurrent build. Formal sources/artifacts restore in finally.
"""
import difflib,json,subprocess,time,textwrap
from pathlib import Path
import api_support as a
import validate
from semantic_api_split_trial import setup_for
H=a.HERE;OUT=a.ROOT/'results/support-sections/trials'
SUPPORT='ForMathlib/Combinatorics/MomentGraph/Sheaf/Duality.lean'
SUMMAND='ForMathlib/Combinatorics/MomentGraph/GradedSheaf/Summand.lean'
SCENARIOS={
 'inverse-support':(SUPPORT,('ForMathlib/Combinatorics/MomentGraph/GradedSheaf/Duality.lean','OAI/KL/Sheaves/Support.lean','OAI/KL/Sheaves/FreeModel.lean','OAI/KL/Comparison/Propagation.lean')),
 'associated-corner':(SUMMAND,('ForMathlib/Combinatorics/MomentGraph/GradedSheaf/Models.lean','OAI/KL/BottSamelson/AdjointSheaf.lean'))}
def variant(source,kind,repair):
 if kind=='inverse-support':
  i=source.index('@[expose] noncomputable def singleStalkEquivSupport');j=source.index('omit [Fintype E] [IsDomain R] in',i)
  source=source[:i]+'''@[expose] noncomputable def singleStalkEquivSupport (x : V) :
    B.singleStalk x ≃ₗ[R] IntegralSupport.supported (B.sections Set.univ) x := by
  let f : IntegralSupport.supported (B.sections Set.univ) x →ₗ[R] B.singleStalk x := {
    toFun := fun m => ⟨m.val.val x, by
      change Pi.single x (m.val.val x) ∈ B.sections Set.univ
      have he : Pi.single x (m.val.val x) = m.val.val := by
        funext y
        by_cases hy : y=x
        · subst y; exact Pi.single_eq_same _ _
        · rw [Pi.single_eq_of_ne hy,m.property y hy]
      rw [he]
      exact m.val.property⟩
    map_add' := by intro m n; rfl
    map_smul' := by intro r m; rfl }
  exact (LinearEquiv.ofBijective f (by
    constructor
    · intro m n h
      apply Subtype.ext; apply Subtype.ext; funext y
      by_cases hy : y=x
      · subst y; exact congrArg Subtype.val h
      · rw [m.property y hy,n.property y hy]
    · intro v
      refine ⟨⟨⟨Pi.single x v.val,v.property⟩,?_⟩,?_⟩
      · intro y hy; exact Pi.single_eq_of_ne hy _
      · apply Subtype.ext; exact Pi.single_eq_same _ _)).symm

'''+source[j:]
  if repair:
   old='''(B.singleStalkEquivSupport x v).val.val = Pi.single x v.val := by rfl'''
   new='''(B.singleStalkEquivSupport x v).val.val = Pi.single x v.val := by
  have hx : (B.singleStalkEquivSupport x v).val.val x = v.val :=
    congrArg Subtype.val ((B.singleStalkEquivSupport x).symm_apply_apply v)
  funext y
  by_cases hy : y=x
  · subst y; simpa only [Pi.single_eq_same] using hx
  · rw [(B.singleStalkEquivSupport x v).property y hy, Pi.single_eq_of_ne hy]
'''
   assert source.count(old)==1;source=source.replace(old,new,1)
 else:
  # The same corner extension via the other associativity convention.
  # This is an intentionally honest non-discriminating control.
  old='s.inclusion.comp (f.comp s.projection)'
  assert source.count(old)==1
  source=source.replace(old,'(s.inclusion.comp f).comp s.projection',1)
 return source

def main():
 env=validate.serial_environment();env['LEAN_PATH']=subprocess.check_output(['lake','env','printenv','LEAN_PATH'],cwd=H,env=env,text=True).strip();lean=str(Path(env['LEAN_SYSROOT'])/'bin/lean')
 for kind,(producer,clients) in SCENARIOS.items():
  out=OUT/kind;out.mkdir(parents=True,exist_ok=True);shadows={};rows=[]
  snapshots={p:(H/p).read_bytes() for p in (producer,*clients)};frozen={p:a.sha(snapshots[p]) for p in clients}
  artifacts={str(p):a.sha(p.read_bytes()) for source in snapshots for p in (H/'.lake/build/lib/lean'/source).with_suffix('.olean').parent.glob(Path(source).stem+'.olean*') if p.is_file()}
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
   source=snapshots[producer].decode();unrepaired=variant(source,kind,False);repaired=variant(source,kind,True)
   for label,old,new in [('definition-only',source,unrepaired),('api-proof',unrepaired,repaired)]:
    (out/(label+'.patch')).write_text(''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='before/'+producer,tofile='after/'+producer)))
   (H/producer).write_text(unrepaired);run('changed-implementation-old-api',producer,kind!='inverse-support')
   (H/producer).write_text(repaired);(out/'modified-producer.lean').write_text(repaired)
   dest=(out/'artifacts'/producer).with_suffix('.olean');dest.parent.mkdir(parents=True,exist_ok=True)
   run('changed-implementation-repaired-api',producer,True,dest);shadows[producer]=dest
   (H/producer).write_bytes(snapshots[producer])
   for i,path in enumerate(clients):
    assert a.sha((H/path).read_bytes())==frozen[path]
    dest=(out/'artifacts'/path).with_suffix('.olean');dest.parent.mkdir(parents=True,exist_ok=True)
    run('frozen-new-'+str(i),path,True,dest);shadows[path]=dest
   run('ordinary-api-client','SupportSectionsChecks.lean',True);a.check_axioms((out/'ordinary-api-client.log').read_text())
   old_results={}
   for i,path in enumerate(clients):
    (H/path).write_bytes(a.before(path));old_results[path]=run('old-client-'+str(i),path)
    (H/path).write_bytes(snapshots[path])
   if kind=='inverse-support':assert old_results[clients[1]]!=0 and old_results[clients[2]]!=0,old_results
   (out/'comparison.json').write_text(json.dumps(dict(old_exit_codes=old_results,all_frozen_new_clients_passed=True,axiom_closures_checked=18),indent=2)+'\n')
  finally:
   for p,b in snapshots.items():(H/p).write_bytes(b)
   state=dict(source_restored=all((H/p).read_bytes()==b for p,b in snapshots.items()),frozen_downstream_unchanged=all(a.sha((H/p).read_bytes())==h for p,h in frozen.items()),lake_artifacts_unchanged=all(a.sha(Path(p).read_bytes())==h for p,h in artifacts.items()),artifacts=artifacts)
   (out/'restoration.json').write_text(json.dumps(state,indent=2)+'\n');assert all(state[k] for k in ('source_restored','frozen_downstream_unchanged','lake_artifacts_unchanged'))
if __name__=='__main__':main()
