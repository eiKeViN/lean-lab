#!/usr/bin/env python3
"""Inverse-first image-section range map. Run without a concurrent build.
Freeze the unchanged producer tail and whole external clients, restore all bytes
and normal artifacts in finally. The old-module comparison receives exactly the
same implementation and two new API boundaries, retaining its old client bodies.
"""
from pathlib import Path
import difflib,json,subprocess,time,resource
import api_saturation as a
import validate
from semantic_api_split_trial import setup_for
H=a.HERE;OUT=a.ROOT/'results/api-saturation/trial'
PRODUCER='ForMathlib/Combinatorics/MomentGraph/GradedSheaf/Summand.lean'
CLIENTS=('ForMathlib/Combinatorics/MomentGraph/GradedSheaf/Models.lean','OAI/KL/BottSamelson/AdjointSheaf.lean')
IMPLEMENTATION=''' := by
  let F : h.image.forget.sections Ω →ₗ[A] LinearMap.range (h.sectionMap Ω) :=
    (h.imageInclusion.sectionMap Ω).codRestrict _ (fun f =>
      ⟨h.imageInclusion.sectionMap Ω f,h.imageSection_fixed hv Ω f⟩)
  let P : LinearMap.range (h.sectionMap Ω) →ₗ[A] h.image.forget.sections Ω :=
    (h.imageProjection.sectionMap Ω).domRestrict _
  have hPF (f : h.image.forget.sections Ω) : P (F f) = f := by
    apply Subtype.ext
    funext x
    apply Subtype.ext
    change ((h.imageProjection.sectionMap Ω (h.imageInclusion.sectionMap Ω f)).val x).val = _
    rw [Hom.sectionMap_apply, Hom.sectionMap_apply]
    exact (ModuleData.rangeProjection_val _ _).trans
      ((congrArg (h.vertex x).map (ModuleData.rangeInclusion_apply _ _)).trans
        (ModuleData.range_fixed (h.vertex x) (hv x) (f.val x)))
  have hFP (m : LinearMap.range (h.sectionMap Ω)) : F (P m) = m := by
    obtain ⟨_,s,rfl⟩ := m
    apply Subtype.ext
    change ((h.imageInclusion.sectionMap Ω).comp (h.imageProjection.sectionMap Ω))
      (h.sectionMap Ω s) = h.sectionMap Ω s
    rw [← Hom.sectionMap_comp, h.imageInclusion_comp_imageProjection]
    apply Subtype.ext
    funext x
    simp only [Hom.sectionMap_apply]
    exact hv x (s.val x)
  exact (LinearEquiv.ofBijective P ⟨fun m n he =>
    (hFP m).symm.trans ((congrArg F he).trans (hFP n)),
    fun f => ⟨F f,hPF f⟩⟩).symm.toLinearMap

'''
REPAIR=''' := by
  have he : h.imageProjection.sectionMap Ω (h.imageSectionMap hv Ω m).val = m := by
    change e (e.symm m) = m
    exact e.apply_symm_apply m
  have hf : h.sectionMap Ω (h.imageSectionMap hv Ω m).val =
      (h.imageSectionMap hv Ω m).val := by
    obtain ⟨s,hs⟩ := (h.imageSectionMap hv Ω m).property
    rw [← hs]
    apply Subtype.ext
    funext x
    simp only [Hom.sectionMap_apply]
    exact hv x (s.val x)
  have hi := congrArg (h.imageInclusion.sectionMap Ω) he
  change ((h.imageInclusion.sectionMap Ω).comp (h.imageProjection.sectionMap Ω))
    (h.imageSectionMap hv Ω m).val = h.imageInclusion.sectionMap Ω m at hi
  rw [← Hom.sectionMap_comp, h.imageInclusion_comp_imageProjection, hf] at hi
  exact hi

'''
# Repeat the local inverse construction inside this one API proof, with an
# explicitly typed equivalence. No unresolved ring/map/bijectivity placeholders.
INVERSE_SETUP = IMPLEMENTATION.split('  exact (LinearEquiv.ofBijective P',1)[0].removeprefix(' := by\n')
REPAIR = REPAIR.replace(' := by\n', ' := by\n'+INVERSE_SETUP+"  let e := LinearEquiv.ofBijective P ⟨fun u v he =>\n    (hFP u).symm.trans ((congrArg F he).trans (hFP v)),\n    fun f => ⟨F f,hPF f⟩⟩\n",1)
def block(s,start,end):return s[s.index(start):s.index(end,s.index(start))]
def variant(s,repair):
 i=s.index(' @[expose] def Hom.imageSectionMap');j=s.index('/-- The canonical map from image sections',i)
 head=s[i:j].split(' :=\n',1)[0]
 s=s[:i]+head+IMPLEMENTATION+s[j:]
 if repair:
  i=s.index('@[simp] theorem Hom.imageSectionMap_val');j=s.index(' theorem Hom.imageSectionMap_bijective',i)
  head=s[i:j].split(' := by',1)[0]
  s=s[:i]+head+REPAIR+s[j:]
 return s

def main():
 OUT.mkdir(parents=True,exist_ok=True);shadows={};rows=[]
 env=validate.serial_environment();env['LEAN_PATH']=subprocess.check_output(['lake','env','printenv','LEAN_PATH'],cwd=H,env=env,text=True).strip();lean=str(Path(env['LEAN_SYSROOT'])/'bin/lean')
 snapshots={p:(H/p).read_bytes() for p in (PRODUCER,*CLIENTS)}
 artifacts={str(p):a.sha(p.read_bytes()) for source in snapshots for p in (H/'.lake/build/lib/lean'/source).with_suffix('.olean').parent.glob(Path(source).stem+'.olean*') if p.is_file()}
 frozen={p:a.sha(snapshots[p]) for p in CLIENTS}
 (OUT/'frozen-downstream.json').write_text(json.dumps(frozen,indent=2)+'\n')
 def run(label,path,expected=None,output=None):
  args=[lean,path,'--setup',setup_for(path,OUT,label,shadows)]
  if output is not None:args+=['-o',str(output)]
  start=time.monotonic()
  with (OUT/(label+'.log')).open('w') as log:r=subprocess.run(args,cwd=H,env=env,stdout=log,stderr=subprocess.STDOUT)
  rows.append(dict(label=label,command=args,exit_code=r.returncode,wall_seconds=time.monotonic()-start,max_rss_kib_so_far=resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss,source_sha256=a.sha((H/path).read_bytes())))
  (OUT/'metrics.json').write_text(json.dumps(rows,indent=2)+'\n')
  log=(OUT/(label+'.log')).read_text()
  if r.returncode and any(t in log for t in ('object file','unknown module prefix','Unknown constant','Unknown identifier','private declaration')):raise RuntimeError('Artifact/name/visibility failure: '+label)
  if expected is not None and (r.returncode==0)!=expected:raise RuntimeError('Unexpected result: '+label+'\n'+log[-4000:])
  return r.returncode
 try:
  source=snapshots[PRODUCER].decode();unrepaired=variant(source,False);repaired=variant(source,True)
  for label,old,new in [('definition-only',source,unrepaired),('api-proof',unrepaired,repaired)]:
   (OUT/(label+'.patch')).write_text(''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='before/'+PRODUCER,tofile='after/'+PRODUCER)))
  tail=' theorem Hom.imageSectionMap_bijective'
  assert source[source.index(tail):]==repaired[repaired.index(tail):]
  (OUT/'frozen-producer-client-tail.json').write_text(json.dumps(dict(start=tail,sha256=a.sha(source[source.index(tail):].encode())),indent=2)+'\n')
  (H/PRODUCER).write_text(unrepaired);run('changed-implementation-old-api',PRODUCER,False)
  (H/PRODUCER).write_text(repaired);(OUT/'modified-producer.lean').write_text(repaired)
  dest=(OUT/'artifacts'/PRODUCER).with_suffix('.olean');dest.parent.mkdir(parents=True,exist_ok=True)
  run('changed-implementation-repaired-api',PRODUCER,True,dest);shadows[PRODUCER]=dest
  (H/PRODUCER).write_bytes(snapshots[PRODUCER])
  for i,p in enumerate(CLIENTS):
   dest=(OUT/'artifacts'/p).with_suffix('.olean');dest.parent.mkdir(parents=True,exist_ok=True)
   run('frozen-new-'+str(i),p,True,dest);shadows[p]=dest
  run('ordinary-api-client','ApiSaturationChecks.lean',True);a.check_axioms((OUT/'ordinary-api-client.log').read_text())
  # Identical producer variant/API available to old whole-module clients.
  old=a.before(PRODUCER).decode()
  fac=block(source,'/-- Inclusion after projection is the canonical',' @[expose] def Hom.imageSplit')
  coord=block(source,'/-- The canonical map from image sections',' theorem Hom.imageSectionMap_bijective')
  old=old.replace(' @[expose] def Hom.imageSplit',fac+' @[expose] def Hom.imageSplit',1)
  old=old.replace(' theorem Hom.imageSectionMap_bijective',coord+' theorem Hom.imageSectionMap_bijective',1)
  old=variant(old,True);(OUT/'old-module-with-same-boundary.lean').write_text(old)
  (OUT/'old-module-binding.json').write_text(json.dumps(dict(base_commit=a.BASE,
    original_source_sha256=a.sha(a.before(PRODUCER)),
    same_implementation_and_api_source_sha256=a.sha(old.encode()),
    bijectivity_client_sha256=a.sha(block(a.before(PRODUCER).decode(),
      ' theorem Hom.imageSectionMap_bijective',' @[expose] def Hom.imageSectionEquiv').encode())),indent=2)+'\n')
  (H/PRODUCER).write_text(old);run('old-module-clients',PRODUCER,False)
  (H/PRODUCER).write_bytes(snapshots[PRODUCER])
  old_results={}
  for i,p in enumerate(CLIENTS):
   (H/p).write_bytes(a.before(p));old_results[p]=run('old-external-'+str(i),p)
   (H/p).write_bytes(snapshots[p])
  (OUT/'comparison.json').write_text(json.dumps(dict(all_frozen_new_clients_passed=True,producer_client_tail_unchanged=True,old_module_clients_failed=True,old_external_exit_codes=old_results,axiom_closures_checked=19),indent=2)+'\n')
 finally:
  for p,b in snapshots.items():(H/p).write_bytes(b)
  state=dict(source_restored=all((H/p).read_bytes()==b for p,b in snapshots.items()),frozen_downstream_unchanged=all(a.sha((H/p).read_bytes())==h for p,h in frozen.items()),lake_artifacts_unchanged=all(a.sha(Path(p).read_bytes())==h for p,h in artifacts.items()),artifacts=artifacts)
  (OUT/'restoration.json').write_text(json.dumps(state,indent=2)+'\n')
  assert all(state[k] for k in ('source_restored','frozen_downstream_unchanged','lake_artifacts_unchanged'))
if __name__=='__main__':main()
