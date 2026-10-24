#!/usr/bin/env python3
"""Quotient-induced range map and relational lattice, on real frozen clients.
Run only with no concurrent build. Formal sources/artifacts restore in finally.
"""
import difflib,json,subprocess,time,textwrap
from pathlib import Path
import api_reflection as a
import validate
from semantic_api_split_trial import setup_for
H=a.HERE;OUT=a.ROOT/'results/graded-reflection/trials'
RANGE='ForMathlib/Algebra/Module/Graded/ModuleData/Range.lean'
TWIST='ForMathlib/Algebra/Module/ReflectionPair/Twist.lean'
SCENARIOS={
 'quotient-range':(RANGE,('ForMathlib/Combinatorics/MomentGraph/GradedSheaf/Summand.lean','OAI/KL/BottSamelson/AdjointSheaf.lean')),
 'relational-lattice':(TWIST,('ForMathlib/Algebra/Module/ReflectionPair/TensorKernel.lean','ForMathlib/Algebra/Module/ReflectionPair/TensorDescent.lean','ForMathlib/LinearAlgebra/KernelCoordinates.lean'))}
QUOT_SETUP = """  let F : M →ₗ[A] range f := f.map.rangeRestrict.comp g.map
  have hk : LinearMap.ker e.map ≤ LinearMap.ker F := by
    intro m hm
    apply Subtype.ext
    exact (h m).trans ((congrArg g.map (LinearMap.mem_ker.mp hm)).trans (map_zero g.map))
"""
QUOT_EVAL = """    rcases v with ⟨_,m,rfl⟩
    change ((LinearMap.ker e.map).liftQ F hk
      (e.map.quotKerEquivRange.symm ⟨e.map m,⟨m,rfl⟩⟩)).val = g.map (e.map m)
    exact (congrArg (fun q => ((LinearMap.ker e.map).liftQ F hk q).val)
      (e.map.quotKerEquivRange_symm_apply_image m (by exact ⟨m,rfl⟩))).trans (h m)
"""

def variant(source,kind,repair):
 if kind=='quotient-range':
  i=source.index(' @[expose] def rangeMap');j=source.index(' @[expose] def rangeInclusion',i)
  head=source[i:j].split(' where\n',1)[0]
  source=source[:i]+head+" := by\n"+QUOT_SETUP+"""  let L := ((LinearMap.ker e.map).liftQ F hk).comp e.map.quotKerEquivRange.symm.toLinearMap
  have hv (v : range e) : (L v).val = g.map v.val := by
"""+QUOT_EVAL+"""  exact {
    map := L
    graded := by
      intro n v hn
      change (L v).val ∈ N.piece n
      rw [hv]
      exact g.graded n v.val hn
  }

"""+source[j:]
  if repair:
   i=source.index('theorem rangeMap_projection');j=source.index('/-- The map induced',i)
   head=source[i:j].split(' := by',1)[0]
   source=source[:i]+head+" := by\n"+QUOT_SETUP+"""  apply Subtype.ext
  change ((LinearMap.ker e.map).liftQ F hk
    (e.map.quotKerEquivRange.symm ⟨e.map m,⟨m,rfl⟩⟩)).val = f.map (g.map m)
  exact congrArg (fun q => ((LinearMap.ker e.map).liftQ F hk q).val)
    (e.map.quotKerEquivRange_symm_apply_image m (by exact ⟨m,rfl⟩))

"""+source[j:]

 else:
  i=source.index('@[expose] def lattice');j=source.index('/-- Membership in the twisted lattice',i)
  block=source[i:j];head,body=block.split(' where\n',1)
  source=source[:i]+head+''' := by
  let S : Submodule R (X × Twist τ Y) := {
'''+textwrap.indent(body.rstrip(),'  ')+'''
  }
  exact S.copy {p | PairProjection.lower f g p.1 = PairProjection.upper f g p.2.val}
    (Set.ext (fun p => PairProjection.compatible_iff f g p.1 p.2.val))

'''+source[j:]
  if repair:
   old='p ∈ lattice f g τ α hdiv hinc ↔ ∃ n : N, f n=p.1 ∧ g n=p.2.val := by rfl'
   new='''p ∈ lattice f g τ α hdiv hinc ↔ ∃ n : N, f n=p.1 ∧ g n=p.2.val := by
  exact PairProjection.compatible_iff f g p.1 p.2.val'''
   assert source.count(old)==1;source=source.replace(old,new,1)
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
   (H/producer).write_text(unrepaired);run('changed-implementation-old-api',producer,False)
   (H/producer).write_text(repaired);(out/'modified-producer.lean').write_text(repaired)
   dest=(out/'artifacts'/producer).with_suffix('.olean');dest.parent.mkdir(parents=True,exist_ok=True)
   run('changed-implementation-repaired-api',producer,True,dest);shadows[producer]=dest
   (H/producer).write_bytes(snapshots[producer])
   for i,path in enumerate(clients):
    assert a.sha((H/path).read_bytes())==frozen[path]
    dest=(out/'artifacts'/path).with_suffix('.olean');dest.parent.mkdir(parents=True,exist_ok=True)
    run('frozen-new-'+str(i),path,True,dest);shadows[path]=dest
   run('ordinary-api-client','GradedReflectionChecks.lean',True);a.check_axioms((out/'ordinary-api-client.log').read_text())
   old_results={}
   for i,path in enumerate(clients):
    (H/path).write_bytes(a.before(path));old_results[path]=run('old-client-'+str(i),path)
    (H/path).write_bytes(snapshots[path])
   assert old_results[clients[0]]!=0,old_results
   (out/'comparison.json').write_text(json.dumps(dict(old_exit_codes=old_results,all_frozen_new_clients_passed=True,axiom_closures_checked=36),indent=2)+'\n')
  finally:
   for p,b in snapshots.items():(H/p).write_bytes(b)
   state=dict(source_restored=all((H/p).read_bytes()==b for p,b in snapshots.items()),frozen_downstream_unchanged=all(a.sha((H/p).read_bytes())==h for p,h in frozen.items()),lake_artifacts_unchanged=all(a.sha(Path(p).read_bytes())==h for p,h in artifacts.items()),artifacts=artifacts)
   (out/'restoration.json').write_text(json.dumps(state,indent=2)+'\n');assert all(state[k] for k in ('source_restored','frozen_downstream_unchanged','lake_artifacts_unchanged'))
if __name__=='__main__':main()
