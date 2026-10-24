from pathlib import Path
import json,subprocess,os,time,hashlib
root=Path.cwd();h=root/'experiments/kl-for-mathlib';d=root/'results/module-final/decisions';lean=root/'.cache/lean-4.34.1-linux/bin/lean';paths=subprocess.check_output(['lake','env','printenv','LEAN_PATH'],cwd=h,text=True).strip();env=dict(os.environ,LEAN_PATH=str(d)+':'+paths,LEAN_NUM_THREADS='2');runs=[]
def run(label,file,expect=0,compile=False):
 cmd=[str(lean),'-R',str(d)]
 if compile:cmd+=['-o',str(d/(file+'.olean'))]
 cmd+=[str(d/(file+'.lean'))];start=time.monotonic()
 with (d/(label+'.log')).open('w') as log:status=subprocess.call(cmd,cwd=h,env=env,stdout=log,stderr=subprocess.STDOUT)
 runs.append(dict(label=label,command=cmd,source_sha256=hashlib.sha256((d/(file+'.lean')).read_bytes()).hexdigest(),expected_exit=expect,actual_exit=status,wall_seconds=time.monotonic()-start));print(label,status,flush=True)
 if status!=expect:print((d/(label+'.log')).read_text()[-3000:]);raise RuntimeError('Unexpected control outcome '+label)
base='0917d25afb52e46cae4233d3056020ed6f881fa3';p='ForMathlib/Algebra/Module/CoefficientChange/Basic.lean';s=subprocess.check_output(['git','show',base+':experiments/kl-for-mathlib/'+p],text=True);plan=json.loads((root/'results/module-final/first-scope.json').read_text())['files'][p]
for e in sorted(plan['edits'],key=lambda e:e['start'],reverse=True):s=s[:e['start']]+e['new']+s[e['start']+len(e['old']):]
(d/'TrialCoefficientChange.lean').write_text(s);run('trial-coefficient-producer','TrialCoefficientChange',compile=True)
for mode in ['Legacy','Modern']:
 s=('module\n' if mode=='Modern' else '')+'import TrialCoefficientChange\n#check OAI.KLInvariance.CoefficientChange.ext\n#check OAI.KLInvariance.CoefficientChange.ext.match_1\n';(d/(mode+'CoefficientConsumer.lean')).write_text(s);run(mode.lower()+'-coefficient-consumer',mode+'CoefficientConsumer',1)
p='ForMathlib/Combinatorics/MomentGraph/Sheaf/Structure.lean';s=subprocess.check_output(['git','show',base+':experiments/kl-for-mathlib/'+p],text=True);s=s[s.index('namespace OAI'):s.index(' theorem structureSheaf_free')];s+='\nend\nend\nend\nend\n';head='import Mathlib\nimport ForMathlib.Combinatorics.MomentGraph.Sheaf.Basic\n';(d/'LegacyStructureActual.lean').write_text(head+s);run('legacy-structure-producer','LegacyStructureActual',compile=True)
modern='module\n'+head.replace('import ','public import ')+'\npublic section\n'+s.replace(' def structureSheaf','@[expose] def structureSheaf');(d/'ModernStructureOriginal.lean').write_text(modern);run('private-structure-control','ModernStructureOriginal',1)
inline=modern.replace('(quotientLinear α e)','((Ideal.Quotient.mkₐ R (Ideal.span {α e})).toLinearMap)');assert inline!=modern;(d/'InlineStructureActual.lean').write_text(inline);run('inline-structure-producer','InlineStructureActual',compile=True)
body='''open OAI.KLInvariance.MomentGraph
universe ur uv ue
variable {R : Type ur} [CommRing R] {V : Type uv} [PartialOrder V]
  {E : Type ue} (G : OrderedGraph V E) (α : E → R) (c x : V)
#check Sheaf.structureSheaf
example : (Sheaf.structureSheaf G α c).vertex x = ModuleCat.of R (PLift (x ≤ c) → R) := rfl
example (e : E) : (Sheaf.structureSheaf G α c).upper e =
    LinearMap.pi (fun h => ((Ideal.Quotient.mkₐ R (Ideal.span {α e})).toLinearMap).comp (LinearMap.proj h)) := rfl
example (e : E) : (Sheaf.structureSheaf G α c).lower e =
    LinearMap.pi (fun h => ((Ideal.Quotient.mkₐ R (Ideal.span {α e})).toLinearMap).comp
      (LinearMap.proj ⟨(G.increasing e).le.trans h.down⟩)) := rfl
'''
for mode,module in [('Legacy','LegacyStructureActual'),('Modern','InlineStructureActual')]:
 text=('module\n' if mode=='Modern' else '')+'import '+module+'\nimport Lean\n'+body
 if mode=='Modern':text+='''open Lean Elab Command in
run_elab do
  let visible ← try let _ ← realizeGlobalConstNoOverload (mkIdent `OAI.KLInvariance.MomentGraph.Sheaf.quotientLinear); pure true catch _ => pure false
  if visible then throwError "private quotient helper became public"
  logInfo "Private helper remains unavailable; vertex/upper/lower rfl controls pass."
'''
 (d/(mode+'StructureConsumer.lean')).write_text(text);run(mode.lower()+'-structure-consumer',mode+'StructureConsumer')
(d/'bounded-controls-results.json').write_text(json.dumps(runs,indent=2)+'\n')
