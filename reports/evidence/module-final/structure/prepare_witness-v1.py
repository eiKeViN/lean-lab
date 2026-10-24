from pathlib import Path
import json
root=Path.cwd();h=root/'experiments/kl-for-mathlib';r=root/'results/module-final/structure';d=json.loads((r/'old-expressions-v2.json').read_text())
def name(a):return '' if not a else (name(a[0])+'.' if a[0] else '')+str(a[1])
aux={name(a[0]):i for i,a in enumerate(d['aux'])};seen=set();order=[];ch={'app':(1,2),'lam':(2,3),'forall':(2,3),'let':(2,3,4),'proj':(3,)}
def visit(n):
 if n in seen:return
 seen.add(n);i=aux[n];a=d['aux'][i];todo=[a[2],a[3]];used=set();deps=set()
 while todo:
  k=todo.pop()
  if k in used:continue
  used.add(k);v=d['nodes'][k]
  if v[0]=='const':deps.add(name(v[1]))
  todo.extend(v[j] for j in ch.get(v[0],()))
 for k in sorted(deps&aux.keys()):visit(k)
 order.append(i)
for n in aux:visit(n)
d['order']=order;(r/'old-ordered.json').write_text(json.dumps(d,separators=(',',':')))
s=(h/'ModernFinalCompat.lean').read_text();codec=s[s.index('open Lean\n'):s.index('run_elab do')];body='''run_elab do
  let old ← ofExcept (Json.parse (← IO.FS.readFile "../../results/module-final/structure/old-ordered.json"))
  let es ← ofExcept (decode (← ofExcept (old.getObjValAs? (Array Json) "nodes")))
  let aux ← ofExcept (old.getObjValAs? (Array Json) "aux")
  let order ← ofExcept (old.getObjValAs? (Array Nat) "order")
  let names ← aux.mapM fun j => do let a ← ofExcept j.getArr?; ofExcept (readName a[0]!)
  let rename := fun (e : Expr) => e.replace fun e => match e with
    | .const n us => if names.contains n then some (.const (`StructureOld ++ n) us) else none
    | _ => none
  for i in order do
    let a ← ofExcept aux[i]!.getArr?
    let n ← ofExcept (readName a[0]!)
    let us ← (← ofExcept a[1]!.getArr?).toList.mapM fun x => ofExcept (readName x)
    let ti : Nat ← ofExcept (fromJson? a[2]!)
    let vi : Nat ← ofExcept (fromJson? a[3]!)
    let kind ← ofExcept a[4]!.getStr?
    if kind == "theorem" then
      addDecl <| .thmDecl { name := `StructureOld ++ n, levelParams := us,
        type := rename es[ti]!, value := rename es[vi]! }
    else
      let hs ← ofExcept a[5]!.getArr?
      let hint ← ofExcept hs[0]!.getStr?
      let hints : ReducibilityHints ← if hint == "opaque" then pure .opaque
        else if hint == "abbrev" then pure .abbrev
        else do
          let depth : Nat ← ofExcept (fromJson? hs[1]!)
          pure (.regular (UInt32.ofNat depth))
      addDecl <| .defnDecl { name := `StructureOld ++ n, levelParams := us,
        type := rename es[ti]!, value := rename es[vi]!, hints := hints, safety := .safe }
  unless !(← isDefEq (mkConst ``Nat) (mkConst ``Bool)) do throwError "negative type control failed"
  let mut missing : Array Name := #[]
  let mut checked := 0
  let records ← ofExcept (old.getObjValAs? (Array Json) "records")
  for row in records do
    let a ← ofExcept row.getArr?
    let user ← ofExcept (readName a[0]!)
    let found ← try pure (some (← realizeGlobalConstNoOverload (mkIdent user))) catch _ => pure none
    let some n := found | missing := missing.push user; continue
    let ci ← getConstInfo n
    unless toJson (ci.levelParams.map nameJson) == a[1]! do throwError "changed universe parameters {user}"
    let env ← getEnv
    unless defeqAttr.hasTag env n == (← ofExcept (fromJson? a[3]!)) &&
        backwardDefeqAttr.hasTag env n == (← ofExcept (fromJson? a[4]!)) do
      throwError "changed equation attributes {user}"
    let ti : Nat ← ofExcept (fromJson? a[2]!)
    let oldType := rename es[ti]!
    check oldType
    check ci.type
    unless ← isDefEq oldType ci.type do throwError "not defeq {user}"
    let actual := mkConst n (ci.levelParams.map .param)
    if ← isProp oldType then
      addDecl <| .thmDecl { name := `StructureHistoricalUse ++ user, levelParams := ci.levelParams,
        type := oldType, value := actual }
    else
      addDecl <| .defnDecl { name := `StructureHistoricalUse ++ user, levelParams := ci.levelParams,
        type := oldType, value := actual, hints := .opaque, safety := .safe }
    let axioms ← collectAxioms (`StructureHistoricalUse ++ user)
    unless axioms.all (fun x => [``propext, ``Classical.choice, ``Quot.sound].contains x) do
      throwError "unexpected axiom {user} {axioms}"
    checked := checked+1
  for n in names do
    let axioms ← collectAxioms (`StructureOld ++ n)
    unless axioms.all (fun x => [``propext, ``Classical.choice, ``Quot.sound].contains x) do
      throwError "unexpected old helper axiom {n} {axioms}"
  logInfo m!"Historical names/types/levels/attributes/kernel/defeq/axioms: {checked}; unavailable={missing}; actual old helpers={names.size}"
'''
# Avoid layout-sensitive multi-line record comma syntax.
body=body.replace(', levelParams :=', '\n        levelParams :=').replace(',\n        type :=','\n        type :=').replace(', value :=','\n        value :=').replace(', hints :=','\n        hints :=').replace(', safety :=','\n        safety :=')
controls=(root/'results/module-final/decisions/ModernStructureConsumer.lean').read_text();controls=controls[controls.index('open OAI.KLInvariance.MomentGraph'):];controls=controls[:controls.index('open Lean Elab Command in')];controls+='''
#check OAI.KLInvariance.MomentGraph.Sheaf.structureSheaf.eq_1
#check OAI.KLInvariance.MomentGraph.Sheaf.structureBaseChangeIso.eq_1
example (e : E) : (Sheaf.structureSheaf G α c).upper e =
    LinearMap.pi (fun h => ((Ideal.Quotient.mkₐ R (Ideal.span {α e})).toLinearMap).comp (LinearMap.proj h)) := by
  rw [Sheaf.structureSheaf.eq_1]
  rfl
example (e : E) : (Sheaf.structureSheaf G α c).lower e =
    LinearMap.pi (fun h => ((Ideal.Quotient.mkₐ R (Ideal.span {α e})).toLinearMap).comp
      (LinearMap.proj ⟨(G.increasing e).le.trans h.down⟩)) := by
  simp only [Sheaf.structureSheaf.eq_1]
  rfl
'''
(r/'Preflight.lean').write_text('import ImplementationImports\nimport Lean\n'+codec+body+controls)
(r/'ModernConsumer.lean').write_text('module\nimport ForMathlib.Combinatorics.MomentGraph.Sheaf.Structure\nimport Lean\n'+codec+body+controls)
