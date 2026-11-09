import ForMathlib.Combinatorics.MomentGraph.Sheaf.Basic
import StalkCodec
open Lean Meta Elab Command BoundaryCodec
run_elab do
  let some oldPath ← IO.getEnv "OLD_STALK_JSON" | throwError "OLD_STALK_JSON missing"
  let some newPath ← IO.getEnv "NEW_STALK_JSON" | throwError "NEW_STALK_JSON missing"
  let old ← ofExcept (Json.parse (← IO.FS.readFile oldPath))
  let new ← ofExcept (Json.parse (← IO.FS.readFile newPath))
  let oldEs ← ofExcept (decode (← ofExcept (old.getObjValAs? (Array Json) "nodes")))
  let newEs ← ofExcept (decode (← ofExcept (new.getObjValAs? (Array Json) "nodes")))
  let aux ← ofExcept (old.getObjValAs? (Array Json) "aux")
  let names ← aux.mapM fun (j : Json) => do let a ← ofExcept j.getArr?; ofExcept (readName a[0]!)
  let renameExpr := fun (e : Expr) => e.replace fun e =>
    match e with
    | .const n us => if names.contains n then some (.const (`BoundaryOld ++ n) us) else none
    | _ => none
  for j in aux do
    let a ← ofExcept j.getArr?
    let n ← ofExcept (readName a[0]!)
    let us ← (← ofExcept a[1]!.getArr?).toList.mapM fun u => ofExcept (readName u)
    let ti : Nat ← ofExcept (fromJson? a[2]!)
    let vi : Nat ← ofExcept (fromJson? a[3]!)
    addDecl <| .thmDecl {
      name := `BoundaryOld ++ n
      levelParams := us
      type := renameExpr oldEs[ti]!
      value := renameExpr oldEs[vi]!
    }
  let ti : Nat ← ofExcept (old.getObjValAs? Nat "type")
  let tj : Nat ← ofExcept (new.getObjValAs? Nat "type")
  let oldType := renameExpr oldEs[ti]!
  let newType := newEs[tj]!
  unless !(ExprStructEq.mk oldType == ExprStructEq.mk newType) do throwError "expected distinct expressions"
  Lean.Meta.check oldType
  Lean.Meta.check newType
  unless ← isDefEq oldType newType do throwError "not definitionally equal"
  unless !(← isDefEq (mkConst ``Nat) (mkConst ``Bool)) do throwError "negative type control failed"
  for n in names do
    let axioms ← collectAxioms (`BoundaryOld ++ n)
    unless axioms.all (fun a => [``propext, ``Quot.sound, ``Classical.choice].contains a) do
      throwError "unexpected axiom closure {axioms}"
  logInfo m!"{names.size} actual legacy auxiliary proofs kernel-checked under fresh names; both actual equation types well-formed; stored expressions differ; definitional equality passes; Nat/Bool negative control passes; three-axiom bound passes"
