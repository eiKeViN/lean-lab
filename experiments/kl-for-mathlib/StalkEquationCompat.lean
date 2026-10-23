module
import ForMathlib.Combinatorics.MomentGraph.GradedSheaf.AttachBottom
import Lean


open Lean
namespace BoundaryCodec
partial def nameJson : Name → Json
  | .anonymous => Json.arr #[]
  | .str p s => toJson (#[nameJson p, toJson s])
  | .num p n => toJson (#[nameJson p, toJson n, Json.null])
partial def levelJson : Level → Json
  | .zero => toJson (#[toJson "zero"])
  | .succ u => toJson (#[toJson "succ", levelJson u])
  | .max u v => toJson (#[toJson "max", levelJson u, levelJson v])
  | .imax u v => toJson (#[toJson "imax", levelJson u, levelJson v])
  | .param n => toJson (#[toJson "param", nameJson n])
  | .mvar _ => panic! "unclosed level"
structure Dump where
  ids : ExprStructMap Nat := {}
  nodes : Array Json := #[]
partial def encode (e : Expr) : StateM Dump Nat := do
  if let .mdata _ b := e then return ← encode b
  if let some i := (← get).ids[ExprStructEq.mk e]? then return i
  let node : Array Json ← match e with
    | .bvar n => pure #[toJson "bvar", toJson n]
    | .sort u => pure #[toJson "sort", levelJson u]
    | .const n us => pure #[toJson "const", nameJson n, toJson (us.map levelJson)]
    | .app f a => do pure #[toJson "app", toJson (← encode f), toJson (← encode a)]
    | .lam n t b bi | .forallE n t b bi => do
      let tag := if e.isLambda then "lam" else "forall"
      let bi := match bi with | .default => 0 | .implicit => 1 | .strictImplicit => 2 | .instImplicit => 3
      pure #[toJson tag, nameJson n, toJson (← encode t), toJson (← encode b), toJson bi]
    | .letE n t v b nondep => do pure #[toJson "let", nameJson n, toJson (← encode t), toJson (← encode v), toJson (← encode b), toJson nondep]
    | .lit (.natVal n) => pure #[toJson "nat", toJson n]
    | .lit (.strVal s) => pure #[toJson "str", toJson s]
    | .proj n i b => do pure #[toJson "proj", nameJson n, toJson i, toJson (← encode b)]
    | _ => panic! "unclosed expression"
  let s ← get
  set ({ids := s.ids.insert (ExprStructEq.mk e) s.nodes.size, nodes := s.nodes.push (toJson node)} : Dump)
  return s.nodes.size
partial def readName (j : Json) : Except String Name := do
  let a ← j.getArr?
  if a.isEmpty then return .anonymous
  if a.size == 2 then return .str (← readName a[0]!) (← a[1]!.getStr?)
  if a.size == 3 then return .num (← readName a[0]!) (← fromJson? a[1]!)
  throw "bad name"
partial def readLevel (j : Json) : Except String Level := do
  let a ← j.getArr?
  match ← a[0]!.getStr? with
  | "zero" => do pure (.zero)
  | "succ" => do pure (.succ (← readLevel a[1]!))
  | "max" => do pure (.max (← readLevel a[1]!) (← readLevel a[2]!))
  | "imax" => do pure (.imax (← readLevel a[1]!) (← readLevel a[2]!))
  | "param" => do pure (.param (← readName a[1]!))
  | _ => throw "bad level"
def decode (nodes : Array Json) : Except String (Array Expr) := do
  let mut es := #[]
  for j in nodes do
    let a ← j.getArr?
    let child := fun (i : Nat) => (show Except String Expr from do
      let n : Nat ← fromJson? a[i]!
      if n < es.size then return es[n]! else throw "non-topological DAG")
    let e : Expr ← match ← a[0]!.getStr? with
      | "bvar" => do pure (.bvar (← fromJson? a[1]!))
      | "sort" => do pure (.sort (← readLevel a[1]!))
      | "const" => do pure (.const (← readName a[1]!) (← (← a[2]!.getArr?).toList.mapM readLevel))
      | "app" => do pure (.app (← child 1) (← child 2))
      | "lam" | "forall" => do
        let bi : Nat ← fromJson? a[4]!
        let bi ← match bi with | 0 => pure BinderInfo.default | 1 => pure .implicit | 2 => pure .strictImplicit | 3 => pure .instImplicit | _ => throw "bad binder"
        if (← a[0]!.getStr?) == "lam" then pure (.lam (← readName a[1]!) (← child 2) (← child 3) bi)
        else pure (.forallE (← readName a[1]!) (← child 2) (← child 3) bi)
      | "let" => do pure (.letE (← readName a[1]!) (← child 2) (← child 3) (← child 4) (← fromJson? a[5]!))
      | "nat" => do pure (.lit (.natVal (← fromJson? a[1]!)))
      | "str" => do pure (.lit (.strVal (← fromJson? a[1]!)))
      | "proj" => do pure (.proj (← readName a[1]!) (← fromJson? a[2]!) (← child 3))
      | _ => throw "bad expression"
    es := es.push e
  return es
end BoundaryCodec

open Lean Meta Elab Command BoundaryCodec
run_elab do
  let oldPath := "stalk-equation-old.json"

  let old ← ofExcept (Json.parse (← IO.FS.readFile oldPath))

  let oldEs ← ofExcept (decode (← ofExcept (old.getObjValAs? (Array Json) "nodes")))

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

  let oldType := renameExpr oldEs[ti]!
  let some eqs ← Lean.Meta.getEqnsFor? ``OAI.KLInvariance.MomentGraph.Sheaf.stalkMap | throwError "missing equations"
  let n := eqs[0]!
  unless (privateToUserName? n).getD n == `OAI.KLInvariance.MomentGraph.Sheaf.stalkMap.eq_1 do
    throwError "wrong equation name {n}"
  let ci ← getConstInfo n
  let env ← getEnv
  unless !defeqAttr.hasTag env n && backwardDefeqAttr.hasTag env n do
    throwError "changed equation defeq/backward_defeq attributes"
  logInfo m!"ordinary implementation name={n}; defeq=false; backward_defeq=true"
  let newType := ci.type
  unless !(ExprStructEq.mk oldType == ExprStructEq.mk newType) do throwError "expected distinct expressions"
  Lean.Meta.check oldType
  Lean.Meta.check newType
  unless ← isDefEq oldType newType do throwError "not definitionally equal"
  unless !(← isDefEq (mkConst ``Nat) (mkConst ``Bool)) do throwError "negative type control failed"
  addDecl <| .thmDecl {
    name := `StalkEquationHistoricalUse
    levelParams := ci.levelParams
    type := oldType
    value := .const ci.name (ci.levelParams.map .param)
  }
  for n in names.push `StalkEquationHistoricalUse do
    let actualName := if n == `StalkEquationHistoricalUse then n else `BoundaryOld ++ n
    let axioms ← collectAxioms actualName
    unless axioms.all (fun a => [``propext, ``Quot.sound, ``Classical.choice].contains a) do
      throwError "unexpected axiom closure {axioms}"
  logInfo m!"{names.size} actual legacy auxiliary proofs kernel-checked under fresh names; both actual equation types well-formed; stored expressions differ; definitional equality passes; Nat/Bool negative control passes; three-axiom bound passes"

open OAI.KLInvariance.MomentGraph
universe u v w z
variable {R : Type u} [CommRing R] {V : Type v} [PartialOrder V] {E : Type w}
  {G : OrderedGraph V E} (B : Sheaf.{u,v,w,z} (R := R) G) (x : V)
#check Sheaf.stalkMap.eq_1
example (b : B.vertex x) (e : Sheaf.Outgoing (G := G) x) :
    B.stalkMap x b e = B.lower e.val (e.property.symm ▸ b) := rfl
example (b : B.vertex x) (e : Sheaf.Outgoing (G := G) x) :
    B.stalkMap x b e = B.lower e.val (e.property.symm ▸ b) := by
  rw [Sheaf.stalkMap.eq_1]
  rfl
example (b : B.vertex x) (e : Sheaf.Outgoing (G := G) x) :
    B.stalkMap x b e = B.lower e.val (e.property.symm ▸ b) := by
  simp only [Sheaf.stalkMap.eq_1]
  rfl
