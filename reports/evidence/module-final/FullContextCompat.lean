import ImplementationImports
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
  let all ← ofExcept (Json.parse (← IO.FS.readFile "module-final-old.json"))
  let oldGroups ← ofExcept (← ofExcept (all.getObjVal? "groups")).getObj?
  let helperGroups ← ofExcept (← ofExcept (all.getObjVal? "helpers")).getObj?
  let order ← ofExcept (all.getObjValAs? (Array Json) "order")
  let mut helperNames : Array Name := #[]
  for row in order do
    let row ← ofExcept row.getArr?
    let group ← ofExcept row[0]!.getStr?
    let i : Nat ← ofExcept (fromJson? row[1]!)
    let d := helperGroups[group]!
    let a ← ofExcept (← ofExcept (d.getObjValAs? (Array Json) "aux"))[i]!.getArr?
    helperNames := helperNames.push (← ofExcept (readName a[0]!))
  let rename := fun (e : Expr) => e.replace fun e => match e with
    | .const n us => if helperNames.contains n then some (.const (`BatchOld ++ n) us) else none
    | _ => none
  for row in order do
    let row ← ofExcept row.getArr?
    let group ← ofExcept row[0]!.getStr?
    let i : Nat ← ofExcept (fromJson? row[1]!)
    let d := helperGroups[group]!
    let es ← ofExcept (decode (← ofExcept (d.getObjValAs? (Array Json) "nodes")))
    let a ← ofExcept (← ofExcept (d.getObjValAs? (Array Json) "aux"))[i]!.getArr?
    let n ← ofExcept (readName a[0]!)
    let us ← (← ofExcept a[1]!.getArr?).toList.mapM fun x => ofExcept (readName x)
    let ti : Nat ← ofExcept (fromJson? a[2]!)
    let vi : Nat ← ofExcept (fromJson? a[3]!)
    unless (← ofExcept a[4]!.getStr?) == "theorem" do throwError "unexpected helper kind"
    addDecl <| .thmDecl {
      name := `BatchOld ++ n
      levelParams := us
      type := rename es[ti]!
      value := rename es[vi]!
    }
  unless !(← isDefEq (mkConst ``Nat) (mkConst ``Bool)) do throwError "negative defeq control failed"
  let attrs ← ofExcept (Json.parse (← IO.FS.readFile "module-final-attributes.json"))
  let current ← ofExcept (Json.parse (← IO.FS.readFile "module-final-current.json"))
  for (_, old) in oldGroups.toArray do
    let es ← ofExcept (decode (← ofExcept (old.getObjValAs? (Array Json) "nodes")))
    let records ← ofExcept (old.getObjValAs? (Array Json) "records")
    for r in records do
      let a ← ofExcept r.getArr?
      let user ← ofExcept (readName a[0]!)
      if user.toString.contains "match_" then continue
      let n ← realizeGlobalConstNoOverload (mkIdent user)
      let ci ← getConstInfo n
      let expectedAttrs ← ofExcept (attrs.getObjVal? user.toString)
      let env ← getEnv
      unless defeqAttr.hasTag env n == (← ofExcept (expectedAttrs.getObjValAs? Bool "defeq")) &&
          backwardDefeqAttr.hasTag env n == (← ofExcept (expectedAttrs.getObjValAs? Bool "backward_defeq")) do
        throwError "changed actual equation attributes: {user}"
      let i : Nat ← ofExcept (fromJson? a[2]!)
      let oldType := rename es[i]!
      check oldType
      check ci.type
      let fixed ← ofExcept (current.getObjVal? user.toString)
      let fixedEs ← ofExcept (decode (← ofExcept (fixed.getObjValAs? (Array Json) "nodes")))
      let fixedTi ← ofExcept (fixed.getObjValAs? Nat "type")
      unless ExprStructEq.mk ci.type == ExprStructEq.mk fixedEs[fixedTi]! do
        throwError "unbound new actual expression: {user}"
      unless ← isDefEq oldType ci.type do throwError "not defeq: {user}"
      let historical := `HistoricalBatchUse ++ user
      addDecl <| .thmDecl {
        name := historical
        levelParams := ci.levelParams
        type := oldType
        value := .const n (ci.levelParams.map .param)
      }
      let axioms ← collectAxioms historical
      unless axioms.all (fun x => [``propext, ``Classical.choice, ``Quot.sound].contains x) do
        throwError "unexpected axiom: {user} {axioms}"
      forallTelescope ci.type fun xs body => do
        let some (_, lhs, rhs) := body.eq? | throwError "not equation: {user}"
        let proof := mkAppN (.const n (ci.levelParams.map .param)) xs
        let goal ← mkFreshExprSyntheticOpaqueMVar body
        let rewritten ← goal.mvarId!.rewrite lhs proof
        unless ← isDefEq rewritten.eNew rhs do throwError "rw changed target {user}"
        check rewritten.eqProof
        let thms ← ({} : SimpTheorems).add (.decl n) ci.levelParams.toArray proof
        let ctx ← Simp.mkContext (simpTheorems := #[thms])
        let (simplified, stats) ← simp lhs ctx
        unless stats.usedTheorems.contains (.decl n) do throwError "simp did not use actual equation: {user}"
        unless ← isDefEq simplified.expr rhs do throwError "simp changed target {user}"
        if let some p := simplified.proof? then check p
      logInfo m!"PASS directed rewrite/simp actual equation: {user}"
      logInfo m!"PASS actual historical type/kernel/defeq/axioms: {user}; actual={n}"
  for n in helperNames do
    let axioms ← collectAxioms (`BatchOld ++ n)
    unless axioms.all (fun x => [``propext, ``Classical.choice, ``Quot.sound].contains x) do
      throwError "unexpected helper axiom {n}"
  logInfo m!"Kernel checked {helperNames.size} actual old helper type/value pairs under fresh names"

open OAI.KLInvariance OAI.KLInvariance.MomentGraph
open scoped BigOperators
section VertexControls
universe u v
variable {V : Type u} {E : Type u} [PartialOrder V] (G : OrderedGraph V E) (x : V)
#check splitVertex.eq_1
#check splitEdge.eq_1
example : (splitVertex x).symm ⊥ = x := rfl
example : (splitVertex x).symm ⊥ = x := by rw [splitVertex.eq_1]; rfl
example : (splitVertex x).symm ⊥ = x := by simp only [splitVertex.eq_1]; rfl
example (e : {e : E // G.source e ≠ x}) : (splitEdge G x).symm (Sum.inl e) = e.val := rfl
example (e : {e : E // G.source e ≠ x}) : (splitEdge G x).symm (Sum.inl e) = e.val := by
  rw [splitEdge.eq_1]; rfl
example (e : {e : E // G.source e ≠ x}) : (splitEdge G x).symm (Sum.inl e) = e.val := by
  simp only [splitEdge.eq_1]; rfl
example (y : V) : (splitVertex x).symm (splitVertex x y) = y := Equiv.symm_apply_apply _ _
example (e : E) : (splitEdge G x).symm (splitEdge G x e) = e := Equiv.symm_apply_apply _ _
end VertexControls
section PairControls
variable (R : Type*) [CommRing R] (a b : R × R)
#check ReflectionFrobenius.crossPair.eq_1
example : ReflectionFrobenius.crossPair R a b = a.1*b.2+a.2*b.1 := rfl
example : ReflectionFrobenius.crossPair R a b = a.1*b.2+a.2*b.1 := by
  rw [ReflectionFrobenius.crossPair.eq_1]; rfl
example : ReflectionFrobenius.crossPair R a b = a.1*b.2+a.2*b.1 := by
  simp only [ReflectionFrobenius.crossPair.eq_1]; rfl
end PairControls
section DiagonalControls
universe u v w
variable {R : Type u} [CommRing R] {X : Type v} {E : X → Type w}
  [∀ x, AddCommGroup (E x)] [∀ x, Module R (E x)] (f : X → R) (a : ∀ x, E x) (x : X)
#check FiniteCharacterLocalization.diagonal.eq_1
example : FiniteCharacterLocalization.diagonal f a x = f x • a x := rfl
example : FiniteCharacterLocalization.diagonal f a x = f x • a x := by
  rw [FiniteCharacterLocalization.diagonal.eq_1]; rfl
example : FiniteCharacterLocalization.diagonal f a x = f x • a x := by
  simp only [FiniteCharacterLocalization.diagonal.eq_1]; rfl
end DiagonalControls
section MomentControls
universe u
variable {I : Type u} [Fintype I] (t : ℝ) (a : I → ℝ)
#check ReflectionSchedules.momentFunctional.eq_1
example : ReflectionSchedules.momentFunctional t a = ∑ i, a i * t^(Fintype.equivFin I i).val := rfl
example : ReflectionSchedules.momentFunctional t a = ∑ i, a i * t^(Fintype.equivFin I i).val := by
  rw [ReflectionSchedules.momentFunctional.eq_1]; rfl
example : ReflectionSchedules.momentFunctional t a = ∑ i, a i * t^(Fintype.equivFin I i).val := by
  simp only [ReflectionSchedules.momentFunctional.eq_1]; rfl
end MomentControls
#check Dihedral.pairMatrix.eq_1
#check TitsSpace.Represents.extendedAction_eq
#check TitsSpace.simplePositive.eq_1
#check TitsSpace.height.eq_1
