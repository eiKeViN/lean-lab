module
import ForMathlib.Combinatorics.MomentGraph.Sheaf.Structure
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
  let old ← ofExcept (Json.parse (← IO.FS.readFile "../../results/module-final/structure/old-ordered.json"))
  let es ← ofExcept (decode (← ofExcept (old.getObjValAs? (Array Json) "nodes")))
  let aux : Array Json ← ofExcept (old.getObjValAs? (Array Json) "aux")
  let order ← ofExcept (old.getObjValAs? (Array Nat) "order")
  let names : Array Name ← aux.mapM fun (j : Json) => do let a ← ofExcept j.getArr?; ofExcept (readName a[0]!)
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
      addDecl <| .thmDecl {
        name := `StructureOld ++ n
        levelParams := us
        type := rename es[ti]!
        value := rename es[vi]! }
    else
      let hs ← ofExcept a[5]!.getArr?
      let hint ← ofExcept hs[0]!.getStr?
      let hints : ReducibilityHints ← if hint == "opaque" then pure .opaque
        else if hint == "abbrev" then pure .abbrev
        else do
          let depth : Nat ← ofExcept (fromJson? hs[1]!)
          pure (.regular (UInt32.ofNat depth))
      addDecl <| .defnDecl {
        name := `StructureOld ++ n
        levelParams := us
        type := rename es[ti]!
        value := rename es[vi]!
        hints := hints
        safety := .safe }
  unless !(← isDefEq (mkConst ``Nat) (mkConst ``Bool)) do throwError "negative type control failed"
  let mut missing : Array Name := #[]
  let mut checked := 0
  let records ← ofExcept (old.getObjValAs? (Array Json) "records")
  for row in records do
    let a ← ofExcept row.getArr?
    let user ← ofExcept (readName a[0]!)
    let found ← try pure (some (← realizeGlobalConstNoOverload (mkIdent user))) catch _ => pure none
    if found.isNone then
      missing := missing.push user
      continue
    let n := found.get!
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
      addDecl <| .thmDecl {
        name := `StructureHistoricalUse ++ user
        levelParams := ci.levelParams
        type := oldType
        value := actual }
    else
      addDecl <| .defnDecl {
        name := `StructureHistoricalUse ++ user
        levelParams := ci.levelParams
        type := oldType
        value := actual
        hints := .opaque
        safety := .safe }
    let axioms ← collectAxioms (`StructureHistoricalUse ++ user)
    unless axioms.all (fun x => [``propext, ``Classical.choice, ``Quot.sound].contains x) do
      throwError "unexpected axiom {user} {axioms}"
    checked := checked+1
  unless checked+missing.size == records.size do throwError "incomplete historical checks"
  for n in names do
    let axioms ← collectAxioms (`StructureOld ++ n)
    unless axioms.all (fun x => [``propext, ``Classical.choice, ``Quot.sound].contains x) do
      throwError "unexpected old helper axiom {n} {axioms}"
  logInfo m!"Historical names/types/levels/attributes/kernel/defeq/axioms: {checked}; unavailable={missing}; actual old helpers={names.size}"
open OAI.KLInvariance.MomentGraph
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

#check OAI.KLInvariance.MomentGraph.Sheaf.structureSheaf.eq_1
#check OAI.KLInvariance.MomentGraph.Sheaf.structureBaseChangeIso.eq_1
example : (Sheaf.structureSheaf G α c).vertex x = ModuleCat.of R (PLift (x ≤ c) → R) := by
  rw [Sheaf.structureSheaf.eq_1] <;> rfl
example : (Sheaf.structureSheaf G α c).vertex x = ModuleCat.of R (PLift (x ≤ c) → R) := by
  simp only [Sheaf.structureSheaf.eq_1] <;> rfl
universe us
variable (S : Type us) [CommRing S] [Algebra R S]
example : (Sheaf.structureBaseChangeIso S G α c).vertex x = Sheaf.baseChangePiScalar S (x ≤ c) := rfl
example : (Sheaf.structureBaseChangeIso S G α c).vertex x = Sheaf.baseChangePiScalar S (x ≤ c) := by
  rw [Sheaf.structureBaseChangeIso.eq_1] <;> rfl
example : (Sheaf.structureBaseChangeIso S G α c).vertex x = Sheaf.baseChangePiScalar S (x ≤ c) := by
  simp only [Sheaf.structureBaseChangeIso.eq_1] <;> rfl
