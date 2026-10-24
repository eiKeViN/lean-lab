import Lean
import Mathlib

/-! Semantic home: ForMathlib.LinearAlgebra.Avoidance. Source spans: ReflectionSchedules:1, ReflectionOrders:6.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.ReflectionSchedules
open Polynomial
universe u v
variable {I : Type u} [Fintype I]
noncomputable section

def coordinatePolynomial (a : I → ℝ) : ℝ[X] :=
  ∑ i, Polynomial.monomial (Fintype.equivFin I i).val (a i)

theorem coordinatePolynomial_coeff (a : I → ℝ) (j : I) :
    (coordinatePolynomial a).coeff (Fintype.equivFin I j).val = a j := by
  classical
  rw [coordinatePolynomial, Polynomial.finsetSum_coeff, Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    have hne : (Fintype.equivFin I i).val ≠ (Fintype.equivFin I j).val := by
      intro h
      exact hij ((Fintype.equivFin I).injective (Fin.ext h))
    simp [Polynomial.coeff_monomial,hne]
  · simp

theorem coordinatePolynomial_injective : Function.Injective (coordinatePolynomial (I := I)) := by
  intro a b h
  funext i
  simpa only [coordinatePolynomial_coeff] using congrArg (fun p : ℝ[X] => p.coeff
    (Fintype.equivFin I i).val) h

def momentFunctional (t : ℝ) : Module.Dual ℝ (I → ℝ) where
  toFun a := ∑ i, a i * t^(Fintype.equivFin I i).val
  map_add' a b := by simp [add_mul,Finset.sum_add_distrib]
  map_smul' r a := by simp [Finset.mul_sum,mul_assoc]

theorem coordinatePolynomial_eval (a : I → ℝ) (t : ℝ) :
    (coordinatePolynomial a).eval t = momentFunctional t a := by
  simp [coordinatePolynomial,momentFunctional,Polynomial.eval_finsetSum]


theorem exists_generic_functional {A : Type v} [Countable A]
    (v : A → (I → ℝ)) (hv : Function.Injective v) :
    ∃ f : Module.Dual ℝ (I → ℝ), Function.Injective (fun a => f (v a)) := by
  classical
  let P := {p : A × A // p.1 ≠ p.2}
  let d : P → ℝ[X] := fun p => coordinatePolynomial (v p.val.1) - coordinatePolynomial (v p.val.2)
  have hd : ∀ p, d p ≠ 0 := by
    intro p h
    exact p.property (hv (coordinatePolynomial_injective (sub_eq_zero.mp h)))
  let bad : Set ℝ := ⋃ p : P, {t | (d p).IsRoot t}
  have hbad : bad.Countable := Set.countable_iUnion (fun p => (Polynomial.finite_setOfPred_isRoot (hd p)).countable)
  have hex : ∃ t, t ∉ bad := by
    by_contra h
    push Not at h
    have heq : bad = Set.univ := Set.eq_univ_of_forall h
    rw [heq] at hbad
    exact Set.not_countable_univ hbad
  obtain ⟨t,ht⟩ := hex
  refine ⟨momentFunctional t,fun a b hab => ?_⟩
  change momentFunctional t (v a) = momentFunctional t (v b) at hab
  by_contra hne
  apply ht
  apply Set.mem_iUnion.mpr
  refine ⟨⟨(a,b),hne⟩,?_⟩
  change (coordinatePolynomial (v a) - coordinatePolynomial (v b)).eval t = 0
  rw [Polynomial.eval_sub,coordinatePolynomial_eval,coordinatePolynomial_eval,hab,sub_self]

end
end KLInvariance.ReflectionSchedules
end


section
namespace KLInvariance.ReflectionSchedules
open Polynomial
universe u v
variable {I : Type u} [Fintype I]
noncomputable section

/-- A countable family of nonzero vectors can be simultaneously avoided. -/
theorem exists_avoiding_functional {A : Type v} [Countable A] (v : A → (I → ℝ)) :
    ∃ f : Module.Dual ℝ (I → ℝ), ∀ a, v a ≠ 0 → f (v a) ≠ 0 := by
  classical
  let P := {a : A // v a ≠ 0}
  have hn (a : P) : coordinatePolynomial (v a.val) ≠ 0 := by
    intro h
    apply a.property
    apply coordinatePolynomial_injective
    simpa [coordinatePolynomial] using h
  let bad : Set ℝ := ⋃ a : P, {t | (coordinatePolynomial (v a.val)).IsRoot t}
  have hb : bad.Countable := Set.countable_iUnion
    (fun a => (Polynomial.finite_setOfPred_isRoot (hn a)).countable)
  obtain ⟨t,ht⟩ : ∃ t, t ∉ bad := by
    by_contra h
    push Not at h
    have he : bad=Set.univ := Set.eq_univ_of_forall h
    rw [he] at hb
    exact Set.not_countable_univ hb
  refine ⟨momentFunctional t,fun a ha he => ht ?_⟩
  apply Set.mem_iUnion.mpr
  refine ⟨⟨a,ha⟩,?_⟩
  simpa only [Set.mem_ofPred_eq,Polynomial.IsRoot,coordinatePolynomial_eval] using he

end
end KLInvariance.ReflectionSchedules
end

end OAI

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
  let names : Array Name := #[`OAI.KLInvariance.ReflectionSchedules.momentFunctional.eq_1]
  let env := (← Lean.getEnv).setExporting false
  let mut dump : BoundaryCodec.Dump := {}
  let mut records : Array Json := #[]
  let mut aux : Array Json := #[]
  let mut pending : Array Name := names
  let mut seen : Array Name := #[]
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    if seen.contains n then continue
    seen := seen.push n
    let some ci := env.find? n | throwError "old name missing {n}"
    let (ti, ds) := (BoundaryCodec.encode ci.type).run dump
    dump := ds
    if names.contains n then
      records := records.push (Json.arr #[BoundaryCodec.nameJson n, toJson (ci.levelParams.map BoundaryCodec.nameJson), toJson ti])
    let visit := fun (e : Expr) => e.foldConsts #[] fun n ns =>
      if n.toString.contains "_proof_" || n.toString.contains "match_" then ns.push n else ns
    pending := pending ++ visit ci.type
    if n.toString.contains "_proof_" || n.toString.contains "match_" then
      let some v := ci.value? (allowOpaque := true) | continue
      pending := pending ++ visit v
      let (vi, ds) := (BoundaryCodec.encode v).run dump
      dump := ds
      aux := aux.push (Json.arr #[BoundaryCodec.nameJson n, toJson (ci.levelParams.map BoundaryCodec.nameJson), toJson ti, toJson vi, toJson (match ci with | .thmInfo _ => "theorem" | _ => "def")])
  IO.FS.writeFile "/workspace/lean-lab/results/module-final/ForMathlib.LinearAlgebra.Avoidance.json" ((Json.mkObj [("nodes",toJson dump.nodes),("records",toJson records),("aux",toJson aux)]).compress)
  IO.println s!"Captured {records.size} actual old types and {aux.size} helper declarations."
