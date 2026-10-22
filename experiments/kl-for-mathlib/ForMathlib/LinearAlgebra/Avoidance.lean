module
public import Mathlib

public section

/-! Semantic home: ForMathlib.LinearAlgebra.Avoidance. Source spans: ReflectionSchedules:1, ReflectionOrders:6.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.ReflectionSchedules
open Polynomial
universe u v
variable {I : Type u} [Fintype I]
noncomputable section

@[expose] def coordinatePolynomial (a : I → ℝ) : ℝ[X] :=
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

@[expose] def momentFunctional (t : ℝ) : Module.Dual ℝ (I → ℝ) where
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
