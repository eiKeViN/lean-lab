import Mathlib
import ForMathlib.Algebra.Polynomial.Reciprocal

/-! Semantic home: ForMathlib.Algebra.Polynomial.ScaledEvaluation. Source spans: SimultaneousInvariance:5/scaled-evaluation.
See migration.json and MIGRATION.md for exact provenance.
Scaled evaluation of integer polynomials over the reals and reciprocal-difference rigidity. No weighted-sum cancellation or graph data is required. -/

namespace OAI

section
namespace KLInvariance.Comparison
open Polynomial
noncomputable section

def scaledPolynomial (t : ℝ) (d : ℕ) (p : ℤ[X]) : ℝ :=
  t ^ (-(d : ℤ)) * p.eval₂ (Int.castRingHom ℝ) (t^2)

/-- A positive real in the open unit interval has a square root in the same
interval. Use the witness to change variables without carrying a concrete sqrt. -/
theorem exists_pos_sq_eq_of_mem_Ioo (q : ℝ) (hq : 0 < q) (hq1 : q < 1) :
    ∃ t : ℝ, 0 < t ∧ t < 1 ∧ t ^ 2 = q := by
  refine ⟨Real.sqrt q, Real.sqrt_pos.mpr hq, ?_, Real.sq_sqrt hq.le⟩
  nlinarith [Real.sq_sqrt hq.le]

/-- Clear reciprocal polynomial evaluation scaling at a nonzero real point.
Use this algebraic step before changing variables; positivity is not required. -/
theorem eval_difference_of_scaled_reciprocal (p p' : ℤ[X]) (d : ℕ) (t : ℝ)
    (ht : t ≠ 0)
    (h : scaledPolynomial t d p - scaledPolynomial t d p' =
      scaledPolynomial t⁻¹ d p - scaledPolynomial t⁻¹ d p') :
    p.eval₂ (Int.castRingHom ℝ) (t ^ 2) - p'.eval₂ (Int.castRingHom ℝ) (t ^ 2) =
      (t ^ 2) ^ d * (p.eval₂ (Int.castRingHom ℝ) (t ^ 2)⁻¹ -
        p'.eval₂ (Int.castRingHom ℝ) (t ^ 2)⁻¹) := by
  have he := h
  simp only [scaledPolynomial, zpow_neg, zpow_natCast, inv_pow, inv_inv,
    ← mul_sub] at he
  have hh := congrArg (fun z : ℝ => t ^ d * z) he
  rw [← mul_assoc, mul_inv_cancel₀ (pow_ne_zero d ht), one_mul] at hh
  rw [← mul_assoc, ← pow_add] at hh
  rw [show d + d = 2 * d by omega, pow_mul] at hh
  exact hh

 theorem eq_of_scaled_difference_reciprocal (p p' : ℤ[X]) (d : ℕ)
    (hp : 2*p.natDegree < d) (hp' : 2*p'.natDegree < d)
    (h : ∀ t : ℝ, 0 < t → t < 1 →
      scaledPolynomial t d p-scaledPolynomial t d p' =
        scaledPolynomial t⁻¹ d p-scaledPolynomial t⁻¹ d p') : p=p' := by
  apply eq_of_eval_difference_reciprocal p p' d hp hp'
  intro q hq hq1
  obtain ⟨t, ht, ht1, hsq⟩ := exists_pos_sq_eq_of_mem_Ioo q hq hq1
  have he := eval_difference_of_scaled_reciprocal p p' d t ht.ne' (h t ht ht1)
  simpa only [hsq] using he

end
end KLInvariance.Comparison
end

end OAI
