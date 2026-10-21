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

 theorem eq_of_scaled_difference_reciprocal (p p' : ℤ[X]) (d : ℕ)
    (hp : 2*p.natDegree < d) (hp' : 2*p'.natDegree < d)
    (h : ∀ t : ℝ, 0 < t → t < 1 →
      scaledPolynomial t d p-scaledPolynomial t d p' =
        scaledPolynomial t⁻¹ d p-scaledPolynomial t⁻¹ d p') : p=p' := by
  apply eq_of_eval_difference_reciprocal p p' d hp hp'
  intro q hq hq1
  let t := Real.sqrt q
  have ht : 0 < t := Real.sqrt_pos.2 hq
  have hsq : t^2=q := Real.sq_sqrt hq.le
  have ht1 : t < 1 := by nlinarith
  have hisq : (t⁻¹)^2=q⁻¹ := by rw [inv_pow,hsq]
  have he := h t ht ht1
  simp only [scaledPolynomial,zpow_neg,zpow_natCast,inv_pow,inv_inv,hsq,hisq,
    ← mul_sub] at he
  have hh := congrArg (fun z : ℝ => t^d*z) he
  have htd : t^d ≠ 0 := pow_ne_zero d ht.ne'
  rw [← mul_assoc,mul_inv_cancel₀ htd,one_mul] at hh
  rw [← mul_assoc,← pow_add] at hh
  rw [show d+d=2*d by omega,pow_mul,hsq] at hh
  exact hh

end
end KLInvariance.Comparison
end

end OAI
