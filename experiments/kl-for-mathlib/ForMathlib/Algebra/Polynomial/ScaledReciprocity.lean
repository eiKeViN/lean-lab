import Mathlib
import ForMathlib.Algebra.Polynomial.Reciprocal

/-! Semantic home: ForMathlib.Algebra.Polynomial.ScaledReciprocity. Source spans: SimultaneousInvariance:5.
See migration.json and MIGRATION.md for exact provenance. -/

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

 theorem matrix_difference_single {V : Type*} [Fintype V] (a : V → ℝ)
    (v w : V → ℝ) (x : V) (hdiag : a x=1)
    (hvw : ∀ y, y ≠ x → v y=w y) :
    (∑ y, a y*v y)-(∑ y, a y*w y)=v x-w x := by
  classical
  rw [← Finset.sum_sub_distrib]
  calc
    (∑ y, (a y*v y-a y*w y)) = ∑ y, if y=x then v x-w x else 0 := by
      apply Finset.sum_congr rfl
      intro y _
      by_cases hy : y=x
      · subst y
        simp [hdiag]
      · simp [hy,hvw y hy]
    _ = v x-w x := by simp

 theorem matrix_difference_le {V : Type*} [Fintype V]
    (a : V → ℝ) (v w : V → ℝ) (x : V) (p p' : ℝ)
    (hdiag : a x=1) (hvw : ∀ y, y ≠ x → v y=w y)
    (hp : p ≤ ∑ y, a y*v y) (hp' : p'=∑ y, a y*w y) :
    p-p' ≤ v x-w x := by
  rw [← matrix_difference_single a v w x hdiag hvw]
  exact sub_le_sub hp hp'.ge

end
end KLInvariance.Comparison
end

end OAI
