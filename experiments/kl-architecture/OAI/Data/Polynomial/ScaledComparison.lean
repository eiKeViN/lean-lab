import Mathlib
import OAI.Data.Polynomial.ReciprocalRigidity

/-! Semantic home: OAI.Data.Polynomial.ScaledComparison. Source spans: SimultaneousInvariance:7, PositiveTransfer:7, SimultaneousInvariance:5.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.Comparison
open Polynomial
 theorem polynomial_eq_of_transfer_eval_eq (p q : ℤ[X])
    (h : ∀ t : ℝ, 0<t → t<1 →
      eval₂ (Int.castRingHom ℝ) (t⁻¹-t) p=eval₂ (Int.castRingHom ℝ) (t⁻¹-t) q) : p=q := by
  apply Polynomial.map_injective (f := Int.castRingHom ℝ) Int.cast_injective
  apply Polynomial.eq_of_infinite_eval_eq
  have hinj : Set.InjOn (fun t : ℝ => t⁻¹-t) (Set.Ioo 0 1) := by
    apply StrictAntiOn.injOn
    intro x hx y _ hxy
    exact sub_lt_sub (inv_lt_inv₀ (lt_trans hx.1 hxy) hx.1 |>.mpr hxy) hxy
  apply (Set.Ioo_infinite (show (0:ℝ)<1 by norm_num)).image hinj |>.mono
  rintro _ ⟨t,ht,rfl⟩
  simpa only [eval_map,Set.mem_ofPred_eq] using h t ht.1 ht.2
end KLInvariance.Comparison
end


section
namespace KLInvariance.Comparison

/-- Degree-one labels, `q=t²`, and exactly the source degree
`2*k = length(y)-length(x)-1` give the same coefficient at every edge. -/
 theorem edge_scalar_identity {t : ℝ} (ht : t ≠ 0) (m n k : ℤ)
    (h : m + 2*k = n-1) :
    t^m * (t^2)^k * (1-t^2) = (t⁻¹-t) * t^n := by
  have hp : (t^2)^k = t^(2*k) := by
    rw [zpow_mul]
    norm_num
  rw [hp,← zpow_add₀ ht,h]
  have hsub : t^(n-1) = t^n*t⁻¹ := by
    rw [sub_eq_add_neg,zpow_add₀ ht,zpow_neg_one]
  rw [hsub]
  have hcancel : t⁻¹*t=1 := inv_mul_cancel₀ ht
  calc
    t^n*t⁻¹*(1-t^2) = (t⁻¹-t*(t⁻¹*t))*t^n := by ring
    _ = (t⁻¹-t)*t^n := by rw [hcancel,mul_one]

 theorem transferCoefficient_pos {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    0 < t⁻¹-t := by
  have hi : 1 < t⁻¹ := (one_lt_inv₀ ht).mpr ht1
  linarith

 theorem stateScale_pos {t : ℝ} (ht : 0 < t) (ht1 : t < 1) (N : ℕ) (m : ℤ) :
    0 < (1-t^2)^N * t^m := by
  have hsq : t^2 < 1 := by nlinarith
  exact mul_pos (pow_pos (sub_pos.mpr hsq) _) (zpow_pos ht _)

/-- Cancellation of a positive state scale converts an additive normalized
edge identity back to its raw Hilbert-series increment. -/
 theorem scaled_increment_eq_iff (a x y k z : ℝ) (ha : a ≠ 0) :
    a*x = a*y+(a*k)*z ↔ x-y=k*z := by
  constructor
  · intro h
    have he : a*x=a*(y+k*z) := by linear_combination h
    have hc := mul_left_cancel₀ ha he
    linarith
  · intro h
    rw [show x=y+k*z by linarith]
    ring

end KLInvariance.Comparison
end


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
