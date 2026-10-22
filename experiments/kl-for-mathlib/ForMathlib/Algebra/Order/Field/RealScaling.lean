module
public import Mathlib

public section

/-! Semantic home: ForMathlib.Algebra.Order.Field.RealScaling. Source spans: PositiveTransfer:7.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

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

end OAI
