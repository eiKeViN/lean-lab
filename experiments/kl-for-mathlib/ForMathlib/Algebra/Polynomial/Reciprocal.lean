import Mathlib

/-! Semantic home: ForMathlib.Algebra.Polynomial.Reciprocal. Source spans: Bruhat:7, Comparison:1, Hecke:5.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

namespace KLInvariance
open Polynomial
/-- The degree/reciprocity rigidity used both by normalization uniqueness and
by the final main-theorem induction: no polynomial supported strictly below
the midpoint can be self-reciprocal about that midpoint. -/
theorem low_degree_reflect_eq_self (f : ℤ[X]) (d : ℕ)
    (hd : 2 * f.natDegree < d) (hself : reflect d f = f) : f = 0 := by
  by_contra hn
  have hc := congrArg (fun p : ℤ[X] => p.coeff f.natDegree) hself
  rw [coeff_reflect, revAt_le (by omega)] at hc
  rw [coeff_eq_zero_of_natDegree_lt (by omega), coeff_natDegree] at hc
  exact (leadingCoeff_ne_zero.mpr hn) hc.symm

end KLInvariance


namespace KLInvariance.Comparison
open Polynomial
/-- A polynomial supported strictly below the middle cannot equal its
reciprocal on an open real interval. This discharges the final rigidity
step after the source's two comparison inequalities have been combined. -/
theorem low_degree_zero_of_eval_reciprocal (p : ℝ[X]) (d : ℕ)
    (hp : 2 * p.natDegree < d)
    (h : ∀ q : ℝ, 0 < q → q < 1 → p.eval q = q ^ d * p.eval q⁻¹) : p = 0 := by
  have heq : p = reflect d p := by
    apply p.eq_of_infinite_eval_eq
    apply (Set.Ioo_infinite (show (0 : ℝ) < 1 by norm_num)).mono
    intro q hq
    change p.eval q = (reflect d p).eval q
    let : Invertible q⁻¹ := invertibleOfNonzero (inv_ne_zero (ne_of_gt hq.1))
    have hr := eval₂_reflect_mul_pow (RingHom.id ℝ) q⁻¹ d p (by omega)
    simp only [eval₂_id, invOf_eq_inv, inv_inv] at hr
    have hr' := congrArg (fun z : ℝ => z * q ^ d) hr
    have hq0 : q ≠ 0 := ne_of_gt hq.1
    simp only [mul_assoc, ← mul_pow, inv_mul_cancel₀ hq0, one_pow, mul_one] at hr'
    calc
      p.eval q = q ^ d * p.eval q⁻¹ := h q hq.1 hq.2
      _ = (reflect d p).eval q := by
        simpa only [mul_comm] using hr'.symm
  by_contra hp0
  have hc := congrArg (fun f : ℝ[X] => f.coeff p.natDegree) heq.symm
  rw [coeff_reflect, revAt_le (by omega), coeff_eq_zero_of_natDegree_lt (by omega),
    coeff_natDegree] at hc
  exact (leadingCoeff_ne_zero.mpr hp0) hc.symm

/-- The exact polynomial conclusion from reciprocal difference equality,
without assuming positivity of KL coefficients. -/
theorem eq_of_eval_difference_reciprocal (p p' : ℤ[X]) (d : ℕ)
    (hp : 2 * p.natDegree < d) (hp' : 2 * p'.natDegree < d)
    (h : ∀ q : ℝ, 0 < q → q < 1 →
      p.eval₂ (Int.castRingHom ℝ) q - p'.eval₂ (Int.castRingHom ℝ) q =
      q ^ d * (p.eval₂ (Int.castRingHom ℝ) q⁻¹ -
        p'.eval₂ (Int.castRingHom ℝ) q⁻¹)) : p = p' := by
  apply sub_eq_zero.mp
  apply Polynomial.map_injective (f := Int.castRingHom ℝ) Int.cast_injective
  rw [Polynomial.map_zero]
  apply low_degree_zero_of_eval_reciprocal ((p - p').map (Int.castRingHom ℝ)) d
  · have hdeg := Polynomial.natDegree_map_le (f := Int.castRingHom ℝ) (p := p - p')
    have hsub := Polynomial.natDegree_sub_le p p'
    omega
  · intro q hq hq'
    simpa only [eval_map, eval₂_sub] using h q hq hq'

end KLInvariance.Comparison


namespace KLInvariance
open Polynomial
/-- Reflection of a bounded-degree polynomial evaluated at an actual unit. -/
theorem eval₂_reflect_unit {C : Type*} [CommRing C] (q : Cˣ)
    (p : ℤ[X]) (d : ℕ) (hp : p.natDegree ≤ d) :
    Polynomial.eval₂ (Int.castRingHom C) (q : C) (reflect d p) =
      (q : C) ^ d * Polynomial.eval₂ (Int.castRingHom C) (↑q⁻¹ : C) p := by
  let := q⁻¹.invertible
  have h := Polynomial.eval₂_reflect_mul_pow (Int.castRingHom C) (↑q⁻¹ : C) d p hp
  simp only [invOf_units, inv_inv] at h
  have h' := congrArg (fun a : C => a * (q : C) ^ d) h
  calc
    _ = Polynomial.eval₂ (Int.castRingHom C) (↑q⁻¹ : C) p * (q : C) ^ d := by
      simpa only [mul_assoc, ← mul_pow, q.inv_mul, one_pow, mul_one] using h'
    _ = _ := mul_comm _ _


end KLInvariance

end OAI
