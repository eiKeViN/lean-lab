import Mathlib

/-! Semantic home: OAI.Data.Polynomial.LowPart. Source spans: CanonicalKL:1.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

namespace KLInvariance.CanonicalP
open Polynomial
noncomputable def lowPart (d : ℕ) (p : ℤ[X]) : ℤ[X] :=
  ∑ n ∈ Finset.range ((d + 1) / 2), Polynomial.monomial n (p.coeff n)

@[simp] theorem coeff_lowPart (d : ℕ) (p : ℤ[X]) (n : ℕ) :
    (lowPart d p).coeff n = if 2 * n < d then p.coeff n else 0 := by
  classical
  simp only [lowPart, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
  rw [Finset.sum_ite_eq']
  have he : n < (d + 1) / 2 ↔ 2 * n < d := by omega
  simp only [Finset.mem_range, he]

theorem lowPart_degree (d : ℕ) (p : ℤ[X]) (hd : 0 < d) :
    2 * (lowPart d p).natDegree < d := by
  have h : (lowPart d p).natDegree ≤ (d - 1) / 2 := by
    apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro n hn
    rw [coeff_lowPart, ite_eq_right (by omega)]
  omega

/-- Solve the anti-reciprocal defect with the required strict degree bound. -/
theorem lowPart_solution (d : ℕ) (p : ℤ[X]) (hanti : reflect d p = -p) :
    reflect d (-lowPart d p) = -lowPart d p + p := by
  apply Polynomial.ext
  intro n
  have hc := congrArg (fun f : ℤ[X] => f.coeff n) hanti
  simp only [Polynomial.coeff_reflect, Polynomial.coeff_neg] at hc
  simp only [Polynomial.coeff_reflect, Polynomial.coeff_neg, Polynomial.coeff_add,
    coeff_lowPart]
  by_cases hn : n ≤ d
  · rw [Polynomial.revAt_le hn] at hc ⊢
    by_cases hlow : 2 * n < d
    · rw [ite_eq_left hlow, ite_eq_right (by omega)]
      ring
    · rw [ite_eq_right hlow]
      by_cases hmid : 2 * n = d
      · have hm : d - n = n := by omega
        rw [hm, ite_eq_right hlow]
        rw [hm] at hc
        linarith
      · rw [ite_eq_left (by omega)]
        linarith
  · rw [Polynomial.revAt_eq_self_of_lt (by omega)] at hc ⊢
    rw [ite_eq_right (by omega)]
    linarith

end KLInvariance.CanonicalP

end OAI
