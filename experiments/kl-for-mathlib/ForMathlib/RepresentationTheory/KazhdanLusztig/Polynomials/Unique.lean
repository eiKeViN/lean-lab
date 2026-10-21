import Mathlib
import ForMathlib.Algebra.Polynomial.Reciprocal
import ForMathlib.GroupTheory.Coxeter.Bruhat.Basic
import ForMathlib.RepresentationTheory.KazhdanLusztig.Polynomials.Normalized

/-! Semantic home: ForMathlib.RepresentationTheory.KazhdanLusztig.Polynomials.Unique. Source spans: Bruhat:4, Bruhat:6.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

namespace KLInvariance
open Polynomial
universe u v u' v'
variable {B : Type u} {W : Type v} [klPreservedInstance1 : Group W] {M : CoxeterMatrix B}
/-- The exact R recursion determines at most one R family. -/
theorem normalized_R_unique (cs : CoxeterSystem M W)
    {RP SQ : PolynomialFamilies W} (hRP : NormalizedKL cs RP) (hSQ : NormalizedKL cs SQ) :
    RP.1 = SQ.1 := by
  classical
  suffices ∀ n : ℕ, ∀ y : W, cs.length y = n → ∀ x, RP.1 x y = SQ.1 x y by
    funext x y
    exact this (cs.length y) y rfl x
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro y hy x
    by_cases h1 : y = 1
    · subst y
      by_cases hx : x = 1
      · subst x
        rw [hRP.R_diagonal, hSQ.R_diagonal]
      · have hn : ¬ BruhatLE cs x 1 := by
          intro h
          have hl := length_le_of_bruhat cs h
          have hx0 : cs.length x = 0 := by simpa using hl
          exact hx (cs.length_eq_zero_iff.mp hx0)
        rw [hRP.R_zero _ _ hn, hSQ.R_zero _ _ hn]
    · obtain ⟨i, hi⟩ := cs.exists_leftDescent_of_ne_one h1
      have hlt : cs.length (cs.simple i * y) < n := hy ▸ hi
      rw [hRP.R_recursion x y i hi, hSQ.R_recursion x y i hi]
      rw [ih _ hlt _ rfl x, ih _ hlt _ rfl (cs.simple i * x)]

end KLInvariance


namespace KLInvariance
open Polynomial
universe u v u' v'
variable {B : Type u} {W : Type v} [klPreservedInstance1 : Group W] {M : CoxeterMatrix B}
/-- The polynomial part of the manuscript's normalization is unique; the
proof uses the actual finite strong-Bruhat intervals, not extra assumptions. -/
theorem normalized_P_unique (cs : CoxeterSystem M W)
    {RP SQ : PolynomialFamilies W} (hRP : NormalizedKL cs RP) (hSQ : NormalizedKL cs SQ) :
    RP.2 = SQ.2 := by
  classical
  have hR := normalized_R_unique cs hRP hSQ
  suffices ∀ n : ℕ, ∀ x y : W, rankDifference cs x y = n → RP.2 x y = SQ.2 x y by
    funext x y
    exact this (rankDifference cs x y) x y rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro x y hxy
    by_cases hcomp : BruhatLE cs x y
    · by_cases heq : x = y
      · subst y
        rw [hRP.P_diagonal, hSQ.P_diagonal]
      · let : Finite (Interval cs x y) := interval_finite cs x y
        let : Fintype (Interval cs x y) := Fintype.ofFinite _
        let bottom : Interval cs x y := ⟨x, bruhat_refl cs x, hcomp⟩
        have hsum : (∑ z : Interval cs x y,
            RP.1 x z.val * (RP.2 z.val y - SQ.2 z.val y)) = RP.2 x y - SQ.2 x y := by
          rw [Finset.sum_eq_single bottom]
          · simp [bottom, hRP.R_diagonal]
          · intro z _ hz
            have hxz : x ≠ z.val := by
              intro hc
              apply hz
              exact Subtype.ext hc.symm
            have hlt := length_lt_of_bruhat_ne cs z.property.1 hxz
            have hle := length_le_of_bruhat cs z.property.2
            have hdiff : rankDifference cs z.val y < n := by
              dsimp [rankDifference] at hxy ⊢
              omega
            rw [ih _ hdiff z.val y rfl, sub_self, mul_zero]
          · simp
        have href : reflect (rankDifference cs x y) (RP.2 x y - SQ.2 x y) =
            RP.2 x y - SQ.2 x y := by
          rw [reflect_sub, hRP.reciprocity x y hcomp, hSQ.reciprocity x y hcomp,
            finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, ← Finset.sum_sub_distrib]
          rw [← hsum]
          apply Finset.sum_congr rfl
          intro z _
          rw [← hR, mul_sub]
        have hd1 := hRP.P_degree x y hcomp heq
        have hd2 := hSQ.P_degree x y hcomp heq
        have hdeg := natDegree_sub_le (RP.2 x y) (SQ.2 x y)
        have hzero := low_degree_reflect_eq_self (RP.2 x y - SQ.2 x y)
          (rankDifference cs x y) (by omega) href
        exact sub_eq_zero.mp hzero
    · rw [hRP.P_zero _ _ hcomp, hSQ.P_zero _ _ hcomp]

/-- Unique existence is still a separate obligation: this proves its
uniqueness half only, without postulating a normalized family. -/
theorem normalizedKL_unique (cs : CoxeterSystem M W)
    {RP SQ : PolynomialFamilies W} (hRP : NormalizedKL cs RP) (hSQ : NormalizedKL cs SQ) :
    RP = SQ :=
  Prod.ext (normalized_R_unique cs hRP hSQ) (normalized_P_unique cs hRP hSQ)

end KLInvariance

end OAI
