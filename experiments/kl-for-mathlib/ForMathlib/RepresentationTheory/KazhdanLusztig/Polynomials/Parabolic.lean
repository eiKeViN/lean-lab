import Mathlib
import ForMathlib.GroupTheory.Coxeter.Parabolic.Standard
import ForMathlib.RepresentationTheory.KazhdanLusztig.Polynomials.Canonical

/-! Semantic home: ForMathlib.RepresentationTheory.KazhdanLusztig.Polynomials.Parabolic. Source spans: Tits:23.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

namespace KLInvariance.StandardParabolic
open CoxeterSystem
universe u v
variable {I : Type u} {W : Type v} [Group W] {M : CoxeterMatrix I}
variable (cs : CoxeterSystem M W) (J : Set I) [Fintype J]
noncomputable section

/-- Restriction of the actual normalized families satisfies their exact
recurrence, degree bound and interval reciprocity in the standard parabolic. -/
theorem normalized_restriction {RP : PolynomialFamilies W} (hRP : NormalizedKL cs RP) :
    NormalizedKL (system (M := M) J)
      (fun x y => RP.1 (inclusion cs J x) (inclusion cs J y),
       fun x y => RP.2 (inclusion cs J x) (inclusion cs J y)) where
  R_diagonal x := hRP.R_diagonal _
  R_zero x y hxy := hRP.R_zero _ _ (fun h => hxy ((bruhat_inclusion_iff cs J x y).1 h))
  R_recursion := by
    intro x y i hy
    have hs (z : (matrix (M := M) J).Group) :
        inclusion cs J ((system (M := M) J).simple i * z) =
          cs.simple i.val * inclusion cs J z := by rw [map_mul, inclusion_simple]
    have hl (z : (matrix (M := M) J).Group) :
        cs.length (cs.simple i.val * inclusion cs J z) =
          (system (M := M) J).length ((system (M := M) J).simple i * z) := by
      rw [← hs, length_inclusion]
    have h := hRP.R_recursion (inclusion cs J x) (inclusion cs J y) i.val
      (by rwa [hl, length_inclusion])
    simpa only [hs, hl, length_inclusion] using h
  P_diagonal x := hRP.P_diagonal _
  P_zero x y hxy := hRP.P_zero _ _ (fun h => hxy ((bruhat_inclusion_iff cs J x y).1 h))
  P_degree := by
    intro x y hxy hne
    have h := hRP.P_degree (inclusion cs J x) (inclusion cs J y)
      ((bruhat_inclusion_iff cs J x y).2 hxy) (fun h => hne (inclusion_injective cs J h))
    rwa [rankDifference_inclusion] at h
  reciprocity := by
    intro x y hxy
    have h := hRP.reciprocity (inclusion cs J x) (inclusion cs J y)
      ((bruhat_inclusion_iff cs J x y).2 hxy)
    rw [rankDifference_inclusion] at h
    rw [h]
    let := interval_finite cs (inclusion cs J x) (inclusion cs J y)
    let := interval_finite (system (M := M) J) x y
    let := Fintype.ofFinite (Interval cs (inclusion cs J x) (inclusion cs J y))
    let := Fintype.ofFinite (Interval (system (M := M) J) x y)
    simp only [finsum_eq_sum_of_fintype]
    exact ((intervalIso cs J x y).toEquiv.sum_comp
      (fun z => RP.1 (inclusion cs J x) z.val * RP.2 z.val (inclusion cs J y))).symm

theorem klFamilies_inclusion :
    (fun x y => rPolynomial cs (inclusion cs J x) (inclusion cs J y),
     fun x y => klPolynomial cs (inclusion cs J x) (inclusion cs J y)) =
      klFamilies (system (M := M) J) :=
  normalizedKL_unique _ (normalized_restriction cs J (klFamilies_spec cs))
    (klFamilies_spec _)

theorem klPolynomial_inclusion (x y : (matrix (M := M) J).Group) :
    klPolynomial cs (inclusion cs J x) (inclusion cs J y) =
      klPolynomial (system (M := M) J) x y :=
  congrFun (congrFun (congrArg Prod.snd (klFamilies_inclusion cs J)) x) y

theorem rPolynomial_inclusion (x y : (matrix (M := M) J).Group) :
    rPolynomial cs (inclusion cs J x) (inclusion cs J y) =
      rPolynomial (system (M := M) J) x y :=
  congrFun (congrFun (congrArg Prod.fst (klFamilies_inclusion cs J)) x) y

end
end KLInvariance.StandardParabolic

end OAI
