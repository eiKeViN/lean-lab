import Mathlib
import OAI.RepresentationTheory.KazhdanLusztig.Polynomials.Parabolic

/-! Semantic home: OAI.RepresentationTheory.KazhdanLusztig.Invariance.FiniteModel. Source spans: Invariance:8.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance
universe u v
variable {I : Type u} {M : CoxeterMatrix I} {W : Type v} [Group W]
  (cs : CoxeterSystem M W) (u b : W)
noncomputable section

structure FiniteIntervalModel where
  indices : Set I
  finite : indices.Finite
  lower : (StandardParabolic.matrix (M := M) indices).Group
  upper : (StandardParabolic.matrix (M := M) indices).Group
  lower_eq : StandardParabolic.inclusion cs indices lower = u
  upper_eq : StandardParabolic.inclusion cs indices upper = b

 theorem exists_finiteIntervalModel (hub : BruhatLE cs u b) :
    Nonempty (FiniteIntervalModel cs u b) := by
  obtain ⟨J,hJ,hJgen⟩ := lower_ideal_finite_generator_support cs b
  obtain ⟨v,hv,hvu⟩ := hJgen u hub
  obtain ⟨w,hw,hwb⟩ := hJgen b (bruhat_refl cs b)
  obtain ⟨v',hv'⟩ := StandardParabolic.lift_word J hv
  obtain ⟨w',hw'⟩ := StandardParabolic.lift_word J hw
  refine ⟨⟨J,hJ,(StandardParabolic.system (M := M) J).wordProd v',
    (StandardParabolic.system (M := M) J).wordProd w',?_,?_⟩⟩
  · rw [StandardParabolic.inclusion_word,hv',hvu]
  · rw [StandardParabolic.inclusion_word,hw',hwb]

def intervalEndpointCongr {a b a' b' : W} (ha : a = a') (hb : b = b') :
    Interval cs a b ≃o Interval cs a' b' := by
  subst a'
  subst b'
  exact OrderIso.refl _

namespace FiniteIntervalModel
variable {cs u b} (F : FiniteIntervalModel cs u b)

 def orderIso : Interval (StandardParabolic.system (M := M) F.indices) F.lower F.upper ≃o
    Interval cs u b := by
  let _ : Fintype F.indices := F.finite.fintype
  have h := StandardParabolic.intervalIso cs F.indices F.lower F.upper
  exact h.trans (intervalEndpointCongr cs F.lower_eq F.upper_eq)

 theorem bruhat (hub : BruhatLE cs u b) :
    BruhatLE (StandardParabolic.system (M := M) F.indices) F.lower F.upper := by
  let _ : Fintype F.indices := F.finite.fintype
  apply (StandardParabolic.bruhat_inclusion_iff cs F.indices F.lower F.upper).mp
  simpa only [F.lower_eq,F.upper_eq] using hub

 theorem kl_eq : klPolynomial (StandardParabolic.system (M := M) F.indices) F.lower F.upper =
    klPolynomial cs u b := by
  let _ : Fintype F.indices := F.finite.fintype
  simpa only [F.lower_eq,F.upper_eq] using
    (StandardParabolic.klPolynomial_inclusion cs F.indices F.lower F.upper).symm

 theorem rank_eq : rankDifference (StandardParabolic.system (M := M) F.indices) F.lower F.upper =
    rankDifference cs u b := by
  let _ : Fintype F.indices := F.finite.fintype
  simpa only [F.lower_eq,F.upper_eq] using
    (StandardParabolic.rankDifference_inclusion cs F.indices F.lower F.upper).symm

end FiniteIntervalModel
end
end KLInvariance
end

end OAI
