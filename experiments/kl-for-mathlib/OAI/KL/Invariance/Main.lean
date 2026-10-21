import Mathlib
import ForMathlib.RepresentationTheory.KazhdanLusztig.Polynomials.FiniteRankReduction
import OAI.KL.Invariance.Finite

/-! Semantic home: OAI.KL.Invariance.Main. Source spans: Invariance:9.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance
open Module TitsSpace BruhatGraph
universe u v u' v'
variable {B : Type u} {W : Type v} [Group W] {M : CoxeterMatrix B}
noncomputable section

 theorem combinatorial_invariance
    {B' : Type u'} {W' : Type v'} [Group W'] {M' : CoxeterMatrix B'}
    (cs : CoxeterSystem M W) (cs' : CoxeterSystem M' W')
    {u b : W} {u' b' : W'}
    (hub : BruhatLE cs u b) (hub' : BruhatLE cs' u' b')
    (ι : Interval cs u b ≃o Interval cs' u' b') :
    klPolynomial cs u b = klPolynomial cs' u' b' := by
  obtain ⟨F⟩ := exists_finiteIntervalModel cs u b hub
  obtain ⟨F'⟩ := exists_finiteIntervalModel cs' u' b' hub'
  let : Fintype F.indices := F.finite.fintype
  let : Fintype F'.indices := F'.finite.fintype
  let basis := Module.Free.chooseBasis ℝ (Extended (StandardParabolic.matrix (M := M) F.indices))
  let basis' := Module.Free.chooseBasis ℝ (Extended (StandardParabolic.matrix (M := M') F'.indices))
  rw [←F.kl_eq,←F'.kl_eq]
  exact klPolynomial_invariance_finite basis basis' F.lower F.upper F'.lower F'.upper
    (F.bruhat hub) (F'.bruhat hub') ((F.orderIso.trans ι).trans F'.orderIso.symm)

end
end KLInvariance
end

end OAI
