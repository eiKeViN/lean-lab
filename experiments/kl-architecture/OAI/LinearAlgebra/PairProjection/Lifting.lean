import Mathlib
import OAI.LinearAlgebra.PairProjection.Basic

/-! Semantic home: OAI.LinearAlgebra.PairProjection.Lifting. Source spans: IntegralPairings:12.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.PairProjection
universe u v w z
variable {R : Type u} [CommRing R]
  {N : Type v} [AddCommGroup N] [Module R N]
  {X : Type w} [AddCommGroup X] [Module R X]
  {Y : Type z} [AddCommGroup Y] [Module R Y]
  (f : N →ₗ[R] X) (g : N →ₗ[R] Y)

 theorem cross_lift (α : R) (hann : ∀ z : Edge f g, α • z=0)
    (p q : N) (h : ∃ n : N, p-q=α • n) :
    ∃ n : N, f n=f q ∧ g n=g p := by
  apply (compatible_iff f g _ _).mp
  obtain ⟨n,hn⟩ := h
  have hd := congrArg ((lower f g).comp f) hn
  simp only [LinearMap.comp_apply,map_sub,map_smul,hann] at hd
  exact (sub_eq_zero.mp hd).symm.trans (compatible f g p)

end KLInvariance.PairProjection
end

end OAI
