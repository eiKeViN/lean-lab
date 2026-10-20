import Mathlib

/-! Semantic home: OAI.Algebra.Module.Quotient.EdgeHom. Source spans: SheafMorphisms:9.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.QuotientEdge
variable {R M N E F : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup E] [Module R E] [AddCommGroup F] [Module R F]
noncomputable section

 def descend (f : M →ₗ[R] E) (g : N →ₗ[R] F)
    (hf : Function.Surjective f) (h : M →ₗ[R] N)
    (hk : LinearMap.ker f ≤ LinearMap.ker (g.comp h)) : E →ₗ[R] F :=
  ((LinearMap.ker f).liftQ (g.comp h) hk).comp (f.quotKerEquivOfSurjective hf).symm.toLinearMap

 theorem descend_apply (f : M →ₗ[R] E) (g : N →ₗ[R] F)
    (hf : Function.Surjective f) (h : M →ₗ[R] N)
    (hk : LinearMap.ker f ≤ LinearMap.ker (g.comp h)) (v : M) :
    descend f g hf h hk (f v) = g (h v) := by
  simp [descend]

 theorem kernel_scalar_le (f : M →ₗ[R] E) (g : N →ₗ[R] F) (r : R)
    (hf : ∀ v, f v = 0 ↔ ∃ w, v=r • w)
    (hg : ∀ v, g v = 0 ↔ ∃ w, v=r • w) (h : M →ₗ[R] N) :
    LinearMap.ker f ≤ LinearMap.ker (g.comp h) := by
  intro v hv
  obtain ⟨w,rfl⟩ := (hf v).mp hv
  change g (h (r • w))=0
  rw [h.map_smul]
  exact (hg _).mpr ⟨h w,rfl⟩

end
end KLInvariance.QuotientEdge
end

end OAI
