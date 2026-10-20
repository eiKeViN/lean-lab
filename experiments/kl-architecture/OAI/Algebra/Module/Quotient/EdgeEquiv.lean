import Mathlib

/-! Semantic home: OAI.Algebra.Module.Quotient.EdgeEquiv. Source spans: GradedSheaves:13.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.QuotientEdge
variable {R M N E F : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup E] [Module R E] [AddCommGroup F] [Module R F]

/-- The edge isomorphism forced by an upper stalk isomorphism and exact quotient maps. -/
noncomputable def iso (f : M →ₗ[R] E) (g : N →ₗ[R] F)
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    (h : M ≃ₗ[R] N) (hk : (LinearMap.ker f).map h.toLinearMap = LinearMap.ker g) : E ≃ₗ[R] F :=
  (f.quotKerEquivOfSurjective hf).symm.trans
    ((Submodule.Quotient.equiv _ _ h hk).trans (g.quotKerEquivOfSurjective hg))

@[simp] lemma iso_apply (f : M →ₗ[R] E) (g : N →ₗ[R] F)
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    (h : M ≃ₗ[R] N) (hk : (LinearMap.ker f).map h.toLinearMap = LinearMap.ker g) (v : M) :
    iso f g hf hg h hk (f v) = g (h v) := by
  simp [iso,Submodule.Quotient.equiv]

lemma map_kernel_scalar (f : M →ₗ[R] E) (g : N →ₗ[R] F) (r : R)
    (hf : ∀ v, f v = 0 ↔ ∃ w, v = r • w)
    (hg : ∀ v, g v = 0 ↔ ∃ w, v = r • w) (h : M ≃ₗ[R] N) :
    (LinearMap.ker f).map h.toLinearMap = LinearMap.ker g := by
  ext v
  constructor
  · rintro ⟨w,hw,rfl⟩
    obtain ⟨u,rfl⟩ := (hf w).mp hw
    exact (hg _).mpr ⟨h u,h.map_smul r u⟩
  · intro hv
    obtain ⟨w,rfl⟩ := (hg v).mp hv
    refine ⟨r • h.symm w,(hf _).mpr ⟨h.symm w,rfl⟩,?_⟩
    simp

/-- No separate choice of edge data or scalar compatibility hypothesis is needed. -/
theorem exists_scalar_iso (f : M →ₗ[R] E) (g : N →ₗ[R] F) (r : R)
    (hfs : Function.Surjective f) (hgs : Function.Surjective g)
    (hf : ∀ v, f v = 0 ↔ ∃ w, v = r • w)
    (hg : ∀ v, g v = 0 ↔ ∃ w, v = r • w) (h : M ≃ₗ[R] N) :
    ∃ j : E ≃ₗ[R] F, ∀ v, j (f v) = g (h v) :=
  ⟨iso f g hfs hgs h (map_kernel_scalar f g r hf hg h),iso_apply f g hfs hgs h _⟩

end KLInvariance.QuotientEdge
end

end OAI
