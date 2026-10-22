module
public import Mathlib

public section

/-! Semantic home: ForMathlib.Algebra.Module.Submodule.ScaledImage. Source spans: GradedSheaves:8.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.EmbeddedModule
variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

@[expose] def scaled (r : R) (K : Submodule R M) : Submodule R M :=
  K.map (LinearMap.lsmul R M r)

theorem map_scaled (j : M ≃ₗ[R] N) (r : R) (K : Submodule R M) :
    (scaled r K).map j.toLinearMap = scaled r (K.map j.toLinearMap) := by
  simp only [scaled,← Submodule.map_comp]
  congr 1
  ext v
  exact j.map_smul r v

/-- Scalar comparison is transported by one and the same edge isomorphism. -/
theorem map_eq_scaled_iff (j : M ≃ₗ[R] N) (r : R) (I J : Submodule R M) :
    I.map j.toLinearMap = scaled r (J.map j.toLinearMap) ↔ I = scaled r J := by
  rw [← map_scaled]
  constructor
  · intro h
    have h' := congrArg (Submodule.map j.symm.toLinearMap) h
    simpa only [← Submodule.map_comp,LinearEquiv.symm_comp,
      Submodule.map_id] using h'
  · exact congrArg (Submodule.map j.toLinearMap)

end KLInvariance.EmbeddedModule
end

end OAI
