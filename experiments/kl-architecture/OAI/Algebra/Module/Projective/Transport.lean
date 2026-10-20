import Mathlib
import OAI.Algebra.Module.ReflectionPair.Twist

/-! Semantic home: OAI.Algebra.Module.Projective.Transport. Source spans: IntegralPairings:15.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance
universe ur um un up
variable {R : Type ur} [CommRing R]
  {M : Type um} [AddCommGroup M] [Module R M]
  {N : Type un} [AddCommGroup N] [Module R N]
  {P : Type up} [AddCommGroup P] [Module R P]
noncomputable section
 theorem projective_of_same_range (f : M →ₗ[R] P) (hf : Function.Injective f)
    (g : N →ₗ[R] P) (hg : Function.Injective g) (h : LinearMap.range f=LinearMap.range g)
    [Module.Projective R N] : Module.Projective R M :=
  Module.Projective.of_equiv (((LinearEquiv.ofInjective g hg).trans
    (LinearEquiv.ofEq _ _ h.symm)).trans (LinearEquiv.ofInjective f hf).symm)

attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

namespace ReflectionPairTranslation.Twist
 theorem projective (τ : R ≃+* R) [Module.Projective R N] : Module.Projective R (Twist τ N) := by
  let : RingHomInvPair τ.symm.toRingHom τ.toRingHom := RingHomInvPair.of_ringEquiv_symm τ
  let : RingHomInvPair τ.toRingHom τ.symm.toRingHom := RingHomInvPair.of_ringEquiv τ
  exact Module.Projective.of_equiv (σ' := τ.toRingHom) (equiv τ N)
end ReflectionPairTranslation.Twist
end
end KLInvariance
end

end OAI
