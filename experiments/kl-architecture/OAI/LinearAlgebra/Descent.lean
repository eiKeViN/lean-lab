import Mathlib

/-! Semantic home: OAI.LinearAlgebra.Descent. Source spans: BalancedPairings:9.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace LinearDescent
universe ur um ux
variable {R : Type ur} [CommRing R]
  {M : Type um} [AddCommGroup M] [Module R M]
  {X : Type ux} [AddCommGroup X] [Module R X]
  (f : M →ₗ[R] X) (hf : Function.Surjective f) (e : Module.End R M)
  (he : ∀ m, f m=0 → f (e m)=0)
noncomputable section

 def descend : Module.End R X :=
  ((LinearMap.ker f).liftQ (f.comp e) he).comp
    (f.quotKerEquivOfSurjective hf).symm.toLinearMap

 theorem descend_apply (m : M) : descend f hf e he (f m)=f (e m) := by
  change (LinearMap.ker f).liftQ (f.comp e) he
    ((f.quotKerEquivOfSurjective hf).symm (f m))=f (e m)
  rw [LinearMap.quotKerEquivOfSurjective_symm_apply]
  rfl

 theorem descend_idempotent (hee : ∀ m, e (e m)=e m) (x : X) :
    descend f hf e he (descend f hf e he x)=descend f hf e he x := by
  obtain ⟨m,rfl⟩ := hf x
  rw [descend_apply,descend_apply,hee]

end
end LinearDescent
end

end OAI
