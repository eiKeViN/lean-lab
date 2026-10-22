module
public import Mathlib

public section

/-! Semantic home: ForMathlib.Algebra.Module.Projective.Range. Source spans: IntegralPairings:7, IntegralPairings:20.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.ProjectiveRange
universe ur um up uq
variable {R : Type ur} [CommRing R]
  {M : Type um} [AddCommGroup M] [Module R M]
  {P : Type up} [AddCommGroup P] [Module R P]
  {Q : Type uq} [AddCommGroup Q] [Module R Q]
noncomputable section

 @[expose] def descend (f : M →ₗ[R] P) (hf : Function.Surjective f) (g : M →ₗ[R] Q)
    (hg : ∀ m, f m=0 → g m=0) : P →ₗ[R] Q :=
  ((LinearMap.ker f).liftQ g hg).comp (f.quotKerEquivOfSurjective hf).symm.toLinearMap

 theorem descend_apply (f : M →ₗ[R] P) (hf : Function.Surjective f) (g : M →ₗ[R] Q)
    (hg : ∀ m, f m=0 → g m=0) (m : M) : descend f hf g hg (f m)=g m := by
  change (LinearMap.ker f).liftQ g hg ((f.quotKerEquivOfSurjective hf).symm (f m))=g m
  rw [LinearMap.quotKerEquivOfSurjective_symm_apply]
  rfl

 theorem projective_of_end (f : M →ₗ[R] P) (hf : Function.Surjective f)
    [Module.Projective R M] (e : Module.End R M)
    (he : ∀ m, f (e m)=f m) (hz : ∀ m, f m=0 → e m=0) : Module.Projective R P := by
  apply Module.Projective.of_split (descend f hf e hz) f
  apply LinearMap.ext
  intro p
  obtain ⟨m,rfl⟩ := hf p
  rw [LinearMap.comp_apply,descend_apply,he,LinearMap.id_apply]

 @[expose] def kernelRetraction (f : M →ₗ[R] P) (s : P →ₗ[R] M)
    (hs : ∀ p, f (s p)=p) : M →ₗ[R] LinearMap.ker f :=
  (LinearMap.id-s.comp f).codRestrict (LinearMap.ker f) (fun m => by
    change f (m-s (f m))=0
    rw [map_sub,hs,sub_self])

 theorem kernel_projective (f : M →ₗ[R] P) (hf : Function.Surjective f)
    [Module.Projective R M] [Module.Projective R P] : Module.Projective R (LinearMap.ker f) := by
  obtain ⟨s,hs⟩ := Module.projective_lifting_property f (LinearMap.id : P →ₗ[R] P) hf
  have hs' : ∀ p, f (s p)=p := LinearMap.congr_fun hs
  apply Module.Projective.of_split (LinearMap.ker f).subtype (kernelRetraction f s hs')
  apply LinearMap.ext
  intro m
  apply Subtype.ext
  change (m : M)-s (f m)=m
  rw [m.property,map_zero,sub_zero]

 @[expose] def splitEquiv (f : M →ₗ[R] P) (s : P →ₗ[R] M) (hs : ∀ p, f (s p)=p) :
    M ≃ₗ[R] (LinearMap.ker f × P) :=
  { (kernelRetraction f s hs).prod f with
    invFun := fun z => z.1.val+s z.2
    left_inv := fun m => sub_add_cancel m (s (f m))
    right_inv := by
      intro z
      apply Prod.ext
      · apply Subtype.ext
        change z.1.val+s z.2-s (f (z.1.val+s z.2))=z.1.val
        rw [map_add,z.1.property,zero_add,hs]
        exact add_sub_cancel_right _ _
      · change f (z.1.val+s z.2)=z.2
        rw [map_add,z.1.property,zero_add,hs] }

 theorem projective_of_kernel (f : M →ₗ[R] P) (hf : Function.Surjective f)
    [Module.Projective R P] [Module.Projective R (LinearMap.ker f)] : Module.Projective R M := by
  obtain ⟨s,hs⟩ := Module.projective_lifting_property f (LinearMap.id : P →ₗ[R] P) hf
  exact Module.Projective.of_equiv (splitEquiv f s (LinearMap.congr_fun hs)).symm

end
end KLInvariance.ProjectiveRange
end


section
namespace KLInvariance.ProjectiveRange
universe ur um uh up us
variable {R : Type ur} [CommRing R]
  {M : Type um} [AddCommGroup M] [Module R M]
  {H : Type uh} [AddCommGroup H] [Module R H]
  {P : Type up} [AddCommGroup P] [Module R P]
  {S : Type us} [AddCommGroup S] [Module R S]
  (r : M →ₗ[R] H) (f : M →ₗ[R] P) (k : P →ₗ[R] S)
  (h : ∀ m, r m=0 → k (f m)=0)
noncomputable section

 @[expose] def onKernel : LinearMap.ker r →ₗ[R] LinearMap.ker k :=
  (f.comp (LinearMap.ker r).subtype).codRestrict (LinearMap.ker k) (fun m => h m.val m.property)

 @[expose] def kernelOnKernelEquiv : ↥(LinearMap.ker r ⊓ LinearMap.ker f) ≃ₗ[R]
    LinearMap.ker (onKernel r f k h) where
  toFun z := ⟨⟨z.val,z.property.1⟩,Subtype.ext z.property.2⟩
  invFun z := ⟨z.val.val,z.val.property,congrArg Subtype.val z.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

 theorem projective_of_two_stage (hr : Function.Surjective r)
    (hf : Function.Surjective (onKernel r f k h))
    [Module.Projective R H] [Module.Projective R (LinearMap.ker k)]
    [Module.Projective R ↥(LinearMap.ker r ⊓ LinearMap.ker f)] :
    Module.Projective R M := by
  let : Module.Projective R (LinearMap.ker (onKernel r f k h)) :=
    Module.Projective.of_equiv (kernelOnKernelEquiv r f k h)
  let : Module.Projective R (LinearMap.ker r) := projective_of_kernel (onKernel r f k h) hf
  exact projective_of_kernel r hr
end
end KLInvariance.ProjectiveRange
end

end OAI
