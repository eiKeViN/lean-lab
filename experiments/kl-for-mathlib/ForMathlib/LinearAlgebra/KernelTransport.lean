module
public import Mathlib

public section

/-! Kernel transport under linear equivalences, independently of KL models. -/

namespace OAI

section

/-! Transport of actual linear-map kernels along a source isomorphism. -/
namespace LinearEquiv
universe ur um un up
variable {R : Type ur} [Ring R]
  {M : Type um} [AddCommGroup M] [Module R M]
  {N : Type un} [AddCommGroup N] [Module R N]
  {P : Type up} [AddCommGroup P] [Module R P]

@[expose] def kernelSourceEquiv (f : M →ₗ[R] P) (e : M ≃ₗ[R] N) :
    LinearMap.ker f ≃ₗ[R] LinearMap.ker (f.comp e.symm.toLinearMap) where
  toFun x := ⟨e x.val,by simpa only [LinearMap.mem_ker,LinearMap.comp_apply,
    LinearEquiv.coe_coe,LinearEquiv.symm_apply_apply] using x.property⟩
  invFun y := ⟨e.symm y.val,y.property⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x.val)
  right_inv y := Subtype.ext (e.apply_symm_apply y.val)
  map_add' x y := Subtype.ext (map_add e x.val y.val)
  map_smul' r x := Subtype.ext (map_smul e r x.val)

end LinearEquiv

end

section

namespace LinearEquiv
universe ur um un up
variable {R : Type ur} [Ring R]
  {M : Type um} [AddCommGroup M] [Module R M]
  {N : Type un} [AddCommGroup N] [Module R N]
  {P : Type up} [AddCommGroup P] [Module R P]

@[expose] def kernelTargetEquiv (f : M →ₗ[R] N) (e : N ≃ₗ[R] P) :
    LinearMap.ker f ≃ₗ[R] LinearMap.ker (e.toLinearMap.comp f) where
  toFun x := ⟨x.val, by
    change e (f x.val)=0
    rw [LinearMap.mem_ker.mp x.property,map_zero]⟩
  invFun y := ⟨y.val, by
    apply e.injective
    simpa only [LinearMap.comp_apply,LinearEquiv.coe_coe,map_zero] using (LinearMap.mem_ker.mp y.property)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end LinearEquiv

end

section

namespace LinearEquiv
universe uk ua um un up uq
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {M : Type um} [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]
  {N : Type un} [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]
  {P : Type up} [AddCommGroup P] [Module k P] [Module A P] [IsScalarTower k A P]
  {Q : Type uq} [AddCommGroup Q] [Module k Q]

@[expose] def kernelMixedEquiv (f : M →ₗ[A] P) (e : M ≃ₗ[A] N) (g : P ≃ₗ[k] Q) :
    LinearMap.ker f ≃ₗ[k] LinearMap.ker
      (g.toLinearMap.comp ((f.comp e.symm.toLinearMap).restrictScalars k)) where
  toFun x := ⟨e x.val, by
    change g (f (e.symm (e x.val)))=0
    rw [e.symm_apply_apply,LinearMap.mem_ker.mp x.property,map_zero]⟩
  invFun y := ⟨e.symm y.val, by
    apply g.injective
    have hy : g (f (e.symm y.val))=0 := y.property
    simpa only [map_zero] using hy⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x.val)
  right_inv y := Subtype.ext (e.apply_symm_apply y.val)
  map_add' x y := Subtype.ext (map_add e x.val y.val)
  map_smul' c x := Subtype.ext (map_smul (e.restrictScalars k) c x.val)

end LinearEquiv

end

end OAI
