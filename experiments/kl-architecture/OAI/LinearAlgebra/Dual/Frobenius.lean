import Mathlib
import OAI.Algebra.Algebra.ReflectionFrobenius.Basis

/-! Semantic home: OAI.LinearAlgebra.Dual.Frobenius. Source spans: Frobenius:2, Frobenius:3, Frobenius:4, Frobenius:5, Frobenius:10.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.FrobeniusDuality
open Module TensorProduct
universe ur ua um
variable {R : Type ur} [CommRing R] {A : Type ua} [CommRing A] [Algebra R A]
  (tr : A →ₗ[R] R) (d : A ≃ₗ[R] Dual R A)
  (hd : ∀ a b, d a b = tr (a*b))
  (M : Type um) [AddCommGroup M] [Module A M] [Module R M] [IsScalarTower R A M]
noncomputable section

 def restrictDual : Dual A M →ₗ[R] Dual R M where
  toFun f := tr.comp (f.restrictScalars R)
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

 def fiber (f : Dual R M) (m : M) : Dual R A :=
  f.comp ((LinearMap.toSpanSingleton A M m).restrictScalars R)

@[simp] theorem fiber_apply (f : Dual R M) (m : M) (a : A) :
    fiber M f m a = f (a • m) := rfl

include hd in
 theorem trace_recover_fiber (f : Dual R M) (m : M) (a : A) :
    tr (d.symm (fiber M f m) * a) = f (a • m) := by
  rw [← hd,d.apply_symm_apply,fiber_apply]

include hd in
 theorem recover_fiber_smul (f : Dual R M) (m : M) (a : A) :
    d.symm (fiber M f (a • m)) = a * d.symm (fiber M f m) := by
  apply d.injective
  apply LinearMap.ext
  intro b
  rw [d.apply_symm_apply,hd,fiber_apply]
  have he : a * d.symm (fiber M f m) * b = d.symm (fiber M f m) * (b*a) := by ring
  rw [he,trace_recover_fiber tr d hd]
  simp only [mul_smul]

 def recoverDual (f : Dual R M) : Dual A M where
  toFun m := d.symm (fiber M f m)
  map_add' m n := by
    apply d.injective
    rw [map_add,d.apply_symm_apply,d.apply_symm_apply,d.apply_symm_apply]
    ext a
    simp [smul_add]
  map_smul' a m := by
    simpa only [RingHom.id_apply,smul_eq_mul] using recover_fiber_smul tr d hd M f m a

@[simp] theorem recoverDual_apply (f : Dual R M) (m : M) :
    recoverDual tr d hd M f m = d.symm (fiber M f m) := rfl

 theorem restrict_recover (f : Dual R M) :
    restrictDual tr M (recoverDual tr d hd M f) = f := by
  ext m
  change tr (d.symm (fiber M f m)) = f m
  simpa only [mul_one,one_smul] using trace_recover_fiber tr d hd M f m 1

 theorem recover_restrict (f : Dual A M) :
    recoverDual tr d hd M (restrictDual tr M f) = f := by
  ext m
  apply d.injective
  change d (d.symm _) = d (f m)
  rw [d.apply_symm_apply]
  ext a
  change tr (f (a • m)) = d (f m) a
  rw [map_smul,smul_eq_mul,hd,mul_comm]

 def restrictionEquiv : Dual A M ≃ₗ[R] Dual R M :=
  LinearEquiv.ofBijective (restrictDual tr M)
    ⟨fun f g h => by
      have hh := congrArg (recoverDual tr d hd M) h
      simpa only [recover_restrict] using hh,
    fun f => ⟨recoverDual tr d hd M f,restrict_recover tr d hd M f⟩⟩

 theorem restrictionEquiv_apply (f : Dual A M) (m : M) :
    restrictionEquiv tr d hd M f m = tr (f m) := rfl

/-- Restricting an integral perfect pairing along a Frobenius trace is again
integral and perfect; no localization or fraction-field argument is used. -/
 def restrictPairing (p : M ≃ₗ[A] Dual A M) : M ≃ₗ[R] Dual R M :=
  (p.restrictScalars R).trans (restrictionEquiv tr d hd M)

 theorem restrictPairing_apply (p : M ≃ₗ[A] Dual A M) (m n : M) :
    restrictPairing tr d hd M p m n = tr (p m n) := rfl

end
end KLInvariance.FrobeniusDuality
end


section
namespace KLInvariance.FrobeniusDuality
open Module TensorProduct
universe ur ua um
variable {R : Type ur} [CommRing R] (A : Type ua) [CommRing A] [Algebra R A]
  {M : Type um} [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]
noncomputable section

 def extendPairing (p : M ≃ₗ[R] Dual R M) :
    (A ⊗[R] M) ≃ₗ[A] Dual A (A ⊗[R] M) :=
  (p.baseChange R A M (Dual R M)).trans
    (TensorProduct.isBaseChange (R := R) (S := A) (M := M)).toDualBaseChange

 theorem extendPairing_tmul (p : M ≃ₗ[R] Dual R M) (a b : A) (m n : M) :
    extendPairing A p (a ⊗ₜ[R] m) (b ⊗ₜ[R] n) =
      a * b * algebraMap R A (p m n) := by
  have hn : b ⊗ₜ[R] n = b • (1 ⊗ₜ[R] n) := by simp only [smul_tmul',smul_eq_mul,mul_one]
  rw [hn,map_smul]
  change b * ((TensorProduct.isBaseChange (R := R) (S := A) (M := M)).toDualBaseChange
    (a ⊗ₜ[R] p m) ((TensorProduct.mk R A M 1) n)) = _
  rw [IsBaseChange.toDualBaseChange_tmul]
  ring

end
end KLInvariance.FrobeniusDuality
end


section
namespace KLInvariance.FrobeniusDuality
open Module TensorProduct
universe ur ua um
noncomputable section

structure PairedModule (A : Type ua) [CommRing A] where
  carrier : Type um
  [add : AddCommGroup carrier]
  [module : Module A carrier]
  free : Module.Free A carrier
  finite : Module.Finite A carrier
  pairing : carrier ≃ₗ[A] Dual A carrier

attribute [instance] PairedModule.add PairedModule.module PairedModule.free PairedModule.finite
instance _root_.OAI.KLInvariance.FrobeniusDuality.instCoeSortPairedModuleType {A : Type ua} [CommRing A] : CoeSort (PairedModule.{ua,um} A) (Type um) := ⟨PairedModule.carrier⟩

 def unitPairing (A : Type ua) [CommRing A] : A ≃ₗ[A] Dual A A where
  toFun a := LinearMap.mul A A a
  invFun f := f 1
  left_inv a := mul_one a
  right_inv f := by
    apply LinearMap.ext
    intro a
    change f 1 * a = f a
    rw [mul_comm,← smul_eq_mul,← map_smul,smul_eq_mul,mul_one]
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

 def unitModule (A : Type ua) [CommRing A] : PairedModule A where
  carrier := A
  free := inferInstance
  finite := inferInstance
  pairing := unitPairing A

variable {R : Type ur} [CommRing R] {A : Type ua} [CommRing A] [Algebra R A]
  [Module.Free R A] [Module.Finite R A]
  (tr : A →ₗ[R] R) (d : A ≃ₗ[R] Dual R A) (hd : ∀ a b, d a b = tr (a*b))
  (N : PairedModule.{ua,um} A)

local instance restrictedModule : Module R N := Module.compHom N (algebraMap R A)
local instance restrictedTower : IsScalarTower R A N := IsScalarTower.of_algebraMap_smul fun _ _ => rfl

 def restrictionBasis : Basis
    (Module.Free.ChooseBasisIndex R A × Module.Free.ChooseBasisIndex A N) R N :=
  (Module.Free.chooseBasis R A).smulTower (Module.Free.chooseBasis A N)

local instance restrictedFree : Module.Free R N := Module.Free.of_basis (restrictionBasis N)
local instance restrictedFinite : Module.Finite R N := Module.Finite.trans A N

 def inducedModule : PairedModule A where
  carrier := A ⊗[R] N
  free := inferInstance
  finite := inferInstance
  pairing := extendPairing A (restrictPairing tr d hd N N.pairing)

 theorem inducedModule_pairing_tmul (a b : A) (m n : N) :
    (inducedModule tr d hd N).pairing (a ⊗ₜ[R] m) (b ⊗ₜ[R] n) =
      a*b*algebraMap R A (tr (N.pairing m n)) :=
  extendPairing_tmul A _ a b m n

end
end KLInvariance.FrobeniusDuality
end


section
namespace KLInvariance.FrobeniusDuality
open Module TensorProduct
universe ur ua um
noncomputable section

structure PairedBimodule (A : Type ua) [CommRing A] where
  obj : PairedModule.{ua,um} A
  right : A →+* End A obj
  balanced : ∀ a m n, obj.pairing (right a m) n = obj.pairing m (right a n)
  symmetric : ∀ m n, obj.pairing m n = obj.pairing n m

 def unitBimodule (A : Type ua) [CommRing A] : PairedBimodule A where
  obj := unitModule A
  right := Algebra.lmul A A |>.toRingHom
  balanced a m n := by
    change A at m n
    change (a*m)*n = m*(a*n)
    ring
  symmetric m n := by
    change A at m n
    exact mul_comm m n

variable {R : Type ur} [CommRing R] {A : Type ua} [CommRing A] [Algebra R A]
  [Module.Free R A] [Module.Finite R A]
  (tr : A →ₗ[R] R) (d : A ≃ₗ[R] Dual R A) (hd : ∀ a b, d a b = tr (a*b))
  (N : PairedModule.{ua,um} A)

attribute [local instance] restrictedModule restrictedTower restrictedFree restrictedFinite

 def restrictedRight (right : A →+* End A N) : A →+* End R N where
  toFun a := (right a).restrictScalars R
  map_one' := by ext m; change (right 1) m = m; rw [map_one]; rfl
  map_mul' a b := by
    ext m
    change (right (a*b)) m = (right a) ((right b) m)
    rw [map_mul]
    rfl
  map_zero' := by ext m; change (right 0) m = 0; rw [map_zero]; rfl
  map_add' a b := by ext m; change (right (a+b)) m = (right a) m + (right b) m; rw [map_add]; rfl

 def inducedRight (right : A →+* End A N) : A →+* End A (inducedModule tr d hd N) :=
  (Module.End.baseChangeHom R A N).toRingHom.comp (restrictedRight N right)

@[simp] theorem inducedRight_tmul (right : A →+* End A N) (r a : A) (m : N) :
    inducedRight tr d hd N right r (a ⊗ₜ[R] m) = a ⊗ₜ[R] right r m := rfl

 theorem inducedPairing_balanced (right : A →+* End A N)
    (hb : ∀ a m n, N.pairing (right a m) n = N.pairing m (right a n))
    (r : A) (m n : inducedModule tr d hd N) :
    (inducedModule tr d hd N).pairing (inducedRight tr d hd N right r m) n =
      (inducedModule tr d hd N).pairing m (inducedRight tr d hd N right r n) := by
  change A ⊗[R] N at m n
  change extendPairing A (restrictPairing tr d hd N N.pairing)
    (((right r).restrictScalars R).baseChange A m) n =
    extendPairing A (restrictPairing tr d hd N N.pairing) m
    (((right r).restrictScalars R).baseChange A n)
  induction m using TensorProduct.inductionOn with
  | add m₁ m₂ h₁ h₂ => simp only [map_add,LinearMap.add_apply,h₁,h₂]
  | tmul a m =>
    induction n using TensorProduct.inductionOn with
    | add n₁ n₂ h₁ h₂ => simp only [map_add,h₁,h₂]
    | tmul b n =>
      simp only [LinearMap.baseChange_tmul,extendPairing_tmul,restrictPairing_apply,
        LinearMap.restrictScalars_apply,hb]

 theorem inducedPairing_symmetric (hs : ∀ m n, N.pairing m n = N.pairing n m)
    (m n : inducedModule tr d hd N) :
    (inducedModule tr d hd N).pairing m n = (inducedModule tr d hd N).pairing n m := by
  change A ⊗[R] N at m n
  change extendPairing A (restrictPairing tr d hd N N.pairing) m n =
    extendPairing A (restrictPairing tr d hd N N.pairing) n m
  induction m using TensorProduct.inductionOn with
  | add m₁ m₂ h₁ h₂ => simp only [map_add,LinearMap.add_apply,h₁,h₂]
  | tmul a m =>
    induction n using TensorProduct.inductionOn with
    | add n₁ n₂ h₁ h₂ => simp only [map_add,LinearMap.add_apply,h₁,h₂]
    | tmul b n =>
      rw [extendPairing_tmul,extendPairing_tmul,restrictPairing_apply,restrictPairing_apply,hs,mul_comm a b]

 def inducedBimodule (N : PairedBimodule.{ua,um} A) : PairedBimodule A where
  obj := inducedModule tr d hd N.obj
  right := inducedRight tr d hd N.obj N.right
  balanced := inducedPairing_balanced tr d hd N.obj N.right N.balanced
  symmetric := inducedPairing_symmetric tr d hd N.obj N.symmetric

end
end KLInvariance.FrobeniusDuality
end


section
namespace KLInvariance.FrobeniusDuality
open Module TensorProduct ReflectionFrobenius
universe uk ua um ui
variable {k : Type uk} [Field k] [CharZero k]
  {A : Type ua} [CommRing A] [IsDomain A] [Algebra k A]
  (τ : A ≃ₐ[k] A) (α : A) (hinv : Function.Involutive τ) (hα : α ≠ 0)
  (hanti : τ α = -α) (hdiv : ∀ a : A, α ∣ a-τ a)
noncomputable section

variable [Module.Free (fixed τ) A] [Module.Finite (fixed τ) A]

variable (N : PairedModule.{ua,um} A)
  {ι : Type ui} (b : Basis ι A N)
attribute [local instance] restrictedModule restrictedTower restrictedFree restrictedFinite

 def inducedBasis : Basis (Fin 2 × ι) A
    (inducedModule (trace τ α hinv hα hanti hdiv)
      (duality τ α hinv hα hanti hdiv) (duality_apply τ α hinv hα hanti hdiv) N) :=
  ((reflectionBasis τ α hinv hα hanti hdiv).smulTower b).baseChange A

 theorem inducedBasis_apply (i : Fin 2) (j : ι) :
    inducedBasis τ α hinv hα hanti hdiv N b (i,j) =
      (1:A) ⊗ₜ[fixed τ] (reflectionBasis τ α hinv hα hanti hdiv i • b j) := by
  change (((reflectionBasis τ α hinv hα hanti hdiv).smulTower b).baseChange A) (i,j) = _
  rw [Basis.baseChange_apply,Basis.smulTower_apply]

 theorem inducedPairing_basis (i i' : Fin 2) (j j' : ι) :
    (inducedModule (trace τ α hinv hα hanti hdiv)
      (duality τ α hinv hα hanti hdiv) (duality_apply τ α hinv hα hanti hdiv) N).pairing
      (inducedBasis τ α hinv hα hanti hdiv N b (i,j))
      (inducedBasis τ α hinv hα hanti hdiv N b (i',j')) =
      (trace τ α hinv hα hanti hdiv
        (reflectionBasis τ α hinv hα hanti hdiv i *
          reflectionBasis τ α hinv hα hanti hdiv i' * N.pairing (b j) (b j')) : A) := by
  rw [inducedBasis_apply,inducedBasis_apply]
  let : Module.Free (fixed τ) N := Module.Free.of_basis
    ((reflectionBasis τ α hinv hα hanti hdiv).smulTower b)
  let : Module.Finite (fixed τ) N := Module.Finite.trans A N
  change extendPairing A (restrictPairing (trace τ α hinv hα hanti hdiv)
    (duality τ α hinv hα hanti hdiv) (duality_apply τ α hinv hα hanti hdiv) N N.pairing) _ _ = _
  rw [extendPairing_tmul,restrictPairing_apply]
  simp only [one_mul]
  change ((trace τ α hinv hα hanti hdiv _) : A) = _
  apply congrArg Subtype.val
  apply congrArg (trace τ α hinv hα hanti hdiv)
  simp only [map_smul,LinearMap.smul_apply,smul_eq_mul]
  ring

 theorem inducedPairing_basis_homogeneous (𝓐 : ℤ → Submodule k A)
    [DirectSum.Decomposition 𝓐] [SetLike.GradedMonoid 𝓐]
    (hroot : α ∈ 𝓐 1) (hτ : ∀ n a, a ∈ 𝓐 n → τ a ∈ 𝓐 n)
    (d : ι → ℤ) (l : ℤ)
    (hb : ∀ j j', N.pairing (b j) (b j') ∈ 𝓐 (d j+d j'-l))
    (i i' : Fin 2) (j j' : ι) :
    (inducedModule (trace τ α hinv hα hanti hdiv)
      (duality τ α hinv hα hanti hdiv) (duality_apply τ α hinv hα hanti hdiv) N).pairing
      (inducedBasis τ α hinv hα hanti hdiv N b (i,j))
      (inducedBasis τ α hinv hα hanti hdiv N b (i',j')) ∈
      𝓐 ((i.val+d j)+(i'.val+d j')-(l+1)) := by
  rw [inducedPairing_basis]
  have h := trace_homogeneous τ α hinv hα hanti hdiv 𝓐 hroot hτ
    (SetLike.GradedMul.mul_mem
      (SetLike.GradedMul.mul_mem
        (reflectionBasis_homogeneous τ α hinv hα hanti hdiv 𝓐 hroot i)
        (reflectionBasis_homogeneous τ α hinv hα hanti hdiv 𝓐 hroot i'))
      (hb j j'))
  convert h using 1
  congr 1
  omega

end
end KLInvariance.FrobeniusDuality
end

end OAI
