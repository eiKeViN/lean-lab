module
public import Mathlib
public import ForMathlib.Algebra.Module.ReflectionPair.TensorKernel

public section

/-! Semantic home: ForMathlib.Algebra.Module.ReflectionPair.TensorDescent. Source spans: IntegralPairings:8, IntegralPairings:11.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.ReflectionPairTranslation
open TensorProduct
universe uc ua un
variable {C : Type uc} [CommRing C] {A : Type ua} [CommRing A] [Algebra C A]
  {N : Type un} [AddCommGroup N] [Module A N] [Module C N] [IsScalarTower C A N]
  (τ : A ≃+* A) (hfix : ∀ c : C, τ (algebraMap C A c)=algebraMap C A c)
noncomputable section

/-- Tensor multiplication is natural for arbitrary A-linear maps, not only endomorphisms. -/
theorem tensorFirst_natural {P : Type*} [AddCommGroup P] [Module A P]
    [Module C P] [IsScalarTower C A P] (f : N →ₗ[A] P) (m : A ⊗[C] N) :
    tensorFirst (C := C) (AlgebraTensorModule.map (LinearMap.id : A →ₗ[A] A) (f.restrictScalars C) m) =
      f (tensorFirst (C := C) m) := by
  induction m using TensorProduct.inductionOn with
  | add m n hm hn => simp only [map_add,hm,hn]
  | tmul a n => simp only [AlgebraTensorModule.map_tmul,LinearMap.id_apply,
      LinearMap.restrictScalars_apply,tensorFirst_tmul,map_smul]

/-- The reflected tensor projection is natural with the induced map on twists. -/
theorem tensorSecond_natural {P : Type*} [AddCommGroup P] [Module A P]
    [Module C P] [IsScalarTower C A P] (f : N →ₗ[A] P) (m : A ⊗[C] N) :
    tensorSecond τ hfix (AlgebraTensorModule.map (LinearMap.id : A →ₗ[A] A) (f.restrictScalars C) m) =
      twistMap τ f (tensorSecond τ hfix m) := by
  induction m using TensorProduct.inductionOn with
  | add m n hm hn => simp only [map_add,hm,hn]
  | tmul a n =>
    apply Twist.ext
    simp only [AlgebraTensorModule.map_tmul,LinearMap.id_apply,
      LinearMap.restrictScalars_apply,tensorSecond_tmul,twistMap_val]
    exact (map_smul f (τ a) n).symm

 theorem tensorFirst_map (e : Module.End A N) (m : A ⊗[C] N) :
    tensorFirst (C := C) (AlgebraTensorModule.map (LinearMap.id : A →ₗ[A] A) (e.restrictScalars C) m)=
      e (tensorFirst (C := C) m) := by
  exact tensorFirst_natural e m

 theorem tensorSecond_map (e : Module.End A N) (m : A ⊗[C] N) :
    tensorSecond τ hfix (AlgebraTensorModule.map (LinearMap.id : A →ₗ[A] A) (e.restrictScalars C) m)=
      twistMap τ e (tensorSecond τ hfix m) := by
  exact tensorSecond_natural τ hfix e m

end
end KLInvariance.ReflectionPairTranslation
end


section
namespace KLInvariance.ReflectionPairTranslation
open TensorProduct
universe uc ua un
variable {C : Type uc} [CommRing C] {A : Type ua} [CommRing A] [Algebra C A]
  {N : Type un} [AddCommGroup N] [Module A N] [Module C N] [IsScalarTower C A N]
  (τ : A ≃+* A) (hfix : ∀ c : C, τ (algebraMap C A c)=algebraMap C A c)
noncomputable section
 theorem tensor_difference (α : A) (hdiv : ∀ a : A, α ∣ a-τ a)
    (m : A ⊗[C] N) :
    ∃ n : N, tensorFirst (C := C) m-(tensorSecond τ hfix m).val=α • n := by
  induction m using TensorProduct.inductionOn with
  | add m n hm hn =>
    obtain ⟨p,hp⟩ := hm
    obtain ⟨q,hq⟩ := hn
    refine ⟨p+q,?_⟩
    simp only [map_add,Twist.val_add]
    rw [add_sub_add_comm,hp,hq,smul_add]
  | tmul a n =>
    obtain ⟨b,hb⟩ := hdiv a
    refine ⟨b • n,?_⟩
    rw [tensorFirst_tmul,tensorSecond_tmul]
    rw [← sub_smul,hb,mul_smul]
end
end KLInvariance.ReflectionPairTranslation
end

end OAI
