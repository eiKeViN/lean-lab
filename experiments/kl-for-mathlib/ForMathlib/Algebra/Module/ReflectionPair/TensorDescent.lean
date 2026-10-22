import Mathlib
import ForMathlib.Algebra.Module.ReflectionPair.TensorKernel

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

 theorem tensorFirst_map (e : Module.End A N) (m : A ⊗[C] N) :
    tensorFirst (C := C) (AlgebraTensorModule.map (LinearMap.id : A →ₗ[A] A) (e.restrictScalars C) m)=
      e (tensorFirst (C := C) m) := by
  induction m using TensorProduct.inductionOn with
  | add m n hm hn => simp only [map_add,hm,hn]
  | tmul a n => simp only [AlgebraTensorModule.map_tmul,LinearMap.id_apply,
      LinearMap.restrictScalars_apply,tensorFirst_tmul,map_smul]

 theorem tensorSecond_map (e : Module.End A N) (m : A ⊗[C] N) :
    tensorSecond τ hfix (AlgebraTensorModule.map (LinearMap.id : A →ₗ[A] A) (e.restrictScalars C) m)=
      twistMap τ e (tensorSecond τ hfix m) := by
  induction m using TensorProduct.inductionOn with
  | add m n hm hn => simp only [map_add,hm,hn]
  | tmul a n =>
    simp only [AlgebraTensorModule.map_tmul,LinearMap.id_apply,
      LinearMap.restrictScalars_apply,tensorSecond_tmul]
    apply Twist.ext
    exact (map_smul e (τ a) n).symm

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
    simp only [map_add]
    change (tensorFirst (C := C) m+tensorFirst (C := C) n)-
      ((tensorSecond τ hfix m).val+(tensorSecond τ hfix n).val)=α • (p+q)
    rw [add_sub_add_comm,hp,hq,smul_add]
  | tmul a n =>
    obtain ⟨b,hb⟩ := hdiv a
    refine ⟨b • n,?_⟩
    change a • n-τ a • n=α • (b • n)
    rw [← sub_smul,hb,mul_smul]
end
end KLInvariance.ReflectionPairTranslation
end

end OAI
