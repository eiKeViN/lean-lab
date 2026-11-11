import QEC.Coding.HypergraphProduct.Dimension.Formula
import Mathlib.LinearAlgebra.TensorProduct.Prod

noncomputable section
namespace HGPExperiment
open TensorProduct
open QEC.Coding.HypergraphProduct

variable {F : Type*} [Field F]
variable {A A' A'' B B' : Type*}
  [AddCommGroup A] [Module F A] [Module.Finite F A]
  [AddCommGroup A'] [Module F A'] [Module.Finite F A']
  [AddCommGroup A''] [Module F A''] [Module.Finite F A'']
  [AddCommGroup B] [Module F B] [Module.Finite F B]
  [AddCommGroup B'] [Module F B'] [Module.Finite F B']

private theorem finrank_submodule_map (U : Submodule F A) (f : A →ₗ[F] A') :
    Module.finrank F (U.map f) + Module.finrank F (U ⊓ f.ker) =
      Module.finrank F U := by
  have h := (f.comp U.subtype).finrank_range_add_finrank_ker
  have hr : LinearMap.range (f.comp U.subtype) = U.map f := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  have hk : (LinearMap.ker (f.comp U.subtype)).map U.subtype = U ⊓ f.ker := by
    ext v
    simp only [Submodule.mem_map, LinearMap.mem_ker, LinearMap.comp_apply,
      Submodule.mem_inf]
    constructor
    · rintro ⟨u, hu, rfl⟩; exact ⟨u.property, hu⟩
    · rintro ⟨hu, hv⟩; exact ⟨⟨v, hu⟩, hv, rfl⟩
  rw [hr] at h
  rw [← hk, Submodule.finrank_map_subtype_eq]
  exact h

/-- The dimension of the image of a tensor product map. -/
theorem finrank_range_tensorMap (f : A →ₗ[F] A') (g : B →ₗ[F] B') :
    Module.finrank F (LinearMap.range (TensorProduct.map f g)) =
      Module.finrank F f.range * Module.finrank F g.range := by
  have he : TensorProduct.map f g =
      (TensorProduct.map f.range.subtype g.range.subtype).comp
        (TensorProduct.map f.rangeRestrict g.rangeRestrict) := by
    ext x y
    rfl
  rw [he, LinearMap.range_comp,
    LinearMap.range_eq_top.mpr (TensorProduct.map_surjective
      f.surjective_rangeRestrict g.surjective_rangeRestrict), Submodule.map_top,
    LinearMap.finrank_range_of_inj
      (TensorProduct.map_injective_of_flat_flat _ _
        f.range.injective_subtype g.range.injective_subtype)]
  exact Module.finrank_tensorProduct

/-- Tensoring preserves the intersection of kernels in one factor. -/
theorem tensor_sameFactor_ker (f : A →ₗ[F] A') (p : A →ₗ[F] A'') :
    (f.rTensor B).ker ⊓ (p.rTensor B).ker =
      LinearMap.range (((f.ker ⊓ p.ker).subtype).rTensor B) := by
  have he : ((f.rTensor B).prod (p.rTensor B)) =
      (TensorProduct.prodLeft F F A' A'' B).toLinearMap.comp
        ((f.prod p).rTensor B) := by
    ext a b <;> simp
  rw [← LinearMap.ker_prod, he, LinearEquiv.ker_comp]
  simpa only [LinearMap.ker_prod] using
    (Module.Flat.rTensor_exact B (f.prod p).exact_subtype_ker_map).linearMap_ker_eq

theorem finrank_tensor_sameFactor_ker (f : A →ₗ[F] A') (p : A →ₗ[F] A'') :
    Module.finrank F ((f.rTensor B).ker ⊓ (p.rTensor B).ker) =
      Module.finrank F (f.ker ⊓ p.ker) * Module.finrank F B := by
  rw [tensor_sameFactor_ker, LinearMap.finrank_range_of_inj
    (Module.Flat.rTensor_preserves_injective_linearMap _
      (f.ker ⊓ p.ker).injective_subtype)]
  exact Module.finrank_tensorProduct

/-- First-block boundaries: imposing zero on the second block forces the
first tensor factor to be a cycle. -/
theorem firstBoundary_range (f : A →ₗ[F] A') (g : B' →ₗ[F] B) :
    ((LinearMap.range ((g.lTensor A).prod (f.rTensor B'))).comap
      (LinearMap.inl F (A ⊗[F] B) (A' ⊗[F] B'))) =
      LinearMap.range (TensorProduct.map f.ker.subtype g) := by
  ext x
  constructor
  · rintro ⟨t, ht⟩
    have ht0 : f.rTensor B' t = 0 := congrArg Prod.snd ht
    have hk := (Module.Flat.rTensor_exact B' f.exact_subtype_ker_map).linearMap_ker_eq
    obtain ⟨s, hs⟩ := show t ∈ LinearMap.range (f.ker.subtype.rTensor B') from
      hk ▸ ht0
    refine ⟨s, ?_⟩
    have hcomp : (g.lTensor A).comp (f.ker.subtype.rTensor B') =
        TensorProduct.map f.ker.subtype g := by ext a b; rfl
    exact (DFunLike.congr_fun hcomp s).symm.trans
      ((congrArg (g.lTensor A) hs).trans (congrArg Prod.fst ht))
  · rintro ⟨s, rfl⟩
    refine ⟨f.ker.subtype.rTensor B' s, ?_⟩
    apply Prod.ext
    · change (g.lTensor A) (f.ker.subtype.rTensor B' s) = _
      have hcomp : (g.lTensor A).comp (f.ker.subtype.rTensor B') =
          TensorProduct.map f.ker.subtype g := by ext a b; rfl
      exact DFunLike.congr_fun hcomp s
    · change f.rTensor B' (f.ker.subtype.rTensor B' s) = 0
      have hcomp : (f.rTensor B').comp (f.ker.subtype.rTensor B') = 0 := by
        rw [← LinearMap.rTensor_comp]
        simp
      exact DFunLike.congr_fun hcomp s

/-- Restricting the image of a tensor map in its first coordinate multiplies
its surviving first-factor dimension by the rank in the second factor. -/
theorem finrank_tensorImage_inf_ker (f : A →ₗ[F] A') (g : B →ₗ[F] B')
    (p : A' →ₗ[F] A'') :
    Module.finrank F ((TensorProduct.map f g).range ⊓ (p.rTensor B').ker) =
      Module.finrank F (f.range ⊓ p.ker) * Module.finrank F g.range := by
  have he : ((TensorProduct.map f g).range).map (p.rTensor B') =
      (TensorProduct.map (p.comp f) g).range := by
    rw [← LinearMap.range_comp]
    congr 1
    ext a b
    rfl
  have he' : f.range.map p = (p.comp f).range := by
    rw [LinearMap.range_comp]
  have h := finrank_submodule_map (TensorProduct.map f g).range (p.rTensor B')
  have h' := finrank_submodule_map f.range p
  rw [he, finrank_range_tensorMap, finrank_range_tensorMap] at h
  rw [he'] at h'
  nlinarith

end HGPExperiment
