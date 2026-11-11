import HGPExperiment.Parameters
import HGPExperiment.Erasure
import QEC.Coding.HypergraphProduct.Dimension.Formula

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

noncomputable section
open scoped Classical
open TensorProduct QEC.Coding QEC.Coding.HypergraphProduct
namespace HGPExperiment
open TensorProduct QEC.Coding QEC.Coding.HypergraphProduct

section Algebra
variable {F M M' N N' U : Type*} [Field F]
  [AddCommGroup M] [Module F M] [Module.Finite F M]
  [AddCommGroup M'] [Module F M'] [Module.Finite F M']
  [AddCommGroup N] [Module F N] [Module.Finite F N]
  [AddCommGroup N'] [Module F N'] [Module.Finite F N']
  [AddCommGroup U] [Module F U] [Module.Finite F U]

/-- Restricting a map to an injectively parametrized subspace computes its intersection kernel. -/
theorem map_ker_comp_eq (e : M →ₗ[F] N) (h : N →ₗ[F] U) :
    (LinearMap.ker (h.comp e)).map e = LinearMap.range e ⊓ LinearMap.ker h := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨y, rfl⟩, hy⟩
  · rintro ⟨⟨y, rfl⟩, hy⟩
    exact ⟨y, hy, rfl⟩

theorem finrank_map_of_injective (e : M →ₗ[F] N) (he : Function.Injective e)
    (A : Submodule F M) : Module.finrank F (A.map e) = Module.finrank F A := by
  exact LinearEquiv.finrank_eq (A.equivMapOfInjective e he).symm

theorem strip_finrank_map_add (A : Submodule F M) (e : M →ₗ[F] N) :
    Module.finrank F (A.map e) + Module.finrank F ↥(A ⊓ LinearMap.ker e) =
      Module.finrank F A := by
  exact finrank_map_add_finrank_inf_ker A e

/-- Rank of a tensor product, proved by corestricting both factors to their ranges. -/
theorem finrank_range_tensorMap (f : M →ₗ[F] M') (g : N →ₗ[F] N') :
    Module.finrank F (LinearMap.range (TensorProduct.map f g)) =
      Module.finrank F (LinearMap.range f) * Module.finrank F (LinearMap.range g) := by
  let i := TensorProduct.map (LinearMap.range f).subtype (LinearMap.range g).subtype
  let s := TensorProduct.map f.rangeRestrict g.rangeRestrict
  have hi : Function.Injective i :=
    TensorProduct.map_injective_of_flat_flat _ _ (LinearMap.range f).injective_subtype
      (LinearMap.range g).injective_subtype
  have hs : Function.Surjective s :=
    TensorProduct.map_surjective f.surjective_rangeRestrict g.surjective_rangeRestrict
  have hfactor : TensorProduct.map f g = i.comp s := by
    ext x y
    rfl
  rw [hfactor, LinearMap.range_comp, LinearMap.range_eq_top.mpr hs, Submodule.map_top,
    LinearMap.finrank_range_of_inj hi, Module.finrank_tensorProduct]

/-- A mixed tensor constraint: the first map vanishes everywhere, while the second
constraint is tested only through a map in the other tensor factor. -/
theorem finrank_ker_mixed_tensor (f : M →ₗ[F] M') (r : M →ₗ[F] U)
    (g : N →ₗ[F] N') :
    Module.finrank F (LinearMap.ker ((f.rTensor N).prod (TensorProduct.map r g))) =
      Module.finrank F (LinearMap.ker f) * Module.finrank F (LinearMap.ker g) +
      Module.finrank F (LinearMap.ker (f.prod r)) * Module.finrank F (LinearMap.range g) := by
  let e := (LinearMap.ker f).subtype.rTensor N
  have he : Function.Injective e :=
    Module.Flat.rTensor_preserves_injective_linearMap _ (LinearMap.ker f).injective_subtype
  have hre : LinearMap.range e = LinearMap.ker (f.rTensor N) :=
    (Module.Flat.rTensor_exact N f.exact_subtype_ker_map).linearMap_ker_eq.symm
  let t := r.comp (LinearMap.ker f).subtype
  have hcomp : (TensorProduct.map r g).comp e = TensorProduct.map t g := by
    ext x y
    rfl
  have hker : Module.finrank F
      (LinearMap.ker ((f.rTensor N).prod (TensorProduct.map r g))) =
      Module.finrank F (LinearMap.ker (TensorProduct.map t g)) := by
    rw [LinearMap.ker_prod, ← hre, ← map_ker_comp_eq, hcomp]
    exact finrank_map_of_injective e he _
  have ht : Module.finrank F (LinearMap.ker t) =
      Module.finrank F (LinearMap.ker (f.prod r)) := by
    have hh := map_ker_comp_eq (LinearMap.ker f).subtype r
    rw [Submodule.range_subtype, ← LinearMap.ker_prod] at hh
    rw [← hh]
    exact (finrank_map_of_injective _ (LinearMap.ker f).injective_subtype _).symm
  have h1 := (TensorProduct.map t g).finrank_range_add_finrank_ker
  rw [finrank_range_tensorMap, Module.finrank_tensorProduct] at h1
  have h2 := t.finrank_range_add_finrank_ker
  have h3 := g.finrank_range_add_finrank_ker
  rw [ht] at h2
  rw [hker]
  nlinarith

/-- Dimension of boundaries supported in the kernel of a projection. -/
theorem finrank_range_inf_ker (b : M →ₗ[F] N) (p : N →ₗ[F] U) :
    Module.finrank F ↥(LinearMap.range b ⊓ LinearMap.ker p) +
      Module.finrank F (LinearMap.ker b) =
      Module.finrank F (LinearMap.ker (p.comp b)) := by
  have h := strip_finrank_map_add (LinearMap.ker (p.comp b)) b
  rw [map_ker_comp_eq] at h
  have hle : LinearMap.ker b ≤ LinearMap.ker (p.comp b) := by
    intro x hx
    simp only [LinearMap.mem_ker, LinearMap.comp_apply] at *
    rw [hx, map_zero]
  rwa [inf_eq_right.mpr hle] at h

end Algebra
end HGPExperiment

namespace HGPExperiment
section StripCoordinates
universe u
variable {R₁ C₁ R₂ C₂ : Type u}
  [Fintype R₁] [DecidableEq R₁] [Fintype C₁] [DecidableEq C₁]
  [Fintype R₂] [DecidableEq R₂] [Fintype C₂] [DecidableEq C₂]

/-- The whole physical variable-variable strip, containing no check-check qubits. -/
def wholeStrip (S : Set C₁) : Set (QubitIndex R₁ C₁ R₂ C₂) :=
  {q | ∃ i j, i ∈ S ∧ q = Sum.inl (i,j)}

@[simp] theorem inl_mem_wholeStrip (S : Set C₁) (i : C₁) (j : C₂) :
    Sum.inl (i,j) ∈ wholeStrip (R₁ := R₁) (R₂ := R₂) S ↔ i ∈ S := by
  simp [wholeStrip]
@[simp] theorem inr_not_mem_wholeStrip (S : Set C₁) (i : R₁) (j : R₂) :
    Sum.inr (i,j) ∉ wholeStrip (C₂ := C₂) S := by
  simp [wholeStrip]

/-- Embed an array on the strip by extending it by zero. -/
def stripEmbed (S : Set C₁) : (S × C₂ → ZMod 2) →ₗ[ZMod 2]
    (QubitIndex R₁ C₁ R₂ C₂ → ZMod 2) where
  toFun v q := match q with
    | .inl (i,j) => if h : i ∈ S then v (⟨i,h⟩,j) else 0
    | .inr _ => 0
  map_add' := by intro x y; funext q; cases q with
    | inl q => rcases q with ⟨i,j⟩; by_cases h : i ∈ S <;> simp [h]
    | inr q => rfl
  map_smul' := by intro a x; funext q; cases q with
    | inl q => rcases q with ⟨i,j⟩; by_cases h : i ∈ S <;> simp [h]
    | inr q => simp

@[simp] theorem stripEmbed_inl (S : Set C₁) (v : S × C₂ → ZMod 2)
    (i : S) (j : C₂) : stripEmbed (R₁ := R₁) (R₂ := R₂) S v (.inl (i,j)) = v (i,j) := by
  simp [stripEmbed, i.property]

 theorem stripEmbed_injective (S : Set C₁) :
    Function.Injective (stripEmbed (R₁ := R₁) (R₂ := R₂) (C₂ := C₂) S) := by
  intro v w h
  funext ⟨i,j⟩
  simpa using congrFun h (.inl (i,j))

 theorem range_stripEmbed (S : Set C₁) :
    LinearMap.range (stripEmbed (R₁ := R₁) (R₂ := R₂) (C₂ := C₂) S) =
      coordinateSpace (wholeStrip S) := by
  ext v
  constructor
  · rintro ⟨w,rfl⟩ q hq
    cases q with
    | inl q => rcases q with ⟨i,j⟩; simp only [inl_mem_wholeStrip] at hq; simp [stripEmbed,hq]
    | inr q => rfl
  · intro hv
    refine ⟨fun q => v (.inl (q.1,q.2)), ?_⟩
    funext q
    cases q with
    | inl q =>
      rcases q with ⟨i,j⟩
      by_cases hi : i ∈ S
      · simp [stripEmbed,hi]
      · simp only [stripEmbed, LinearMap.coe_mk, AddHom.coe_mk, dif_neg hi]
        exact (hv _ (by simpa using hi)).symm
    | inr q => exact (hv _ (by simp [wholeStrip])).symm

/-- Projection to the complete complement of a whole strip. -/
def stripOutside (S : Set C₁) :
    (QubitIndex R₁ C₁ R₂ C₂ → ZMod 2) →ₗ[ZMod 2]
      ((↥(Sᶜ) × C₂ → ZMod 2) × (R₁ × R₂ → ZMod 2)) where
  toFun v := (fun q => v (.inl (q.1,q.2)), fun q => v (.inr q))
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

theorem ker_stripOutside (S : Set C₁) :
    LinearMap.ker (stripOutside (R₁ := R₁) (R₂ := R₂) (C₂ := C₂) S) =
      coordinateSpace (wholeStrip S) := by
  ext v
  simp only [LinearMap.mem_ker, stripOutside, LinearMap.coe_mk, AddHom.coe_mk,
    Prod.mk_eq_zero, funext_iff, Pi.zero_apply, mem_coordinateSpace]
  constructor
  · rintro ⟨h1,h2⟩ q hq
    cases q with
    | inl q => rcases q with ⟨i,j⟩; exact h1 (⟨i,by simpa using hq⟩,j)
    | inr q => exact h2 q
  · intro h
    refine ⟨?_, fun q => h _ (by simp [wholeStrip])⟩
    intro q
    apply h
    intro hmem
    exact q.1.property ((inl_mem_wholeStrip S _ _).mp hmem)

end StripCoordinates
end HGPExperiment

namespace HGPExperiment
section TensorKernels
variable {F M M' N : Type*} [Field F]
  [AddCommGroup M] [Module F M] [Module.Finite F M]
  [AddCommGroup M'] [Module F M'] [Module.Finite F M']
  [AddCommGroup N] [Module F N] [Module.Finite F N]

theorem strip_finrank_ker_rTensor (f : M →ₗ[F] M') :
    Module.finrank F (LinearMap.ker (f.rTensor N)) =
      Module.finrank F (LinearMap.ker f) * Module.finrank F N := by
  rw [(Module.Flat.rTensor_exact N f.exact_subtype_ker_map).linearMap_ker_eq,
    LinearMap.finrank_range_of_inj
      (Module.Flat.rTensor_preserves_injective_linearMap _ (LinearMap.ker f).injective_subtype),
    Module.finrank_tensorProduct]

theorem strip_finrank_ker_lTensor (f : M →ₗ[F] M') :
    Module.finrank F (LinearMap.ker (f.lTensor N)) =
      Module.finrank F N * Module.finrank F (LinearMap.ker f) := by
  rw [(Module.Flat.lTensor_exact N f.exact_subtype_ker_map).linearMap_ker_eq,
    LinearMap.finrank_range_of_inj
      (Module.Flat.lTensor_preserves_injective_linearMap _ (LinearMap.ker f).injective_subtype),
    Module.finrank_tensorProduct]
end TensorKernels
end HGPExperiment

namespace HGPExperiment
section CoordinateTensor
universe u
variable {R₁ C₁ R₂ C₂ : Type u}
  [Fintype R₁] [DecidableEq R₁] [Fintype C₁] [DecidableEq C₁]
  [Fintype R₂] [DecidableEq R₂] [Fintype C₂] [DecidableEq C₂]

/-- Zero extension from a set of first-input coordinates. -/
def stripExtend (S : Set C₁) : (S → ZMod 2) →ₗ[ZMod 2] (C₁ → ZMod 2) :=
  (coordinateSpace S).subtype.comp (coordinateEquiv S).symm.toLinearMap

@[simp] theorem stripExtend_apply (S : Set C₁) (v : S → ZMod 2) (i : C₁) :
    stripExtend S v i = if h : i ∈ S then v ⟨i,h⟩ else 0 := rfl

theorem mulVec_stripExtend {R : Type u} (H : Matrix R C₁ (ZMod 2))
    (S : Set C₁) (v : S → ZMod 2) :
    H.mulVecLin (stripExtend S v) = (restrictColumns H S).mulVecLin v := by
  classical
  funext r
  simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, stripExtend_apply,
    restrictColumns, Matrix.submatrix_apply, id_eq]
  apply Finset.sum_congr_set S
  · intro i hi
    simp [hi]
  · intro i hi
    simp [hi]

/-- Tensor coordinates for the injection into the whole physical strip. -/
def stripTensorEmbed (S : Set C₁) :
    ((S → ZMod 2) ⊗[ZMod 2] (C₂ → ZMod 2)) →ₗ[ZMod 2]
      (QubitIndex R₁ C₁ R₂ C₂ → ZMod 2) :=
  (stripEmbed S).comp (wordTensorEquiv (ZMod 2) S C₂).toLinearMap

@[simp] theorem stripTensorEmbed_tmul (S : Set C₁) (v : S → ZMod 2)
    (w : C₂ → ZMod 2) (i : C₁) (j : C₂) :
    stripTensorEmbed (R₁ := R₁) (R₂ := R₂) S (v ⊗ₜ[ZMod 2] w) (.inl (i,j)) =
      stripExtend S v i * w j := by
  classical
  by_cases hi : i ∈ S <;> simp [stripTensorEmbed,stripEmbed,stripExtend_apply,hi]

@[simp] theorem stripTensorEmbed_tmul_check (S : Set C₁) (v : S → ZMod 2)
    (w : C₂ → ZMod 2) (q : R₁ × R₂) :
    stripTensorEmbed (C₂ := C₂) S (v ⊗ₜ[ZMod 2] w) (.inr q) = 0 := rfl

theorem stripTensorEmbed_injective (S : Set C₁) :
    Function.Injective (stripTensorEmbed (R₁ := R₁) (R₂ := R₂) (C₂ := C₂) S) :=
  (stripEmbed_injective S).comp (wordTensorEquiv (ZMod 2) S C₂).injective

end CoordinateTensor
end HGPExperiment
