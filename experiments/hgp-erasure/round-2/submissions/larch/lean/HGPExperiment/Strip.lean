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

theorem range_stripTensorEmbed (S : Set C₁) :
    LinearMap.range (stripTensorEmbed (R₁ := R₁) (R₂ := R₂) (C₂ := C₂) S) =
      coordinateSpace (wholeStrip S) := by
  rw [stripTensorEmbed, LinearMap.range_comp, LinearEquiv.range,
    Submodule.map_top, range_stripEmbed]

 theorem xChecks_stripTensorEmbed (H : Data (ZMod 2) R₁ C₁ R₂ C₂) (S : Set C₁) :
    (xChecks H).mulVecLin.comp (stripTensorEmbed S) =
      (wordTensorEquiv (ZMod 2) R₁ C₂).toLinearMap.comp
        ((restrictColumns H.first S).mulVecLin.rTensor (C₂ → ZMod 2)) := by
  classical
  apply TensorProduct.ext'
  intro v w
  funext ⟨r,j⟩
  change (xChecks H).mulVec _ _ = _
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fintype.sum_prod_type,
    xChecks_variable, xChecks_check, stripTensorEmbed_tmul, stripTensorEmbed_tmul_check,
    mul_zero, Finset.sum_const_zero, add_zero]
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.sum_const_zero, Finset.mem_univ, if_true]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.rTensor_tmul,
    wordTensorEquiv_tmul_apply]
  change (∑ i, H.first r i * (stripExtend S v i * w j)) =
    (restrictColumns H.first S).mulVec v r * w j
  rw [← mulVec_stripExtend H.first S v]
  simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  ring

 theorem zChecks_stripTensorEmbed (H : Data (ZMod 2) R₁ C₁ R₂ C₂) (S : Set C₁) :
    (zChecks H).mulVecLin.comp (stripTensorEmbed S) =
      (wordTensorEquiv (ZMod 2) C₁ R₂).toLinearMap.comp
        ((TensorProduct.map (stripExtend S) H.second.mulVecLin)) := by
  classical
  apply TensorProduct.ext'
  intro v w
  funext ⟨i,r⟩
  change (zChecks H).mulVec _ _ = _
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fintype.sum_prod_type,
    zChecks_variable, zChecks_check, stripTensorEmbed_tmul, stripTensorEmbed_tmul_check,
    mul_zero, Finset.sum_const_zero, add_zero]
  simp only [ite_mul, zero_mul, Finset.sum_ite_irrel, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.sum_const_zero, Finset.mem_univ,
    if_true, LinearMap.comp_apply, LinearEquiv.coe_coe, TensorProduct.map_tmul,
    wordTensorEquiv_tmul_apply, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

end CoordinateTensor
end HGPExperiment

namespace HGPExperiment
section CycleDimensions
universe u
variable {R₁ C₁ R₂ C₂ : Type u}
  [Fintype R₁] [DecidableEq R₁] [Fintype C₁] [DecidableEq C₁]
  [Fintype R₂] [DecidableEq R₂] [Fintype C₂] [DecidableEq C₂]

theorem stripExtend_injective (S : Set C₁) : Function.Injective (stripExtend S) :=
  (coordinateSpace S).injective_subtype.comp (coordinateEquiv S).symm.injective

theorem range_stripExtend (S : Set C₁) :
    LinearMap.range (stripExtend S) = coordinateSpace S := by
  rw [stripExtend, LinearMap.range_comp, LinearEquiv.range, Submodule.map_top,
    Submodule.range_subtype]

theorem finrank_supported_cycles_strip (H : Data (ZMod 2) R₁ C₁ R₂ C₂) (S : Set C₁) :
    Module.finrank (ZMod 2) ↥(cycles (xChecks H) ⊓ coordinateSpace (wholeStrip S)) =
      Module.finrank (ZMod 2) (cycles (restrictColumns H.first S)) * Fintype.card C₂ := by
  have h := map_ker_comp_eq (stripTensorEmbed (R₁ := R₁) (R₂ := R₂) (C₂ := C₂) S)
    (xChecks H).mulVecLin
  rw [range_stripTensorEmbed, inf_comm] at h
  change Module.finrank (ZMod 2) ↥(LinearMap.ker _ ⊓ coordinateSpace (wholeStrip S)) = _
  rw [← h, finrank_map_of_injective _ (stripTensorEmbed_injective S),
    xChecks_stripTensorEmbed, LinearEquiv.ker_comp, strip_finrank_ker_rTensor,
    Module.finrank_fintype_fun_eq_card]
  rfl

theorem finrank_supported_cocycles_strip (H : Data (ZMod 2) R₁ C₁ R₂ C₂) (S : Set C₁) :
    Module.finrank (ZMod 2) ↥(cycles (zChecks H) ⊓ coordinateSpace (wholeStrip S)) =
      Fintype.card S * Module.finrank (ZMod 2) (cycles H.second) := by
  have h := map_ker_comp_eq (stripTensorEmbed (R₁ := R₁) (R₂ := R₂) (C₂ := C₂) S)
    (zChecks H).mulVecLin
  rw [range_stripTensorEmbed, inf_comm] at h
  change Module.finrank (ZMod 2) ↥(LinearMap.ker _ ⊓ coordinateSpace (wholeStrip S)) = _
  rw [← h, finrank_map_of_injective _ (stripTensorEmbed_injective S),
    zChecks_stripTensorEmbed, LinearEquiv.ker_comp]
  have hfactor : TensorProduct.map (stripExtend S) H.second.mulVecLin =
      ((stripExtend S).rTensor (R₂ → ZMod 2)).comp
        (H.second.mulVecLin.lTensor (S → ZMod 2)) := by
    ext x y
    rfl
  rw [hfactor, LinearMap.ker_comp_of_ker_eq_bot _
      (LinearMap.ker_eq_bot.mpr (Module.Flat.rTensor_preserves_injective_linearMap _
        (stripExtend_injective S))), strip_finrank_ker_lTensor,
      Module.finrank_fintype_fun_eq_card]
  rfl

theorem finrank_joint_restriction (H : Matrix R₁ C₁ (ZMod 2)) (S : Set C₁) :
    Module.finrank (ZMod 2) (LinearMap.ker (H.mulVecLin.prod (restrictCoords Sᶜ))) =
      Module.finrank (ZMod 2) (cycles (restrictColumns H S)) := by
  have h := map_ker_comp_eq (stripExtend S) H.mulVecLin
  have hr : LinearMap.ker (restrictCoords (F := ZMod 2) Sᶜ) = coordinateSpace S := by
    simpa using (ker_restrictCoords (F := ZMod 2) Sᶜ)
  rw [range_stripExtend, inf_comm, ← hr, ← LinearMap.ker_prod] at h
  have hmul : H.mulVecLin.comp (stripExtend S) = (restrictColumns H S).mulVecLin := by
    ext v
    exact mulVec_stripExtend H S v
  rw [← h, finrank_map_of_injective _ (stripExtend_injective S), hmul]
  rfl
end CycleDimensions
end HGPExperiment

namespace HGPExperiment
section BoundaryZ
universe u
variable {R₁ C₁ R₂ C₂ : Type u}
  [Fintype R₁] [DecidableEq R₁] [Fintype C₁] [DecidableEq C₁]
  [Fintype R₂] [DecidableEq R₂] [Fintype C₂] [DecidableEq C₂]

 theorem projected_boundary2_tensor (H : Data (ZMod 2) R₁ C₁ R₂ C₂) (S : Set C₁) :
    ((stripOutside S).comp (boundary2 H)).comp
        (wordTensorEquiv (ZMod 2) C₁ R₂).toLinearMap =
      ((wordTensorEquiv (ZMod 2) ↥(Sᶜ) C₂).prodCongr
        (wordTensorEquiv (ZMod 2) R₁ R₂)).toLinearMap.comp
          ((TensorProduct.map (restrictCoords Sᶜ) H.second.transpose.mulVecLin).prod
            (H.first.mulVecLin.rTensor (R₂ → ZMod 2))) := by
  apply TensorProduct.ext'
  intro x y
  apply Prod.ext
  · funext ⟨i,j⟩
    change boundary2 H (wordTensorEquiv (ZMod 2) C₁ R₂ (x ⊗ₜ[ZMod 2] y))
      (.inl (i,j)) = _
    rw [boundary2_inl_apply]
    simp only [wordTensorEquiv_tmul_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearMap.prod_apply, TensorProduct.map_tmul, LinearEquiv.prodCongr_apply,
      Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply,
      restrictCoords_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    ring
  · funext ⟨r,s⟩
    change boundary2 H (wordTensorEquiv (ZMod 2) C₁ R₂ (x ⊗ₜ[ZMod 2] y))
      (.inr (r,s)) = _
    rw [boundary2_inr_apply]
    simp only [wordTensorEquiv_tmul_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearMap.prod_apply, LinearMap.rTensor_tmul, LinearEquiv.prodCongr_apply,
      Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    ring

 theorem finrank_ker_projected_boundary2 (H : Data (ZMod 2) R₁ C₁ R₂ C₂) (S : Set C₁) :
    Module.finrank (ZMod 2) (LinearMap.ker ((stripOutside S).comp (boundary2 H))) =
      Module.finrank (ZMod 2) (cycles H.first) *
        Module.finrank (ZMod 2) (cycles H.second.transpose) +
      Module.finrank (ZMod 2) (cycles (restrictColumns H.first S)) * H.second.rank := by
  rw [← (kerCompLinearEquiv (wordTensorEquiv (ZMod 2) C₁ R₂)
    ((stripOutside S).comp (boundary2 H))).finrank_eq,
    projected_boundary2_tensor, LinearEquiv.ker_comp,
    LinearMap.ker_prod, inf_comm, ← LinearMap.ker_prod,
    finrank_ker_mixed_tensor, finrank_joint_restriction]
  change _ = _
  rw [show Module.finrank (ZMod 2) (LinearMap.range H.second.transpose.mulVecLin) =
      H.second.rank from Matrix.rank_transpose H.second]

 theorem finrank_supported_boundaries_strip_z (H : Data (ZMod 2) R₁ C₁ R₂ C₂) (S : Set C₁) :
    Module.finrank (ZMod 2) ↥(boundaries (zChecks H) ⊓ coordinateSpace (wholeStrip S)) =
      Module.finrank (ZMod 2) (cycles (restrictColumns H.first S)) * H.second.rank := by
  have h := finrank_range_inf_ker (boundary2 H) (stripOutside (C₂ := C₂) S)
  rw [ker_stripOutside, finrank_ker_projected_boundary2, finrank_ker_boundary2_eq] at h
  have hb : boundaries (zChecks H) = LinearMap.range (boundary2 H) := by
    change LinearMap.range ((boundary2Matrix H).transpose.transpose.mulVecLin) = _
    rw [Matrix.transpose_transpose]
    rfl
  rw [hb]
  change _ + Module.finrank (ZMod 2) (cycles H.first) *
    Module.finrank (ZMod 2) (cycles H.second.transpose) = _ at h
  omega

end BoundaryZ
end HGPExperiment

namespace HGPExperiment
section StripZFormula
universe u
variable {R₁ C₁ R₂ C₂ : Type u}
  [Fintype R₁] [DecidableEq R₁] [Fintype C₁] [DecidableEq C₁]
  [Fintype R₂] [DecidableEq R₂] [Fintype C₂] [DecidableEq C₂]

/-- Universal Z information in a whole variable-variable strip. -/
theorem strip_zDim (H : Data (ZMod 2) R₁ C₁ R₂ C₂) (S : Set C₁) :
    zDim (xChecks H) (zChecks H) (wholeStrip S) =
      Module.finrank (ZMod 2) (cycles (restrictColumns H.first S)) *
        Module.finrank (ZMod 2) (cycles H.second) := by
  have h := supportedDim_add_finrank_boundary (cycles (xChecks H)) (boundaries (zChecks H))
    (boundaries_le_cycles _ _ (checks_commute H)) (wholeStrip S)
  rw [finrank_supported_boundaries_strip_z, finrank_supported_cycles_strip] at h
  have hk := finrank_cycles_add_rank H.second
  change zDim (xChecks H) (zChecks H) (wholeStrip S) + _ = _ at h
  nlinarith
end StripZFormula
end HGPExperiment
