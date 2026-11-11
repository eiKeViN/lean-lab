import HGPExperiment.Parameters
import HGPExperiment.Erasure
import QEC.Coding.HypergraphProduct.Dimension.Formula

noncomputable section
namespace HGPExperiment
open TensorProduct QEC.Coding QEC.Coding.HypergraphProduct
universe u
variable {R₁ C₁ R₂ C₂ : Type u}
  [Fintype R₁] [DecidableEq R₁] [Fintype C₁] [DecidableEq C₁]
  [Fintype R₂] [DecidableEq R₂] [Fintype C₂] [DecidableEq C₂]

/-- Coordinates outside a physical variable-variable strip. -/
def stripComplementProjection (S : Set C₁) :
    (QubitIndex R₁ C₁ R₂ C₂ → ZMod 2) →ₗ[ZMod 2]
      ((↥(Sᶜ) × C₂ → ZMod 2) × (R₁ × R₂ → ZMod 2)) where
  toFun v := (fun q => v (.inl (q.1,q.2)), fun q => v (.inr q))
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

/-- The projected X-boundary map is the simultaneous tensor constraint. -/
theorem projected_boundary1Transpose_tensor (H : Data (ZMod 2) R₁ C₁ R₂ C₂)
    (S : Set C₁) [Fintype ↥(Sᶜ)] :
    ((stripComplementProjection S).comp (wordLinearMapTranspose (boundary1 H))).comp
        (wordTensorEquiv (ZMod 2) R₁ C₂).toLinearMap =
      jointTensorWordMap ((restrictCoords Sᶜ).comp H.first.transpose.mulVecLin)
        H.second.mulVecLin := by
  classical
  apply TensorProduct.ext'
  intro x y
  apply Prod.ext
  · funext q
    rcases q with ⟨i,j⟩
    change wordLinearMapTranspose (boundary1 H)
      (wordTensorEquiv (ZMod 2) R₁ C₂ (x ⊗ₜ[ZMod 2] y)) (.inl (i.val,j)) = _
    rw [boundary1Transpose_inl_apply]
    simp only [wordTensorEquiv_tmul_apply, jointTensorWordMap_tmul_fst_apply,
      LinearMap.comp_apply, restrictCoords_apply, Matrix.mulVecLin_apply,
      Matrix.mulVec, dotProduct, Matrix.transpose_apply]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro r hr
    ring
  · funext q
    rcases q with ⟨i,j⟩
    change wordLinearMapTranspose (boundary1 H)
      (wordTensorEquiv (ZMod 2) R₁ C₂ (x ⊗ₜ[ZMod 2] y)) (.inr (i,j)) = _
    rw [boundary1Transpose_inr_apply]
    simp only [wordTensorEquiv_tmul_apply, jointTensorWordMap_tmul_snd_apply,
      Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct]
    rw [ZMod.neg_eq_self_mod_two, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro c hc
    ring

/-- Projected X-boundary kernel, including arbitrary dependent rows and empty factors. -/
theorem finrank_ker_projected_boundary1Transpose
    (H : Data (ZMod 2) R₁ C₁ R₂ C₂) (S : Set C₁) [Fintype ↥(Sᶜ)] :
    Module.finrank (ZMod 2) (LinearMap.ker
      ((stripComplementProjection S).comp (wordLinearMapTranspose (boundary1 H)))) =
      Module.finrank (ZMod 2) (LinearMap.ker
        ((restrictCoords Sᶜ).comp H.first.transpose.mulVecLin)) *
      Module.finrank (ZMod 2) (cycles H.second) := by
  classical
  calc
    _ = Module.finrank (ZMod 2) (LinearMap.ker
        (((stripComplementProjection S).comp (wordLinearMapTranspose (boundary1 H))).comp
          (wordTensorEquiv (ZMod 2) R₁ C₂).toLinearMap)) :=
      (kerCompLinearEquiv (wordTensorEquiv (ZMod 2) R₁ C₂)
        ((stripComplementProjection S).comp (wordLinearMapTranspose (boundary1 H)))).finrank_eq.symm
    _ = Module.finrank (ZMod 2) (LinearMap.ker
        (jointTensorMap ((restrictCoords Sᶜ).comp H.first.transpose.mulVecLin)
          H.second.mulVecLin)) := by
      rw [projected_boundary1Transpose_tensor, ker_jointTensorWordMap_eq]
    _ = _ := finrank_ker_jointTensorMap _ _

end HGPExperiment
