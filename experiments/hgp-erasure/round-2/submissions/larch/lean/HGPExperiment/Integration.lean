import HGPExperiment.Parameters
import HGPExperiment.Inference
import HGPExperiment.LogicalSemantics

noncomputable section
namespace HGPExperiment
open QEC.Coding QEC.Coding.HypergraphProduct
universe u
variable {R₁ C₁ R₂ C₂ : Type u}
  [Fintype R₁] [DecidableEq R₁] [Fintype C₁] [DecidableEq C₁]
  [Fintype R₂] [DecidableEq R₂] [Fintype C₂] [DecidableEq C₂]

@[simp] theorem cycles_xChecks (H : Data (ZMod 2) R₁ C₁ R₂ C₂) :
    cycles (xChecks H) = (chainComplex H).middleCycleCode.carrier := rfl

@[simp] theorem boundaries_zChecks (H : Data (ZMod 2) R₁ C₁ R₂ C₂) :
    boundaries (zChecks H) = (chainComplex H).middleBoundaryCode.carrier := rfl

@[simp] theorem boundaries_xChecks (H : Data (ZMod 2) R₁ C₁ R₂ C₂) :
    boundaries (xChecks H) = (chainComplex H).firstCoboundaryCheckCode.carrier := by
  change LinearMap.range ((boundary1Matrix H).transpose.mulVecLin) =
    LinearMap.range (wordLinearMapTranspose (boundary1 H))
  rw [boundary1, wordLinearMapTranspose_toLin'_eq]
  rfl

@[simp] theorem cycles_zChecks (H : Data (ZMod 2) R₁ C₁ R₂ C₂) :
    cycles (zChecks H) = (chainComplex H).middleCocycleCode.carrier := by
  change LinearMap.ker ((boundary2Matrix H).transpose.mulVecLin) =
    LinearMap.ker (wordLinearMapTranspose (boundary2 H))
  rw [boundary2, wordLinearMapTranspose_toLin'_eq]
  rfl

/-- The erasure model and the supplied parameter theorem use the identical
pure logical sectors of the identical two check operators. -/
theorem matrixLogical_iff_qec (H : Data (ZMod 2) R₁ C₁ R₂ C₂)
    (v : QubitIndex R₁ C₁ R₂ C₂ → ZMod 2) :
    matrixLogical (xChecks H) (zChecks H) v ↔
      IsCSSLogical (binaryCSSCode H).xCode (binaryCSSCode H).zCode v := by
  unfold matrixLogical IsCSSLogical
  rw [cycles_zChecks, boundaries_xChecks, cycles_xChecks, boundaries_zChecks,
    binaryCSSCode_xCode, binaryCSSCode_zCode,
    (chainComplex H).middleBoundaryCode_dual_carrier_eq_middleCocycleCode,
    (chainComplex H).firstCoboundaryCheckCode_dual_carrier_eq_middleCycleCode]

theorem matrixCSSDistance_eq_hgpDistance (H : Data (ZMod 2) R₁ C₁ R₂ C₂) :
    matrixCSSDistance (xChecks H) (zChecks H) = hgpDistance H := by
  classical
  apply le_antisymm
  · apply le_finitePredicateMinimum
    intro v hv
    exact finitePredicateMinimum_le_of (weight := HammingWeight)
      ((matrixLogical_iff_qec H v).mpr hv)
  · apply le_finitePredicateMinimum
    intro v hv
    exact finitePredicateMinimum_le_of (weight := HammingWeight)
      ((matrixLogical_iff_qec H v).mp hv)

/-- The distance controlling failure of actual HGP erasures is the distance
appearing in the Tillich--Zémor parameter theorem. -/
theorem hgp_erasureDistance (H : Data (ZMod 2) R₁ C₁ R₂ C₂) :
    erasureDistance (xChecks H) (zChecks H) = hgpDistance H := by
  rw [erasureDistance_eq_cssDistance, matrixCSSDistance_eq_hgpDistance]

/-- Each set smaller than the HGP lower distance bound has unambiguous inference. -/
theorem hgp_small_erasure_succeeds (H : Data (ZMod 2) R₁ C₁ R₂ C₂)
    (E : Finset (QubitIndex R₁ C₁ R₂ C₂))
    (hE : (E.card : WithTop Nat) < inputDistanceMinimum H) :
    erasureSucceeds (xChecks H) (zChecks H) (E : Set _) := by
  classical
  by_contra hf
  have hmin : erasureDistance (xChecks H) (zChecks H) ≤ (E.card : WithTop Nat) :=
    finitePredicateMinimum_le_of (weight := Finset.card) hf
  rw [hgp_erasureDistance] at hmin
  exact (not_lt_of_ge ((hgp_distance_lower H).trans hmin)) hE

/-- The global erasure dimension is the dimension of the same HGP homology quotient. -/
theorem logicalDim_hgp (H : Data (ZMod 2) R₁ C₁ R₂ C₂) :
    logicalDim (xChecks H) (zChecks H) =
      Module.finrank (ZMod 2) (ZLogical H) := by
  unfold logicalDim zDim
  rw [supportedDim_univ_eq, cycles_xChecks, boundaries_zChecks]
  rfl

end HGPExperiment
