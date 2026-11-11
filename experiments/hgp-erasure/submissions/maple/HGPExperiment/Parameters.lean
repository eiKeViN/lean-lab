import QEC.Results.QLDPC.HypergraphProductParameters

noncomputable section

namespace HGPExperiment.HGP

open QEC.Coding QEC.Coding.HypergraphProduct

universe u
variable {R₁ C₁ R₂ C₂ : Type u}
  [Fintype R₁] [DecidableEq R₁] [Fintype C₁] [DecidableEq C₁]
  [Fintype R₂] [DecidableEq R₂] [Fintype C₂] [DecidableEq C₂]

/-- The X-check matrix, on the actual HGP qubit set. -/
abbrev P (h : Data (ZMod 2) R₁ C₁ R₂ C₂) := boundary1Matrix h

/-- The Z-check matrix, on the same qubit set. -/
abbrev D (h : Data (ZMod 2) R₁ C₁ R₂ C₂) := (boundary2Matrix h).transpose

theorem commutation (h : Data (ZMod 2) R₁ C₁ R₂ C₂) :
    P h * (D h).transpose = 0 := by
  exact boundary1Matrix_mul_boundary2Matrix h

theorem length (h : Data (ZMod 2) R₁ C₁ R₂ C₂) :
    Fintype.card (QubitIndex R₁ C₁ R₂ C₂) =
      Fintype.card C₁ * Fintype.card C₂ + Fintype.card R₁ * Fintype.card R₂ :=
  (tillichZemorHypergraphProductParameters h).2.1

/-- The four input dimensions are dimensions of the matrix kernels. -/
theorem input_kernel_dimensions (h : Data (ZMod 2) R₁ C₁ R₂ C₂) :
    Dimension (firstCode h) = Module.finrank (ZMod 2) (LinearMap.ker (Matrix.toLin' h.first)) ∧
    Dimension (secondCode h) = Module.finrank (ZMod 2) (LinearMap.ker (Matrix.toLin' h.second)) ∧
    Dimension (firstTransposeCode h) = Module.finrank (ZMod 2) (LinearMap.ker (Matrix.toLin' h.first.transpose)) ∧
    Dimension (secondTransposeCode h) = Module.finrank (ZMod 2) (LinearMap.ker (Matrix.toLin' h.second.transpose)) := by
  simp only [Dimension_eq_finrank_carrier]
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem z_dimension (h : Data (ZMod 2) R₁ C₁ R₂ C₂) :
    Module.finrank (ZMod 2) (chainComplex h).middleHomology =
      Dimension (firstCode h) * Dimension (secondCode h) +
      Dimension (firstTransposeCode h) * Dimension (secondTransposeCode h) :=
  (tillichZemorHypergraphProductParameters h).2.2.1

theorem cohomology_dimension_eq_homology (h : Data (ZMod 2) R₁ C₁ R₂ C₂) :
    Module.finrank (ZMod 2) (chainComplex h).middleCohomology =
      Module.finrank (ZMod 2) (chainComplex h).middleHomology := by
  let K := chainComplex h
  have hcoh := Submodule.finrank_quotient_add_finrank K.middleCoboundaryInCocycles
  have hcob : Module.finrank (ZMod 2) K.middleCoboundaryInCocycles =
      Dimension K.firstCoboundaryCheckCode := by
    rw [Dimension_eq_finrank_carrier]
    exact K.middleCoboundaryInCocyclesEquiv.finrank_eq
  have hhom := Submodule.finrank_quotient_add_finrank K.middleBoundaryInCycles
  rw [K.finrank_middleBoundaryInCycles_eq] at hhom
  have hdualZ := K.middleBoundaryCode.dimension_add_dual_dimension_eq_length
  have hdualX := K.firstCoboundaryCheckCode.dimension_add_dual_dimension_eq_length
  rw [Dimension_eq_finrank_carrier, Dimension_eq_finrank_carrier,
    K.middleBoundaryCode_dual_carrier_eq_middleCocycleCode] at hdualZ
  rw [Dimension_eq_finrank_carrier, Dimension_eq_finrank_carrier,
    K.firstCoboundaryCheckCode_dual_carrier_eq_middleCycleCode] at hdualX
  rw [hcob, Dimension_eq_finrank_carrier] at hcoh
  rw [Dimension_eq_finrank_carrier] at hhom
  change Module.finrank (ZMod 2) K.middleCohomology =
    Module.finrank (ZMod 2) K.middleHomology
  simp only [Dimension_eq_finrank_carrier] at hcoh hhom
  omega

theorem x_dimension (h : Data (ZMod 2) R₁ C₁ R₂ C₂) :
    Module.finrank (ZMod 2) (chainComplex h).middleCohomology =
      Dimension (firstCode h) * Dimension (secondCode h) +
      Dimension (firstTransposeCode h) * Dimension (secondTransposeCode h) := by
  rw [cohomology_dimension_eq_homology, z_dimension]

theorem distance_lower_bound (h : Data (ZMod 2) R₁ C₁ R₂ C₂) :
    inputDistanceMinimum h ≤ extendedAlgebraicCSSMinimumDistance
      (binaryCSSCode h).xCode (binaryCSSCode h).zCode :=
  (tillichZemorHypergraphProductParameters h).2.2.2.1

/-- This bounds every representative, rather than only a chosen minimum. -/
theorem representative_weight_bound (h : Data (ZMod 2) R₁ C₁ R₂ C₂)
    (v : Word (ZMod 2) (QubitIndex R₁ C₁ R₂ C₂))
    (hv : IsCSSLogical (binaryCSSCode h).xCode (binaryCSSCode h).zCode v) :
    inputDistanceMinimum h ≤ (HammingWeight v : WithTop ℕ) := by
  exact (distance_lower_bound h).trans (finitePredicateMinimum_le_of hv)

end HGPExperiment.HGP
