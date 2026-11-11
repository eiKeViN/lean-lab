import QEC.Coding.Core.Definitions

/-! # Equality of the two logical quotient dimensions
Source: QEC/Coding/Stabilizer/FiniteFieldPauli.lean, rank-nullity proof of
`chainComplex_finrank_middleCohomology_eq_middleHomology`. Its module is not
precompiled in the frozen dependency; this proof uses only the available core.
-/
noncomputable section
namespace Paper
open QEC.Coding
universe u v
variable {F : Type u} {ι : Type v} [Field F] [Fintype F] [Fintype ι]
/-- Both quotient ranks equal length minus the two check-space dimensions.
Apply quotient rank-nullity in each sector, identify the denominator ranks
with their actual images, then use the two orthogonal-complement dimension identities. -/
theorem cohomology_finrank_eq_homology
    {κ₀ κ₂ : Type v} [Fintype κ₀] [Fintype κ₂]
    (K : ChainComplexData F (Word F κ₀) (Word F ι) (Word F κ₂)) :
    Module.finrank F K.middleCohomology = Module.finrank F K.middleHomology := by
  have hcoh := Submodule.finrank_quotient_add_finrank K.middleCoboundaryInCocycles
  have hcob : Module.finrank F K.middleCoboundaryInCocycles =
      Dimension K.firstCoboundaryCheckCode := by
    rw [Dimension_eq_finrank_carrier]
    exact K.middleCoboundaryInCocyclesEquiv.finrank_eq
  have hcohSum : Module.finrank F K.middleCohomology +
      Dimension K.firstCoboundaryCheckCode =
      Dimension K.middleCocycleCode := by
    rw [← hcob, Dimension_eq_finrank_carrier]
    exact hcoh
  have hhom := Submodule.finrank_quotient_add_finrank K.middleBoundaryInCycles
  have hbound : Module.finrank F K.middleBoundaryInCycles =
      Dimension K.middleBoundaryCode := K.finrank_middleBoundaryInCycles_eq
  have hhomSum : Module.finrank F K.middleHomology +
      Dimension K.middleBoundaryCode = Dimension K.middleCycleCode := by
    rw [← hbound, Dimension_eq_finrank_carrier]
    exact hhom
  have hdualZ : Dimension K.middleCocycleCode +
      Dimension K.middleBoundaryCode = Length F ι := by
    have h := K.middleBoundaryCode.dimension_add_dual_dimension_eq_length
    have heq : Dimension K.middleBoundaryCode.dual =
        Dimension K.middleCocycleCode := by
      rw [Dimension_eq_finrank_carrier, Dimension_eq_finrank_carrier,
        K.middleBoundaryCode_dual_carrier_eq_middleCocycleCode]
    rw [heq] at h
    simpa only [add_comm] using h
  have hdualX : Dimension K.middleCycleCode +
      Dimension K.firstCoboundaryCheckCode = Length F ι := by
    have h := K.firstCoboundaryCheckCode.dimension_add_dual_dimension_eq_length
    have heq : Dimension K.firstCoboundaryCheckCode.dual =
        Dimension K.middleCycleCode := by
      rw [Dimension_eq_finrank_carrier, Dimension_eq_finrank_carrier,
        K.firstCoboundaryCheckCode_dual_carrier_eq_middleCycleCode]
    rw [heq] at h
    simpa only [add_comm] using h
  omega

end Paper
