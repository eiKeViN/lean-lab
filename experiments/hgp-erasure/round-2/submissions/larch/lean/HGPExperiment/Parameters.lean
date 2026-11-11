import QEC.Results.QLDPC.HypergraphProductParameters

/-! The actual two-input HGP, with the same checks as the supplied parameter theorem. -/
noncomputable section

namespace HGPExperiment
open QEC.Coding QEC.Coding.HypergraphProduct

universe u
variable {R₁ C₁ R₂ C₂ : Type u}
  [Fintype R₁] [DecidableEq R₁] [Fintype C₁] [DecidableEq C₁]
  [Fintype R₂] [DecidableEq R₂] [Fintype C₂] [DecidableEq C₂]

abbrev xChecks (H : Data (ZMod 2) R₁ C₁ R₂ C₂) := boundary1Matrix H
abbrev zChecks (H : Data (ZMod 2) R₁ C₁ R₂ C₂) := (boundary2Matrix H).transpose

theorem checks_commute (H : Data (ZMod 2) R₁ C₁ R₂ C₂) :
    xChecks H * (zChecks H).transpose = 0 := by
  exact boundary1Matrix_mul_boundary2Matrix H

@[simp] theorem xChecks_variable (H : Data (ZMod 2) R₁ C₁ R₂ C₂)
    (r : R₁) (c : C₂) (i : C₁) (j : C₂) :
    xChecks H (r,c) (.inl (i,j)) = if c = j then H.first r i else 0 := rfl

@[simp] theorem xChecks_check (H : Data (ZMod 2) R₁ C₁ R₂ C₂)
    (r : R₁) (c : C₂) (i : R₁) (j : R₂) :
    xChecks H (r,c) (.inr (i,j)) = if r = i then H.second j c else 0 := by
  simp [xChecks, boundary1Matrix, CharTwo.neg_eq]

@[simp] theorem zChecks_variable (H : Data (ZMod 2) R₁ C₁ R₂ C₂)
    (c : C₁) (r : R₂) (i : C₁) (j : C₂) :
    zChecks H (c,r) (.inl (i,j)) = if i = c then H.second r j else 0 := rfl

@[simp] theorem zChecks_check (H : Data (ZMod 2) R₁ C₁ R₂ C₂)
    (c : C₁) (r : R₂) (i : R₁) (j : R₂) :
    zChecks H (c,r) (.inr (i,j)) = if j = r then H.first i c else 0 := rfl

/-- Z cycles modulo the actual Z-check row space. -/
abbrev ZLogical (H : Data (ZMod 2) R₁ C₁ R₂ C₂) := (chainComplex H).middleHomology
/-- X cocycles modulo the actual X-check row space. -/
abbrev XLogical (H : Data (ZMod 2) R₁ C₁ R₂ C₂) := (chainComplex H).middleCohomology

abbrev hgpDistance (H : Data (ZMod 2) R₁ C₁ R₂ C₂) :=
  extendedAlgebraicCSSMinimumDistance (binaryCSSCode H).xCode (binaryCSSCode H).zCode

theorem hgp_length : Fintype.card (QubitIndex R₁ C₁ R₂ C₂) =
    Fintype.card C₁ * Fintype.card C₂ + Fintype.card R₁ * Fintype.card R₂ :=
  card_qubitIndex

theorem zLogical_dimension (H : Data (ZMod 2) R₁ C₁ R₂ C₂) :
    Module.finrank (ZMod 2) (ZLogical H) =
      Dimension (firstCode H) * Dimension (secondCode H) +
      Dimension (firstTransposeCode H) * Dimension (secondTransposeCode H) :=
  (tillichZemorHypergraphProductParameters H).2.2.1

theorem xLogical_dimension (H : Data (ZMod 2) R₁ C₁ R₂ C₂) :
    Module.finrank (ZMod 2) (XLogical H) =
      Dimension (firstCode H) * Dimension (secondCode H) +
      Dimension (firstTransposeCode H) * Dimension (secondTransposeCode H) := by
  let K := chainComplex H
  have hcoh := Submodule.finrank_quotient_add_finrank K.middleCoboundaryInCocycles
  have hcob : Module.finrank (ZMod 2) K.middleCoboundaryInCocycles =
      Dimension K.firstCoboundaryCheckCode := by
    rw [Dimension_eq_finrank_carrier]
    exact K.middleCoboundaryInCocyclesEquiv.finrank_eq
  have hcohSum : Module.finrank (ZMod 2) K.middleCohomology +
      Dimension K.firstCoboundaryCheckCode = Dimension K.middleCocycleCode := by
    rw [← hcob, Dimension_eq_finrank_carrier]
    exact hcoh
  have hhom := Submodule.finrank_quotient_add_finrank K.middleBoundaryInCycles
  have hbound : Module.finrank (ZMod 2) K.middleBoundaryInCycles =
      Dimension K.middleBoundaryCode := K.finrank_middleBoundaryInCycles_eq
  have hhomSum : Module.finrank (ZMod 2) K.middleHomology +
      Dimension K.middleBoundaryCode = Dimension K.middleCycleCode := by
    rw [← hbound, Dimension_eq_finrank_carrier]
    exact hhom
  have hdualZ := K.middleBoundaryCode.dimension_add_dual_dimension_eq_length
  have heqZ : Dimension K.middleBoundaryCode.dual = Dimension K.middleCocycleCode := by
    rw [Dimension_eq_finrank_carrier, Dimension_eq_finrank_carrier,
      K.middleBoundaryCode_dual_carrier_eq_middleCocycleCode]
  have hdualX := K.firstCoboundaryCheckCode.dimension_add_dual_dimension_eq_length
  have heqX : Dimension K.firstCoboundaryCheckCode.dual = Dimension K.middleCycleCode := by
    rw [Dimension_eq_finrank_carrier, Dimension_eq_finrank_carrier,
      K.firstCoboundaryCheckCode_dual_carrier_eq_middleCycleCode]
  have hz := zLogical_dimension H
  change Module.finrank (ZMod 2) K.middleHomology = _ at hz
  change Module.finrank (ZMod 2) K.middleCohomology = _
  omega

theorem hgp_distance_lower (H : Data (ZMod 2) R₁ C₁ R₂ C₂) :
    inputDistanceMinimum H ≤ hgpDistance H :=
  (tillichZemorHypergraphProductParameters H).2.2.2.1

/-- This bound applies to each representative of each nonzero pure logical class. -/
theorem logical_representative_lower (H : Data (ZMod 2) R₁ C₁ R₂ C₂)
    (v : Word (ZMod 2) (QubitIndex R₁ C₁ R₂ C₂))
    (hv : IsCSSLogical (binaryCSSCode H).xCode (binaryCSSCode H).zCode v) :
    inputDistanceMinimum H ≤ (HammingWeight v : WithTop ℕ) := by
  classical
  exact (hgp_distance_lower H).trans (finitePredicateMinimum_le_of hv)

/-- Explicit quotient formulation: every representative of a nonzero Z class obeys the bound. -/
theorem zClass_representative_lower (H : Data (ZMod 2) R₁ C₁ R₂ C₂)
    (v : (chainComplex H).middleCycleCode.carrier)
    (hv : (Submodule.Quotient.mk v : ZLogical H) ≠ 0) :
    inputDistanceMinimum H ≤ (HammingWeight v.val : WithTop ℕ) := by
  apply logical_representative_lower H v.val
  apply Or.inr
  constructor
  · simpa only [binaryCSSCode_xCode,
      ChainComplexData.firstCoboundaryCheckCode_dual_carrier_eq_middleCycleCode] using v.property
  · intro hb
    apply hv
    exact (Submodule.Quotient.mk_eq_zero _).mpr hb

/-- Explicit quotient formulation for every representative of a nonzero X class. -/
theorem xClass_representative_lower (H : Data (ZMod 2) R₁ C₁ R₂ C₂)
    (v : (chainComplex H).middleCocycleCode.carrier)
    (hv : (Submodule.Quotient.mk v : XLogical H) ≠ 0) :
    inputDistanceMinimum H ≤ (HammingWeight v.val : WithTop ℕ) := by
  apply logical_representative_lower H v.val
  apply Or.inl
  constructor
  · simpa only [binaryCSSCode_zCode,
      ChainComplexData.middleBoundaryCode_dual_carrier_eq_middleCocycleCode] using v.property
  · intro hb
    apply hv
    exact (Submodule.Quotient.mk_eq_zero _).mpr hb

/-- The zero input code has infinite distance; no positivity or rank assumption is used. -/
theorem zero_code_distance (C : LinearCode (ZMod 2) C₁) :
    extendedMinimumDistance C = ⊤ ↔ C.carrier = ⊥ :=
  extendedMinimumDistance_eq_top_iff C

end HGPExperiment
