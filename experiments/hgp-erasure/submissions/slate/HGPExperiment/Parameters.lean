import QEC.Results.QLDPC.HypergraphProductParameters

/-! The actual checks, quotient parameters, and representative distance bounds. -/
noncomputable section
namespace HGPExperiment.Parameters
open QEC.Coding QEC.Coding.HypergraphProduct
universe u
variable {R₁ C₁ R₂ C₂ : Type u}
  [Fintype R₁] [DecidableEq R₁] [Fintype C₁] [DecidableEq C₁]
  [Fintype R₂] [DecidableEq R₂] [Fintype C₂] [DecidableEq C₂]

abbrev P (h : Data (ZMod 2) R₁ C₁ R₂ C₂) := boundary1Matrix h
abbrev D (h : Data (ZMod 2) R₁ C₁ R₂ C₂) := (boundary2Matrix h).transpose

/-- The physical checks commute, including for empty index sets. -/
theorem A_commutes (h : Data (ZMod 2) R₁ C₁ R₂ C₂) :
    P h * (D h).transpose = 0 := boundary1Matrix_mul_boundary2Matrix h

/-- Explicit first check on the variable-variable block. -/
theorem P_inl (h : Data (ZMod 2) R₁ C₁ R₂ C₂) (r : R₁) (c c' : C₂) (a : C₁) :
    P h (r,c) (Sum.inl (a,c')) = if c = c' then h.first r a else 0 := rfl

/-- Over F₂ the sign in the tensor differential disappears. -/
theorem P_inr (h : Data (ZMod 2) R₁ C₁ R₂ C₂) (r r' : R₁) (s : R₂) (c : C₂) :
    P h (r,c) (Sum.inr (r',s)) = if r = r' then h.second s c else 0 := by
  simp [P, boundary1Matrix, CharTwo.neg_eq]

theorem D_inl (h : Data (ZMod 2) R₁ C₁ R₂ C₂) (a a' : C₁) (s : R₂) (c : C₂) :
    D h (a',s) (Sum.inl (a,c)) = if a = a' then h.second s c else 0 := rfl

theorem D_inr (h : Data (ZMod 2) R₁ C₁ R₂ C₂) (a : C₁) (s s' : R₂) (r : R₁) :
    D h (a,s') (Sum.inr (r,s)) = if s = s' then h.first r a else 0 := rfl

theorem A_length :
    Fintype.card (QubitIndex R₁ C₁ R₂ C₂) =
      Fintype.card C₁ * Fintype.card C₂ + Fintype.card R₁ * Fintype.card R₂ :=
  card_qubitIndex

/-- Z logical classes are the honest cycle/boundary quotient. -/
theorem A_dimension (h : Data (ZMod 2) R₁ C₁ R₂ C₂) :
    Module.finrank (ZMod 2) (chainComplex h).middleHomology =
      Dimension (firstCode h) * Dimension (secondCode h) +
      Dimension (firstTransposeCode h) * Dimension (secondTransposeCode h) :=
  finrank_middleHomology_eq_dimension_products h

/-- The X quotient has the same dimension, without a rank assumption. -/
theorem A_cohomology_dimension (h : Data (ZMod 2) R₁ C₁ R₂ C₂) :
    Module.finrank (ZMod 2) (chainComplex h).middleCohomology =
      Dimension (firstCode h) * Dimension (secondCode h) +
      Dimension (firstTransposeCode h) * Dimension (secondTransposeCode h) := by
  rw [QEC.Coding.FiniteFieldPauli.chainComplex_finrank_middleCohomology_eq_middleHomology]
  exact A_dimension h

/-- Every representative of a nonzero Z class obeys the four-distance bound. -/
theorem A_z_representative_bound (h : Data (ZMod 2) R₁ C₁ R₂ C₂)
    (v : (chainComplex h).middleCycleCode.carrier)
    (hv : (chainComplex h).middleBoundaryInCycles.mkQ v ≠ 0) :
    inputDistanceMinimum h ≤ (HammingWeight v.val : WithTop Nat) := by
  have hn : v.val ∉ (chainComplex h).middleBoundaryCode.carrier := by
    intro hb
    apply hv
    exact (Submodule.Quotient.eq_zero_iff_mem).2 hb
  have hl : IsCSSLogical (binaryCSSCode h).xCode (binaryCSSCode h).zCode v.val := by
    right
    constructor
    · simpa only [binaryCSSCode_xCode,
        ChainComplexData.firstCoboundaryCheckCode_dual_carrier_eq_middleCycleCode]
        using v.property
    · simpa only [binaryCSSCode_zCode] using hn
  exact (inputDistanceMinimum_le_extendedAlgebraicCSSMinimumDistance h).trans
    (finitePredicateMinimum_le_of hl)

/-- Every representative of a nonzero X class obeys the same bound. -/
theorem A_x_representative_bound (h : Data (ZMod 2) R₁ C₁ R₂ C₂)
    (v : (chainComplex h).middleCocycleCode.carrier)
    (hv : (chainComplex h).middleCoboundaryInCocycles.mkQ v ≠ 0) :
    inputDistanceMinimum h ≤ (HammingWeight v.val : WithTop Nat) := by
  have hn : v.val ∉ (chainComplex h).firstCoboundaryCheckCode.carrier := by
    intro hb
    apply hv
    exact (Submodule.Quotient.eq_zero_iff_mem).2 hb
  have hl : IsCSSLogical (binaryCSSCode h).xCode (binaryCSSCode h).zCode v.val := by
    left
    constructor
    · simpa only [binaryCSSCode_zCode,
        ChainComplexData.middleBoundaryCode_dual_carrier_eq_middleCocycleCode]
        using v.property
    · simpa only [binaryCSSCode_xCode] using hn
  exact (inputDistanceMinimum_le_extendedAlgebraicCSSMinimumDistance h).trans
    (finitePredicateMinimum_le_of hl)

end HGPExperiment.Parameters
