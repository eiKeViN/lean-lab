import QEC.Results.QLDPC.HypergraphProductParameters

/-!
# Actual binary hypergraph-product checks and parameters

Source: `source.md`, A; supplied QECert Tillich–Zémor theorem. Both logical
spaces are the actual cycle/boundary quotients of the displayed checks.
-/

noncomputable section

namespace Sheaf.HGP

open QEC.Coding QEC.Coding.HypergraphProduct

universe u

variable {R₁ C₁ R₂ C₂ : Type u}
  [Fintype R₁] [DecidableEq R₁] [Fintype C₁] [DecidableEq C₁]
  [Fintype R₂] [DecidableEq R₂] [Fintype C₂] [DecidableEq C₂]

/-- Source A: the binary input checks of the hypergraph product. -/
abbrev Input := Data (ZMod 2) R₁ C₁ R₂ C₂

/-- Source A: physical coordinates `(C₁ × C₂) ⊕ (R₁ × R₂)`. -/
abbrev Qubit := QubitIndex R₁ C₁ R₂ C₂

/-- Source A: the X-check matrix `[H₁ ⊗ I | I ⊗ H₂ᵀ]`. -/
def checkP (H : Input (R₁ := R₁) (C₁ := C₁) (R₂ := R₂) (C₂ := C₂)) :=
  boundary1Matrix H

/-- Source A: the Z-check matrix `[I ⊗ H₂ | H₁ᵀ ⊗ I]`. -/
def checkD (H : Input (R₁ := R₁) (C₁ := C₁) (R₂ := R₂) (C₂ := C₂)) :=
  (boundary2Matrix H).transpose

variable (H : Input (R₁ := R₁) (C₁ := C₁) (R₂ := R₂) (C₂ := C₂))

/-- Source A, first block of P; this is the defining boundary entry. -/
theorem checkP_inl (r : R₁) (c₂ c₂' : C₂) (c₁ : C₁) :
    checkP H (r, c₂) (Sum.inl (c₁, c₂')) =
      if c₂ = c₂' then H.first r c₁ else 0 := rfl

/-- Source A, second block of P. In F₂ the boundary's minus sign is plus. -/
theorem checkP_inr (r r' : R₁) (r₂ : R₂) (c₂ : C₂) :
    checkP H (r, c₂) (Sum.inr (r', r₂)) =
      if r = r' then H.second r₂ c₂ else 0 := by
  simp [checkP, boundary1Matrix, CharTwo.neg_eq]

/-- Source A, first block of D; transpose the second boundary entry. -/
theorem checkD_inl (c₁ c₁' : C₁) (r₂ : R₂) (c₂ : C₂) :
    checkD H (c₁', r₂) (Sum.inl (c₁, c₂)) =
      if c₁ = c₁' then H.second r₂ c₂ else 0 := rfl

/-- Source A, second block of D; transpose the second boundary entry. -/
theorem checkD_inr (r₁ : R₁) (c₁ : C₁) (r₂ r₂' : R₂) :
    checkD H (c₁, r₂') (Sum.inr (r₁, r₂)) =
      if r₂ = r₂' then H.first r₁ c₁ else 0 := rfl

/-- Source A: orthogonality is the supplied boundary-squared identity. -/
theorem checks_orthogonal : checkP H * (checkD H).transpose = 0 :=
  boundary1Matrix_mul_boundary2Matrix H

/-- Source A: count the two disjoint product coordinate blocks. -/
theorem length_eq : Fintype.card (Qubit (R₁ := R₁) (C₁ := C₁)
    (R₂ := R₂) (C₂ := C₂)) =
    Fintype.card C₁ * Fintype.card C₂ + Fintype.card R₁ * Fintype.card R₂ :=
  card_qubitIndex

/-- Source A: Z logical space `ker P / row D`, using the actual chain quotient. -/
abbrev ZLogical := (chainComplex H).middleHomology

/-- Source A: X logical space `ker D / row P`, using the actual dual quotient. -/
abbrev XLogical := (chainComplex H).middleCohomology

/-- Source A: Z cycles are exactly the kernel of the displayed P check. -/
theorem zCycles_eq : (chainComplex H).middleCycleCode.carrier =
    LinearMap.ker (Matrix.toLin' (checkP H)) := rfl

/-- Source A: Z boundaries are the row space of D, as the range of Dᵀ. -/
theorem zBoundaries_eq : (chainComplex H).middleBoundaryCode.carrier =
    LinearMap.range (Matrix.toLin' (checkD H).transpose) := rfl

/-- Source A: X cycles are exactly the kernel of the displayed D check.
Proof: the coordinate transpose agrees with the matrix transpose. -/
theorem xCycles_eq : (chainComplex H).middleCocycleCode.carrier =
    LinearMap.ker (Matrix.toLin' (checkD H)) := by
  change LinearMap.ker (wordLinearMapTranspose (boundary2 H)) = _
  rw [boundary2, wordLinearMapTranspose_toLin'_eq]
  rfl

/-- Source A: X boundaries are the row space of P.
Proof: the coordinate transpose agrees with the matrix transpose. -/
theorem xBoundaries_eq : (chainComplex H).firstCoboundaryCheckCode.carrier =
    LinearMap.range (Matrix.toLin' (checkP H).transpose) := by
  change LinearMap.range (wordLinearMapTranspose (boundary1 H)) = _
  rw [boundary1, wordLinearMapTranspose_toLin'_eq]
  rfl

/-- Source A: exact Z quotient dimension, supplied Künneth formula without
rank or nonemptiness hypotheses. The four codes are the actual input kernels. -/
theorem z_dimension : Module.finrank (ZMod 2) (ZLogical H) =
    Dimension (firstCode H) * Dimension (secondCode H) +
      Dimension (firstTransposeCode H) * Dimension (secondTransposeCode H) :=
  finrank_middleHomology_eq_dimension_products H

/-- Source A: exact X quotient dimension. Finite chain homology and cohomology
have equal ranks; apply the supplied Z-sector Künneth formula. -/
theorem x_dimension : Module.finrank (ZMod 2) (XLogical H) =
    Dimension (firstCode H) * Dimension (secondCode H) +
      Dimension (firstTransposeCode H) * Dimension (secondTransposeCode H) := by
  let K := chainComplex H
  have hcoh := Submodule.finrank_quotient_add_finrank K.middleCoboundaryInCocycles
  have hcob : Module.finrank (ZMod 2) K.middleCoboundaryInCocycles =
      Dimension K.firstCoboundaryCheckCode := K.middleCoboundaryInCocyclesEquiv.finrank_eq
  have hcohSum : Module.finrank (ZMod 2) (XLogical H) +
      Dimension K.firstCoboundaryCheckCode = Dimension K.middleCocycleCode := by
    rw [← hcob, Dimension_eq_finrank_carrier]
    exact hcoh
  have hhom := Submodule.finrank_quotient_add_finrank K.middleBoundaryInCycles
  rw [K.finrank_middleBoundaryInCycles_eq] at hhom
  have hdualZ : Dimension K.middleCocycleCode + Dimension K.middleBoundaryCode =
      Length (ZMod 2) (QubitIndex R₁ C₁ R₂ C₂) := by
    have h := K.middleBoundaryCode.dimension_add_dual_dimension_eq_length
    have heq : Dimension K.middleBoundaryCode.dual = Dimension K.middleCocycleCode := by
      rw [Dimension_eq_finrank_carrier, Dimension_eq_finrank_carrier,
        K.middleBoundaryCode_dual_carrier_eq_middleCocycleCode]
    omega
  have hdualX : Dimension K.middleCycleCode + Dimension K.firstCoboundaryCheckCode =
      Length (ZMod 2) (QubitIndex R₁ C₁ R₂ C₂) := by
    have h := K.firstCoboundaryCheckCode.dimension_add_dual_dimension_eq_length
    have heq : Dimension K.firstCoboundaryCheckCode.dual = Dimension K.middleCycleCode := by
      rw [Dimension_eq_finrank_carrier, Dimension_eq_finrank_carrier,
        K.firstCoboundaryCheckCode_dual_carrier_eq_middleCycleCode]
    omega
  have hdim := z_dimension H
  change Module.finrank (ZMod 2) K.middleHomology = _ at hdim
  change Module.finrank (ZMod 2) K.middleHomology + _ = _ at hhom
  change _ = Module.finrank (ZMod 2) K.middleCycleCode at hhom
  change _ = Module.finrank (ZMod 2) K.middleCocycleCode at hcohSum
  change Module.finrank (ZMod 2) K.middleCocycleCode + _ = _ at hdualZ
  change Module.finrank (ZMod 2) K.middleCycleCode + _ = _ at hdualX
  omega

/-- Source A: every nontrivial Z representative obeys the four-distance bound.
Proof: it is a pure logical vector, so its weight bounds the CSS minimum;
compose with the supplied lower bound. Zero input codes have infinite distance. -/
theorem z_representative_weight (v : Word (ZMod 2) (QubitIndex R₁ C₁ R₂ C₂))
    (hv : Matrix.toLin' (checkP H) v = 0)
    (hn : v ∉ LinearMap.range (Matrix.toLin' (checkD H).transpose)) :
    inputDistanceMinimum H ≤ (HammingWeight v : WithTop Nat) := by
  classical
  apply (inputDistanceMinimum_le_extendedAlgebraicCSSMinimumDistance H).trans
  apply finitePredicateMinimum_le_of
  apply Or.inr
  constructor
  · rw [binaryCSSCode_xCode,
      (chainComplex H).firstCoboundaryCheckCode_dual_carrier_eq_middleCycleCode]
    exact hv
  · exact hn

/-- Source A: every nontrivial X representative obeys the four-distance bound.
Proof: it is a pure logical vector, so its weight bounds the CSS minimum;
compose with the supplied lower bound. No nonemptiness hypothesis is used. -/
theorem x_representative_weight (v : Word (ZMod 2) (QubitIndex R₁ C₁ R₂ C₂))
    (hv : Matrix.toLin' (checkD H) v = 0)
    (hn : v ∉ LinearMap.range (Matrix.toLin' (checkP H).transpose)) :
    inputDistanceMinimum H ≤ (HammingWeight v : WithTop Nat) := by
  classical
  apply (inputDistanceMinimum_le_extendedAlgebraicCSSMinimumDistance H).trans
  apply finitePredicateMinimum_le_of
  apply Or.inl
  constructor
  · rw [binaryCSSCode_zCode,
      (chainComplex H).middleBoundaryCode_dual_carrier_eq_middleCocycleCode,
      xCycles_eq H]
    exact hv
  · rw [binaryCSSCode_xCode, xBoundaries_eq H]
    exact hn

end Sheaf.HGP
