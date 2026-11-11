import QEC.Results.QLDPC.HypergraphProductParameters
import Paper.LogicalDimension
import Paper.HGPChecks

/-!
# The actual HGP checks, logical quotients, and parameters

Source: `source.md`, A. The imported Tillich–Zémor theorem is expressly allowed
by the source. All matrix and quotient identifications below refer to that same construction.
-/

noncomputable section

namespace Paper.HGP

open QEC.Coding QEC.Coding.HypergraphProduct

universe u

variable {R₁ C₁ R₂ C₂ : Type u}
  [Fintype R₁] [DecidableEq R₁] [Fintype C₁] [DecidableEq C₁]
  [Fintype R₂] [DecidableEq R₂] [Fintype C₂] [DecidableEq C₂]

/-- Source A: entries of `[H₁ ⊗ I | I ⊗ H₂ᵀ]`. The minus sign vanishes over F₂. -/
theorem xChecks_blocks (H : Data (ZMod 2) R₁ C₁ R₂ C₂) :
    (∀ r c a b, xChecks H (r, c) (Sum.inl (a, b)) =
      if c = b then H.first r a else 0) ∧
    (∀ r c a b, xChecks H (r, c) (Sum.inr (a, b)) =
      if r = a then H.second b c else 0) := by
  constructor
  · intros; rfl
  · intros; simp [xChecks, boundary1Matrix, CharTwo.neg_eq]

/-- Source A: entries of `[I ⊗ H₂ | H₁ᵀ ⊗ I]`. -/
theorem zChecks_blocks (H : Data (ZMod 2) R₁ C₁ R₂ C₂) :
    (∀ c r a b, zChecks H (c, r) (Sum.inl (a, b)) =
      if a = c then H.second r b else 0) ∧
    (∀ c r a b, zChecks H (c, r) (Sum.inr (a, b)) =
      if b = r then H.first a c else 0) := by
  constructor <;> intros <;> rfl

/-- Source A: the two actual check matrices commute. Expand the transpose and
apply the supplied boundary identity, which requires no rank or positivity hypothesis. -/
theorem checks_commute (H : Data (ZMod 2) R₁ C₁ R₂ C₂) :
    xChecks H * (zChecks H).transpose = 0 := by
  simpa only [xChecks, zChecks, Matrix.transpose_transpose] using
    boundary1Matrix_mul_boundary2Matrix H

/-- Source A: both sectors are exactly the kernels and transpose images of the
specified checks. The two transpose statements use the supplied coordinate transpose lemma. -/
theorem check_quotient_semantics (H : Data (ZMod 2) R₁ C₁ R₂ C₂) :
    LinearMap.ker (Matrix.toLin' (xChecks H)) =
        (chainComplex H).middleCycleCode.carrier ∧
    LinearMap.range (Matrix.toLin' (zChecks H).transpose) =
        (chainComplex H).middleBoundaryCode.carrier ∧
    LinearMap.ker (Matrix.toLin' (zChecks H)) =
        (chainComplex H).middleCocycleCode.carrier ∧
    LinearMap.range (Matrix.toLin' (xChecks H).transpose) =
        (chainComplex H).firstCoboundaryCheckCode.carrier := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · simp only [zChecks, Matrix.transpose_transpose]
    rfl
  · change LinearMap.ker (Matrix.toLin' (boundary2Matrix H).transpose) =
      LinearMap.ker (wordLinearMapTranspose (Matrix.toLin' (boundary2Matrix H)))
    rw [wordLinearMapTranspose_toLin'_eq]
  · change LinearMap.range (Matrix.toLin' (boundary1Matrix H).transpose) =
      LinearMap.range (wordLinearMapTranspose (Matrix.toLin' (boundary1Matrix H)))
    rw [wordLinearMapTranspose_toLin'_eq]

/-- Source A: a Z quotient representative is nonzero exactly when it is not a boundary.
This is the defining zero-class criterion of the actual quotient. -/
theorem z_class_nonzero_iff (H : Data (ZMod 2) R₁ C₁ R₂ C₂)
    (v : (chainComplex H).middleCycleCode.carrier) :
    (Submodule.Quotient.mk v : (chainComplex H).middleHomology) ≠ 0 ↔
      v.1 ∉ (chainComplex H).middleBoundaryCode.carrier := by
  exact not_congr Submodule.Quotient.mk_eq_zero

/-- Source A: the corresponding zero-class criterion for the X quotient. -/
theorem x_class_nonzero_iff (H : Data (ZMod 2) R₁ C₁ R₂ C₂)
    (v : (chainComplex H).middleCocycleCode.carrier) :
    (Submodule.Quotient.mk v : (chainComplex H).middleCohomology) ≠ 0 ↔
      v.1 ∉ (chainComplex H).firstCoboundaryCheckCode.carrier := by
  exact not_congr Submodule.Quotient.mk_eq_zero

/-- Source A: length and both actual logical quotient dimensions. Project the
supplied parameter theorem and use the supplied equality of homology and cohomology ranks. -/
theorem parameters (H : Data (ZMod 2) R₁ C₁ R₂ C₂) :
    Fintype.card (QubitIndex R₁ C₁ R₂ C₂) =
        Fintype.card C₁ * Fintype.card C₂ + Fintype.card R₁ * Fintype.card R₂ ∧
    Module.finrank (ZMod 2) (chainComplex H).middleHomology =
        Dimension (firstCode H) * Dimension (secondCode H) +
          Dimension (firstTransposeCode H) * Dimension (secondTransposeCode H) ∧
    Module.finrank (ZMod 2) (chainComplex H).middleCohomology =
        Dimension (firstCode H) * Dimension (secondCode H) +
          Dimension (firstTransposeCode H) * Dimension (secondTransposeCode H) := by
  have h := tillichZemorHypergraphProductParameters H
  refine ⟨h.2.1, h.2.2.1, ?_⟩
  rw [Paper.cohomology_finrank_eq_homology]
  exact h.2.2.1

/-- Source A: the four-input distance minimum bounds every representative in
both nonzero logical sectors. Such a vector is a witness for the predicate whose
minimum defines CSS distance; compose that inequality with the supplied lower bound. -/
theorem representative_weight_lower_bound (H : Data (ZMod 2) R₁ C₁ R₂ C₂)
    (v : Word (ZMod 2) (QubitIndex R₁ C₁ R₂ C₂))
    (hv : (v ∈ (chainComplex H).middleCycleCode.carrier ∧
        v ∉ (chainComplex H).middleBoundaryCode.carrier) ∨
      (v ∈ (chainComplex H).middleCocycleCode.carrier ∧
        v ∉ (chainComplex H).firstCoboundaryCheckCode.carrier)) :
    inputDistanceMinimum H ≤ (HammingWeight v : WithTop Nat) := by
  classical
  have hv' : IsCSSLogical (binaryCSSCode H).xCode (binaryCSSCode H).zCode v := by
    rcases hv with hz | hx
    · apply Or.inr
      simpa only [binaryCSSCode_xCode, binaryCSSCode_zCode,
        ChainComplexData.firstCoboundaryCheckCode_dual_carrier_eq_middleCycleCode] using hz
    · apply Or.inl
      simpa only [binaryCSSCode_xCode, binaryCSSCode_zCode,
        ChainComplexData.middleBoundaryCode_dual_carrier_eq_middleCocycleCode] using hx
  exact (inputDistanceMinimum_le_extendedAlgebraicCSSMinimumDistance H).trans
    (finitePredicateMinimum_le_of (weight := HammingWeight) hv')

/-- Source A: zero classical codes have distance infinity, with the same
minimum convention used in the parameter theorem. This is the supplied finite-infimum result. -/
theorem zero_code_distance (C : LinearCode (ZMod 2) C₁) :
    extendedMinimumDistance C = ⊤ ↔ C.carrier = ⊥ :=
  extendedMinimumDistance_eq_top_iff C

end Paper.HGP
