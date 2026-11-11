import QEC.Results.QLDPC.HypergraphProductParameters

noncomputable section

open QEC.Coding QEC.Coding.HypergraphProduct

namespace HGPExperiment.Examples

abbrev F := ZMod 2
abbrev Bit := Fin 2

def repetitionCheck : Matrix (Fin 1) Bit F := fun _ _ => 1

def redundantCheck : Matrix Bit Bit F := fun _ _ => 1

def five : Data F (Fin 1) Bit (Fin 1) Bit := diagonalData repetitionCheck

def eight : Data F Bit Bit Bit Bit := diagonalData redundantCheck

/-- The two-bit repetition word. -/
def repetitionWord : Bit → F := fun _ => 1

private theorem sum_two_eq_zero_iff (x : Bit → F) :
    (x 0 + x 1 = 0) ↔ x 1 = x 0 := by
  have h : ∀ a b : F, a + b = 0 ↔ b = a := by decide
  exact h _ _

/-- The kernel of a nonempty all-ones check on two coordinates. -/
theorem ones_kernel {R : Type} [Fintype R] [Nonempty R]
    (x : Bit → F) :
    x ∈ LinearMap.ker (Matrix.toLin' (fun (_ : R) (_ : Bit) => (1 : F))) ↔
      x 1 = x 0 := by
  change (Matrix.toLin' (fun (_ : R) (_ : Bit) => (1 : F))) x = 0 ↔ _
  simp only [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    one_mul]
  constructor
  · intro h
    exact sum_two_eq_zero_iff x |>.mp (congrFun h (Classical.arbitrary R))
  · intro h
    funext r
    exact (sum_two_eq_zero_iff x).mpr h

/-- Evaluation at the first coordinate identifies the repetition kernel with F₂. -/
def onesKernelEquiv (R : Type) [Fintype R] [Nonempty R] :
    LinearMap.ker (Matrix.toLin' (fun (_ : R) (_ : Bit) => (1 : F))) ≃ₗ[F] F where
  toFun x := x.val 0
  invFun a := ⟨fun _ => a, (ones_kernel _).mpr rfl⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    fin_cases i
    · rfl
    · exact ((ones_kernel x.val).mp x.property).symm
  right_inv a := rfl
  map_add' x y := rfl
  map_smul' a x := rfl

theorem ones_kernel_dimension (R : Type) [Fintype R] [Nonempty R] :
    Module.finrank F
      (LinearMap.ker (Matrix.toLin' (fun (_ : R) (_ : Bit) => (1 : F)))) = 1 := by
  rw [(onesKernelEquiv R).finrank_eq]
  exact Module.finrank_self F

theorem repetition_distance (R : Type) [Fintype R] [DecidableEq R] [Nonempty R] :
    extendedMinimumDistance
      (parityCheckKernelCode (Matrix.toLin' (fun (_ : R) (_ : Bit) => (1 : F)))) = 2 := by
  classical
  apply le_antisymm
  · apply finitePredicateMinimum_le_of (x := repetitionWord)
    constructor
    · exact (ones_kernel _).mpr rfl
    · intro h
      have := congrFun h 0
      norm_num [repetitionWord] at this
  · apply le_finitePredicateMinimum
    intro x hx
    have heq := (ones_kernel x).mp hx.1
    have h0 : x 0 ≠ 0 := by
      intro hz
      apply hx.2
      funext i
      fin_cases i
      · exact hz
      · exact heq.trans hz
    have hweight : HammingWeight x = 2 := by
      simp [HammingWeight, hammingSupport, heq, h0]
    rw [hweight]

theorem five_length : Fintype.card (QubitIndex (Fin 1) Bit (Fin 1) Bit) = 5 := by decide

theorem eight_length : Fintype.card (QubitIndex Bit Bit Bit Bit) = 8 := by decide

theorem five_kernel_dimension : Dimension (firstCode five) = 1 := by
  exact ones_kernel_dimension (Fin 1)

theorem eight_kernel_dimension : Dimension (firstCode eight) = 1 := by
  exact ones_kernel_dimension Bit

theorem eight_transpose_kernel_dimension : Dimension (firstTransposeCode eight) = 1 := by
  exact ones_kernel_dimension Bit

theorem repetitionCheck_surjective : Function.Surjective (Matrix.toLin' repetitionCheck) := by
  intro y
  refine ⟨![y 0, 0], ?_⟩
  funext r
  fin_cases r
  simp [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, repetitionCheck, Fin.sum_univ_two]

theorem five_transpose_kernel_dimension : Dimension (firstTransposeCode five) = 0 := by
  exact (diagonalTransposeCode_dimensions_eq_zero repetitionCheck repetitionCheck_surjective).1

theorem five_dimension : Module.finrank F (chainComplex five).middleHomology = 1 := by
  rw [finrank_middleHomology_diagonal_fullRank repetitionCheck repetitionCheck_surjective]
  have h := five_kernel_dimension
  change Dimension (firstCode (diagonalData repetitionCheck)) = 1 at h
  rw [h]
  norm_num

theorem eight_dimension : Module.finrank F (chainComplex eight).middleHomology = 2 := by
  rw [finrank_middleHomology_eq_dimension_products]
  have hs : Dimension (secondCode eight) = 1 := eight_kernel_dimension
  have ht : Dimension (secondTransposeCode eight) = 1 := eight_transpose_kernel_dimension
  rw [eight_kernel_dimension, hs, eight_transpose_kernel_dimension, ht]

theorem five_distance : extendedAlgebraicCSSMinimumDistance
    (binaryCSSCode five).xCode (binaryCSSCode five).zCode = 2 := by
  rw [extendedAlgebraicCSSMinimumDistance_diagonal_fullRank repetitionCheck repetitionCheck_surjective]
  exact repetition_distance (Fin 1)

theorem eight_distance : extendedAlgebraicCSSMinimumDistance
    (binaryCSSCode eight).xCode (binaryCSSCode eight).zCode = 2 := by
  have h : extendedMinimumDistance (firstCode eight) = 2 := repetition_distance Bit
  have hs : extendedMinimumDistance (secondCode eight) = 2 := h
  have ht : extendedMinimumDistance (firstTransposeCode eight) = 2 := h
  have hts : extendedMinimumDistance (secondTransposeCode eight) = 2 := h
  have hm : inputDistanceMinimum eight = 2 := by
    simp [inputDistanceMinimum, h, hs, ht, hts]
  rw [extendedAlgebraicCSSMinimumDistance_eq_inputDistanceMinimum eight, hm]
  exact Or.inl ⟨h.trans hm.symm, by rw [hs]; exact WithTop.coe_ne_top⟩

/-- An explicitly displayed weight-two nonzero homology class for either input. -/
theorem ones_weight_two_witness (R : Type) [Fintype R] [DecidableEq R] [Nonempty R] :
    let d : Data F R Bit R Bit := diagonalData (fun _ _ => 1)
    let z := firstBlockWord (rowOne := R) (rowTwo := R) repetitionWord (Pi.single 0 1)
    z ∈ (chainComplex d).middleCycleCode.carrier ∧
    z ∉ (chainComplex d).middleBoundaryCode.carrier ∧ HammingWeight z = 2 := by
  dsimp only
  let d : Data F R Bit R Bit := diagonalData (fun _ _ => 1)
  let z := firstBlockWord (rowOne := R) (rowTwo := R) repetitionWord (Pi.single 0 1)
  let u := firstBlockWord (rowOne := R) (rowTwo := R) (Pi.single 0 1) repetitionWord
  have hk : repetitionWord ∈ (firstCode d).carrier := (ones_kernel _).mpr rfl
  have hk' : repetitionWord ∈ (secondCode d).carrier := hk
  refine ⟨firstBlockWord_mem_middleCycleCode d _ _ hk, ?_, ?_⟩
  · apply not_mem_middleBoundaryCode_of_pairing_cocycle_ne_zero d _ u
    · exact firstBlockWord_mem_middleCocycleCode d _ _ hk'
    · simp [u, wordPairing_firstBlockWord, wordPairing_single_left,
        wordPairing_single_right, repetitionWord]
  · rw [hammingWeight_firstBlockWord_single_right]
    simp [HammingWeight, hammingSupport, repetitionWord]

theorem five_weight_two_witness :
    let z := firstBlockWord (rowOne := Fin 1) (rowTwo := Fin 1) repetitionWord (Pi.single 0 1)
    z ∈ (chainComplex five).middleCycleCode.carrier ∧
    z ∉ (chainComplex five).middleBoundaryCode.carrier ∧ HammingWeight z = 2 :=
  ones_weight_two_witness (Fin 1)

theorem eight_weight_two_witness :
    let z := firstBlockWord (rowOne := Bit) (rowTwo := Bit) repetitionWord (Pi.single 0 1)
    z ∈ (chainComplex eight).middleCycleCode.carrier ∧
    z ∉ (chainComplex eight).middleBoundaryCode.carrier ∧ HammingWeight z = 2 :=
  ones_weight_two_witness Bit

end HGPExperiment.Examples
