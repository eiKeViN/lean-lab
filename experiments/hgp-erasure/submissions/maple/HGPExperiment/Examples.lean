import HGPExperiment.Parameters

noncomputable section
namespace HGPExperiment.Examples
open QEC.Coding QEC.Coding.HypergraphProduct

/-- A rectangular all-ones parity check; its row dependence is retained. -/
def ones (m n : ℕ) : Matrix (Fin m) (Fin n) (ZMod 2) := fun _ _ => 1

def repetitionData : Data (ZMod 2) (Fin 1) (Fin 2) (Fin 1) (Fin 2) :=
  ⟨ones 1 2, ones 1 2⟩

def dependentData : Data (ZMod 2) (Fin 2) (Fin 2) (Fin 2) (Fin 2) :=
  ⟨ones 2 2, ones 2 2⟩

theorem ones_rank (m n : ℕ) (hm : 0 < m) (hn : 0 < n) : (ones m n).rank = 1 := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  rw [Matrix.rank_eq_finrank_span_cols]
  have he : (ones m n).col = fun _ : Fin n => (fun _ : Fin m => (1 : ZMod 2)) := rfl
  rw [he, Set.range_const]
  apply finrank_span_singleton
  intro hz
  have hz' := congrFun hz ⟨0, hm⟩
  exact one_ne_zero hz'

theorem ones_kernel_dimension (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    Dimension (parityCheckKernelCode (Matrix.toLin' (ones m n))) = n - 1 := by
  have h := dimension_kernelCode_add_rank (ones m n)
  rw [ones_rank m n hm hn, Fintype.card_fin] at h
  omega

private theorem two_bit_bound : ∀ x : Fin 2 → ZMod 2,
    x 0 + x 1 = 0 → x ≠ 0 → 2 ≤ HammingWeight x := by decide

private theorem repeat_nonzero : (fun _ : Fin 2 => (1 : ZMod 2)) ≠ 0 := by decide

private theorem repeat_weight : HammingWeight (fun _ : Fin 2 => (1 : ZMod 2)) = 2 := by decide

theorem ones_repetition_distance (m : ℕ) (hm : 0 < m) :
    extendedMinimumDistance (parityCheckKernelCode (Matrix.toLin' (ones m 2))) = 2 := by
  apply le_antisymm
  · have hmemb : (fun _ : Fin 2 => (1 : ZMod 2)) ∈
        (parityCheckKernelCode (Matrix.toLin' (ones m 2))).carrier := by
      change (ones m 2).mulVec (fun _ => 1) = 0
      ext r
      simp [ones, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    have hh := finitePredicateMinimum_le_of (weight := HammingWeight)
      ⟨hmemb, repeat_nonzero⟩
    simpa only [repeat_weight] using hh
  · apply le_finitePredicateMinimum
    intro x hx
    have hx' : (ones m 2).mulVec x = 0 := hx.1
    have heq := congrFun hx' ⟨0, hm⟩
    have heq' : x 0 + x 1 = 0 := by
      simpa [ones, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using heq
    exact_mod_cast two_bit_bound x heq' hx.2

theorem repetition_input_dimensions :
    Dimension (firstCode repetitionData) = 1 ∧
    Dimension (secondCode repetitionData) = 1 ∧
    Dimension (firstTransposeCode repetitionData) = 0 ∧
    Dimension (secondTransposeCode repetitionData) = 0 := by
  have h := ones_kernel_dimension 1 2 (by decide) (by decide)
  have ht := ones_kernel_dimension 2 1 (by decide) (by decide)
  exact ⟨h, h, ht, ht⟩

theorem dependent_input_dimensions :
    Dimension (firstCode dependentData) = 1 ∧
    Dimension (secondCode dependentData) = 1 ∧
    Dimension (firstTransposeCode dependentData) = 1 ∧
    Dimension (secondTransposeCode dependentData) = 1 := by
  have h := ones_kernel_dimension 2 2 (by decide) (by decide)
  exact ⟨h, h, h, h⟩

theorem repetition_transpose_distance : extendedMinimumDistance (firstTransposeCode repetitionData) = ⊤ := by
  apply (extendedMinimumDistance_eq_top_iff _).2
  apply (Submodule.finrank_eq_zero).1
  simpa only [Dimension_eq_finrank_carrier] using repetition_input_dimensions.2.2.1

theorem repetition_input_minimum : inputDistanceMinimum repetitionData = 2 := by
  have h := ones_repetition_distance 1 (by decide)
  have ht := repetition_transpose_distance
  change min (min _ _) (min _ _) = _
  change min (min (extendedMinimumDistance (firstCode repetitionData))
      (extendedMinimumDistance (firstCode repetitionData)))
    (min (extendedMinimumDistance (firstTransposeCode repetitionData))
      (extendedMinimumDistance (firstTransposeCode repetitionData))) = _
  change min (min (extendedMinimumDistance (parityCheckKernelCode (Matrix.toLin' (ones 1 2))))
      (extendedMinimumDistance (parityCheckKernelCode (Matrix.toLin' (ones 1 2)))))
    (min (extendedMinimumDistance (firstTransposeCode repetitionData))
      (extendedMinimumDistance (firstTransposeCode repetitionData))) = _
  simp [h, ht]

theorem dependent_input_minimum : inputDistanceMinimum dependentData = 2 := by
  have h := ones_repetition_distance 2 (by decide)
  change min (min (extendedMinimumDistance (parityCheckKernelCode (Matrix.toLin' (ones 2 2))))
      (extendedMinimumDistance (parityCheckKernelCode (Matrix.toLin' (ones 2 2)))))
    (min (extendedMinimumDistance (parityCheckKernelCode (Matrix.toLin' (ones 2 2))))
      (extendedMinimumDistance (parityCheckKernelCode (Matrix.toLin' (ones 2 2))))) = _
  simp [h]

theorem repetition_parameters :
    Fintype.card (QubitIndex (Fin 1) (Fin 2) (Fin 1) (Fin 2)) = 5 ∧
    Module.finrank (ZMod 2) (chainComplex repetitionData).middleHomology = 1 ∧
    extendedAlgebraicCSSMinimumDistance (binaryCSSCode repetitionData).xCode
      (binaryCSSCode repetitionData).zCode = 2 := by
  refine ⟨by decide, ?_, ?_⟩
  · rw [HGP.z_dimension, repetition_input_dimensions.1,
      repetition_input_dimensions.2.1, repetition_input_dimensions.2.2.1,
      repetition_input_dimensions.2.2.2]
  · rw [extendedAlgebraicCSSMinimumDistance_eq_inputDistanceMinimum,
      repetition_input_minimum]
    apply Or.inl
    constructor
    · exact (ones_repetition_distance 1 (by decide)).trans repetition_input_minimum.symm
    · change extendedMinimumDistance (parityCheckKernelCode (Matrix.toLin' (ones 1 2))) ≠ ⊤
      rw [ones_repetition_distance 1 (by decide)]
      exact WithTop.coe_ne_top

theorem dependent_parameters :
    Fintype.card (QubitIndex (Fin 2) (Fin 2) (Fin 2) (Fin 2)) = 8 ∧
    Module.finrank (ZMod 2) (chainComplex dependentData).middleHomology = 2 ∧
    extendedAlgebraicCSSMinimumDistance (binaryCSSCode dependentData).xCode
      (binaryCSSCode dependentData).zCode = 2 := by
  refine ⟨by decide, ?_, ?_⟩
  · rw [HGP.z_dimension, dependent_input_dimensions.1,
      dependent_input_dimensions.2.1, dependent_input_dimensions.2.2.1,
      dependent_input_dimensions.2.2.2]
  · rw [extendedAlgebraicCSSMinimumDistance_eq_inputDistanceMinimum,
      dependent_input_minimum]
    apply Or.inl
    constructor
    · exact (ones_repetition_distance 2 (by decide)).trans dependent_input_minimum.symm
    · change extendedMinimumDistance (parityCheckKernelCode (Matrix.toLin' (ones 2 2))) ≠ ⊤
      rw [ones_repetition_distance 2 (by decide)]
      exact WithTop.coe_ne_top

end HGPExperiment.Examples
