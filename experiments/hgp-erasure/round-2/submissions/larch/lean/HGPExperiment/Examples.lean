import HGPExperiment.Parameters
import HGPExperiment.Erasure

noncomputable section
namespace HGPExperiment
open QEC.Coding QEC.Coding.HypergraphProduct

/-- Both input checks are the one-row repetition parity check. -/
def repetitionHGP : Data (ZMod 2) (Fin 1) (Fin 2) (Fin 1) (Fin 2) :=
  ⟨fun _ _ => 1, fun _ _ => 1⟩
/-- Both input checks have two identical all-one rows. -/
def dependentHGP : Data (ZMod 2) (Fin 2) (Fin 2) (Fin 2) (Fin 2) :=
  ⟨fun _ _ => 1, fun _ _ => 1⟩

def repetitionWord : Fin 2 → ZMod 2 := fun _ => 1

theorem repetitionWord_weight : HammingWeight repetitionWord = 2 := by decide

theorem repetitionWord_ne_zero : repetitionWord ≠ 0 := by decide

/-- An all-one matrix with nonempty row and column sets has rank one. -/
theorem allOne_rank {R C : Type} [Fintype R] [DecidableEq R]
    [Fintype C] [DecidableEq C] [Nonempty R] [Nonempty C] :
    Matrix.rank (fun _ : R => fun _ : C => (1 : ZMod 2)) = 1 := by
  classical
  let M : Matrix R C (ZMod 2) := fun _ _ => 1
  have hle : M.rank ≤ 1 := by
    convert Matrix.rank_vecMulVec_le (fun _ : R => (1 : ZMod 2))
      (fun _ : C => 1) using 1
    congr 1
  have hpos : 0 < M.rank := by
    rw [Matrix.rank, Module.finrank_pos_iff_exists_ne_zero]
    let c : C := Classical.arbitrary C
    refine ⟨⟨M.mulVecLin (Pi.single c 1), LinearMap.mem_range_self _ _⟩, ?_⟩
    intro h
    have heq := congrFun (congrArg Subtype.val h) (Classical.arbitrary R)
    change (∑ j : C, (1 : ZMod 2) * (Pi.single c 1 : C → ZMod 2) j) = 0 at heq
    simpa using heq
  change M.rank = 1
  omega

theorem allOne_kernel_distance {R : Type} [Fintype R] [DecidableEq R] [Nonempty R] :
    extendedMinimumDistance (parityCheckKernelCode
      (Matrix.toLin' (fun _ : R => fun _ : Fin 2 => (1 : ZMod 2)))) = 2 := by
  classical
  apply le_antisymm
  · have hv : repetitionWord ∈ (parityCheckKernelCode
        (Matrix.toLin' (fun _ : R => fun _ : Fin 2 => (1 : ZMod 2)))).carrier := by
      rw [mem_parityCheckKernelCode]
      ext r
      change (∑ j : Fin 2, (1 : ZMod 2) * repetitionWord j) = 0
      decide
    calc
      _ ≤ (HammingWeight repetitionWord : WithTop ℕ) :=
        finitePredicateMinimum_le_of (weight := HammingWeight) ⟨hv, repetitionWord_ne_zero⟩
      _ = 2 := by rw [repetitionWord_weight]; rfl
  · apply le_finitePredicateMinimum
    intro v hv
    have heq : v 0 + v 1 = 0 := by
      have h := congrFun ((mem_parityCheckKernelCode _ v).mp hv.1)
        (Classical.arbitrary R)
      change (∑ j : Fin 2, (1 : ZMod 2) * v j) = 0 at h
      simpa [Fin.sum_univ_two] using h
    have hweight : HammingWeight v = 2 := by
      exact (by decide : ∀ v : Fin 2 → ZMod 2,
        v 0 + v 1 = 0 → v ≠ 0 → HammingWeight v = 2) v heq hv.2
    exact le_of_eq (congrArg (fun n : ℕ => (n : WithTop ℕ)) hweight.symm)

theorem repetition_input_dimensions :
    Dimension (firstCode repetitionHGP) = 1 ∧
    Dimension (secondCode repetitionHGP) = 1 ∧
    Dimension (firstTransposeCode repetitionHGP) = 0 ∧
    Dimension (secondTransposeCode repetitionHGP) = 0 := by
  have h := dimension_kernelCode_add_rank repetitionHGP.first
  have ht := dimension_kernelCode_add_rank repetitionHGP.first.transpose
  have hr : repetitionHGP.first.rank = 1 := allOne_rank (R := Fin 1) (C := Fin 2)
  have hrt : repetitionHGP.first.transpose.rank = 1 := allOne_rank (R := Fin 2) (C := Fin 1)
  simp only [Fintype.card_fin, hr, hrt] at h ht
  change Dimension (parityCheckKernelCode (Matrix.toLin' repetitionHGP.first)) = 1 ∧
    Dimension (parityCheckKernelCode (Matrix.toLin' repetitionHGP.first)) = 1 ∧
    Dimension (parityCheckKernelCode (Matrix.toLin' repetitionHGP.first.transpose)) = 0 ∧
    Dimension (parityCheckKernelCode (Matrix.toLin' repetitionHGP.first.transpose)) = 0
  omega

theorem dependent_input_dimensions :
    Dimension (firstCode dependentHGP) = 1 ∧
    Dimension (secondCode dependentHGP) = 1 ∧
    Dimension (firstTransposeCode dependentHGP) = 1 ∧
    Dimension (secondTransposeCode dependentHGP) = 1 := by
  have h := dimension_kernelCode_add_rank dependentHGP.first
  have hr : dependentHGP.first.rank = 1 := allOne_rank (R := Fin 2) (C := Fin 2)
  simp only [Fintype.card_fin, hr] at h
  change Dimension (parityCheckKernelCode (Matrix.toLin' dependentHGP.first)) = 1 ∧
    Dimension (parityCheckKernelCode (Matrix.toLin' dependentHGP.first)) = 1 ∧
    Dimension (parityCheckKernelCode (Matrix.toLin' dependentHGP.first)) = 1 ∧
    Dimension (parityCheckKernelCode (Matrix.toLin' dependentHGP.first)) = 1
  omega

/-- The transpose kernel of the one-row check is actually the zero code. -/
theorem repetition_transpose_distance :
    extendedMinimumDistance (firstTransposeCode repetitionHGP) = ⊤ := by
  apply (extendedMinimumDistance_eq_top_iff _).2
  apply Submodule.finrank_eq_zero.mp
  exact repetition_input_dimensions.2.2.1

theorem repetition_input_distance : inputDistanceMinimum repetitionHGP = 2 := by
  have h : extendedMinimumDistance (firstCode repetitionHGP) = 2 :=
    allOne_kernel_distance
  have ht := repetition_transpose_distance
  simpa [inputDistanceMinimum, show secondCode repetitionHGP = firstCode repetitionHGP from rfl,
    show secondTransposeCode repetitionHGP = firstTransposeCode repetitionHGP from rfl, h, ht]

theorem dependent_input_distance : inputDistanceMinimum dependentHGP = 2 := by
  have h : extendedMinimumDistance (firstCode dependentHGP) = 2 := allOne_kernel_distance
  simpa [inputDistanceMinimum, show secondCode dependentHGP = firstCode dependentHGP from rfl,
    show firstTransposeCode dependentHGP = firstCode dependentHGP from rfl,
    show secondTransposeCode dependentHGP = firstCode dependentHGP from rfl, h]

/-- Displayed weight-two Z representative on one column of the first block. -/
def exampleZ {R : Type} : Word (ZMod 2) (QubitIndex R (Fin 2) R (Fin 2)) :=
  firstBlockWord repetitionWord (Pi.single 0 1)
/-- Displayed weight-two X representative on one row of the first block. -/
def exampleX {R : Type} : Word (ZMod 2) (QubitIndex R (Fin 2) R (Fin 2)) :=
  firstBlockWord (Pi.single 0 1) repetitionWord

theorem example_representatives {R : Type} [Fintype R] [DecidableEq R]
    (H : Data (ZMod 2) R (Fin 2) R (Fin 2))
    (hfirst : H.first = fun _ _ => 1) (hsecond : H.second = fun _ _ => 1) :
    IsCSSLogical (binaryCSSCode H).xCode (binaryCSSCode H).zCode exampleZ ∧
    IsCSSLogical (binaryCSSCode H).xCode (binaryCSSCode H).zCode exampleX ∧
    HammingWeight (exampleZ (R := R)) = 2 ∧ HammingWeight (exampleX (R := R)) = 2 := by
  have hzinput : repetitionWord ∈ (firstCode H).carrier := by
    rw [mem_firstCode_iff]
    ext r
    rw [hfirst]
    change (∑ j : Fin 2, (1 : ZMod 2) * repetitionWord j) = 0
    decide
  have hxinput : repetitionWord ∈ (secondCode H).carrier := by
    rw [mem_secondCode_iff]
    ext r
    rw [hsecond]
    change (∑ j : Fin 2, (1 : ZMod 2) * repetitionWord j) = 0
    decide
  have hzcycle := firstBlockWord_mem_middleCycleCode H repetitionWord (Pi.single 0 1) hzinput
  have hxcycle := firstBlockWord_mem_middleCocycleCode H (Pi.single 0 1) repetitionWord hxinput
  have hpair : wordPairing (exampleX (R := R)) (exampleZ (R := R)) ≠ 0 := by
    rw [exampleX, exampleZ, wordPairing_firstBlockWord,
      wordPairing_single_left, wordPairing_single_right]
    decide
  have hznot := not_mem_middleBoundaryCode_of_pairing_cocycle_ne_zero H
    exampleZ exampleX hxcycle hpair
  have hxnot := not_mem_firstCoboundaryCheckCode_of_pairing_cycle_ne_zero H
    exampleX exampleZ hzcycle hpair
  refine ⟨Or.inr ⟨?_, hznot⟩, Or.inl ⟨?_, hxnot⟩, ?_, ?_⟩
  · simpa only [binaryCSSCode_xCode,
      ChainComplexData.firstCoboundaryCheckCode_dual_carrier_eq_middleCycleCode, exampleZ] using hzcycle
  · simpa only [binaryCSSCode_zCode,
      ChainComplexData.middleBoundaryCode_dual_carrier_eq_middleCocycleCode, exampleX] using hxcycle
  · rw [exampleZ, hammingWeight_firstBlockWord_single_right, repetitionWord_weight]
  · rw [exampleX, hammingWeight_firstBlockWord_single_left, repetitionWord_weight]

theorem repetition_parameters :
    Fintype.card (QubitIndex (Fin 1) (Fin 2) (Fin 1) (Fin 2)) = 5 ∧
    Module.finrank (ZMod 2) (ZLogical repetitionHGP) = 1 ∧
    Module.finrank (ZMod 2) (XLogical repetitionHGP) = 1 ∧ hgpDistance repetitionHGP = 2 := by
  classical
  rcases repetition_input_dimensions with ⟨h₁,h₂,ht₁,ht₂⟩
  have hz := zLogical_dimension repetitionHGP
  have hx := xLogical_dimension repetitionHGP
  rw [h₁,h₂,ht₁,ht₂] at hz hx
  have hlo := hgp_distance_lower repetitionHGP
  rw [repetition_input_distance] at hlo
  have reps := example_representatives repetitionHGP rfl rfl
  have hhi : hgpDistance repetitionHGP ≤ 2 := by
    have h := finitePredicateMinimum_le_of (weight := HammingWeight) reps.1
    rw [reps.2.2.1] at h
    exact h
  exact ⟨by decide, by simpa using hz, by simpa using hx, le_antisymm hhi hlo⟩

theorem dependent_parameters :
    Fintype.card (QubitIndex (Fin 2) (Fin 2) (Fin 2) (Fin 2)) = 8 ∧
    Module.finrank (ZMod 2) (ZLogical dependentHGP) = 2 ∧
    Module.finrank (ZMod 2) (XLogical dependentHGP) = 2 ∧ hgpDistance dependentHGP = 2 := by
  classical
  rcases dependent_input_dimensions with ⟨h₁,h₂,ht₁,ht₂⟩
  have hz := zLogical_dimension dependentHGP
  have hx := xLogical_dimension dependentHGP
  rw [h₁,h₂,ht₁,ht₂] at hz hx
  have hlo := hgp_distance_lower dependentHGP
  rw [dependent_input_distance] at hlo
  have reps := example_representatives dependentHGP rfl rfl
  have hhi : hgpDistance dependentHGP ≤ 2 := by
    have h := finitePredicateMinimum_le_of (weight := HammingWeight) reps.1
    rw [reps.2.2.1] at h
    exact h
  exact ⟨by decide, by simpa using hz, by simpa using hx, le_antisymm hhi hlo⟩

/-- One-column shortening of the repetition kernel is zero. -/
theorem repetition_shortened_dimension :
    Module.finrank (ZMod 2) (cycles (restrictColumns repetitionHGP.first ({0} : Set (Fin 2)))) = 0 := by
  classical
  haveI : Nonempty ({0} : Set (Fin 2)) := ⟨⟨0, by simp⟩⟩
  have h := finrank_cycles_add_rank (restrictColumns repetitionHGP.first ({0} : Set (Fin 2)))
  have hr : (restrictColumns repetitionHGP.first ({0} : Set (Fin 2))).rank = 1 :=
    allOne_rank (R := Fin 1) (C := ({0} : Set (Fin 2)))
  have hc : Fintype.card ({0} : Set (Fin 2)) = 1 := by simp
  omega

/-- Projection of the repetition kernel onto one coordinate has dimension one. -/
theorem repetition_projected_dimension :
    Module.finrank (ZMod 2)
      ((cycles repetitionHGP.first).map (restrictCoords ({0} : Set (Fin 2)))) = 1 := by
  classical
  have he : (cycles repetitionHGP.first).map (restrictCoords ({0} : Set (Fin 2))) = ⊤ := by
    apply top_unique
    intro v _
    refine ⟨fun _ => v ⟨0, by simp⟩, ?_, ?_⟩
    · change repetitionHGP.first.mulVecLin (fun _ => v ⟨0, by simp⟩) = 0
      ext r
      change (∑ j : Fin 2, (1 : ZMod 2) * v ⟨0, by simp⟩) = 0
      simp [Fin.sum_univ_two, CharTwo.add_self_eq_zero]
    · ext i
      have hi : i = ⟨0, by simp⟩ := Subtype.ext (by simpa using i.property)
      subst i
      rfl
  rw [he, finrank_top, Module.finrank_fintype_fun_eq_card]
  simp

theorem repetition_kernel_dimension :
    Module.finrank (ZMod 2) (cycles repetitionHGP.second) = 1 := by
  change Module.finrank (ZMod 2) (secondCode repetitionHGP).carrier = 1
  rw [← Dimension_eq_finrank_carrier]
  exact repetition_input_dimensions.2.1

theorem dependent_kernel_dimension :
    Module.finrank (ZMod 2) (cycles dependentHGP.second) = 1 := by
  change Module.finrank (ZMod 2) (secondCode dependentHGP).carrier = 1
  rw [← Dimension_eq_finrank_carrier]
  exact dependent_input_dimensions.2.1

/-- Restriction to the full column set preserves the kernel dimension. -/
theorem dependent_shortened_dimension :
    Module.finrank (ZMod 2) (cycles (restrictColumns dependentHGP.first Set.univ)) = 1 := by
  classical
  haveI : Nonempty (Set.univ : Set (Fin 2)) := ⟨⟨0, Set.mem_univ 0⟩⟩
  have h := finrank_cycles_add_rank (restrictColumns dependentHGP.first Set.univ)
  have hr : (restrictColumns dependentHGP.first Set.univ).rank = 1 :=
    allOne_rank (R := Fin 2) (C := (Set.univ : Set (Fin 2)))
  have hc : Fintype.card (Set.univ : Set (Fin 2)) = 2 := by simp
  omega

theorem dependent_projected_dimension :
    Module.finrank (ZMod 2)
      ((cycles dependentHGP.first).map (restrictCoords (Set.univ : Set (Fin 2)))) = 1 := by
  classical
  have hi : Function.Injective (restrictCoords (F := ZMod 2) (Set.univ : Set (Fin 2))) := by
    intro v w h
    ext i
    exact congrFun h ⟨i, Set.mem_univ i⟩
  rw [(Submodule.equivMapOfInjective (cycles dependentHGP.first) _ hi).finrank_eq.symm]
  change Module.finrank (ZMod 2) (firstCode dependentHGP).carrier = 1
  rw [← Dimension_eq_finrank_carrier]
  exact dependent_input_dimensions.1


end HGPExperiment
