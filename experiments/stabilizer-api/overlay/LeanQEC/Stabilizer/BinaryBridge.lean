import LeanQEC.Stabilizer.Generators

/-!
# Stabilizers and their binary linear representation

The phase-forgetting map is injective on a valid stabilizer group. Package this
fact as an equivalence, so that downstream users can move in both directions
and reuse the ordinary group and linear-algebra APIs.
-/

noncomputable section

namespace StabCode

variable {n : ℕ}

/-- The binary representation, with membership in the code's subspace included. -/
def binaryHom (C : StabCode n) : C.Stabilizer →* Multiplicative C.stabSymplecticSpace where
  toFun s := Multiplicative.ofAdd
    ⟨Pauli_toBinSympPauli (C.toPauli s),
      (C.mem_stabilizerSpace_iff _).mpr ⟨C.toPauli s, C.stabilizer_mem s, rfl⟩⟩
  map_one' := congrArg Multiplicative.ofAdd (Subtype.ext Pauli_toBinSympPauli_one)
  map_mul' s t := congrArg Multiplicative.ofAdd
    (Subtype.ext (Pauli_to_BinSymp_correct (C.toPauli s) (C.toPauli t)))

/-- The task-facing binary vector, with no additive/multiplicative tag to unpack. -/
def toBinary (C : StabCode n) (s : C.Stabilizer) : C.stabSymplecticSpace :=
  Multiplicative.toAdd (C.binaryHom s)

@[simp]
theorem toBinary_coe (C : StabCode n) (s : C.Stabilizer) :
    (C.toBinary s).val = Pauli_toBinSympPauli (C.toPauli s) := rfl

@[simp]
theorem toBinary_one (C : StabCode n) : C.toBinary 1 = 0 :=
  congrArg Multiplicative.toAdd C.binaryHom.map_one

@[simp]
theorem toBinary_mul (C : StabCode n) (s t : C.Stabilizer) :
    C.toBinary (s * t) = C.toBinary s + C.toBinary t :=
  congrArg Multiplicative.toAdd (C.binaryHom.map_mul s t)

theorem binaryHom_injective (C : StabCode n) : Function.Injective C.binaryHom := by
  intro s t h
  apply C.toPauli_injective
  apply phi_injOn C (C.stabilizer_mem s) (C.stabilizer_mem t)
  exact congrArg (fun x : Multiplicative C.stabSymplecticSpace =>
    (Multiplicative.toAdd x).val) h

theorem binaryHom_surjective (C : StabCode n) : Function.Surjective C.binaryHom := by
  intro x
  obtain ⟨s, hs, he⟩ := (C.mem_stabilizerSpace_iff _).mp (Multiplicative.toAdd x).property
  exact ⟨C.ofMem s hs, congrArg Multiplicative.ofAdd (Subtype.ext he)⟩

/-- A binary vector in the stabilizer subspace determines its unique signed stabilizer. -/
def binaryEquiv (C : StabCode n) : C.Stabilizer ≃* Multiplicative C.stabSymplecticSpace :=
  MulEquiv.ofBijective C.binaryHom ⟨C.binaryHom_injective, C.binaryHom_surjective⟩

@[simp]
theorem binaryEquiv_apply_coe (C : StabCode n) (s : C.Stabilizer) :
    (Multiplicative.toAdd (C.binaryEquiv s)).val =
      Pauli_toBinSympPauli (C.toPauli s) := rfl

/-- The same equivalence in additive notation, suitable for linear algebra. -/
def binaryAddEquiv (C : StabCode n) : Additive C.Stabilizer ≃+ C.stabSymplecticSpace :=
  MulEquiv.toAdditiveLeft C.binaryEquiv

instance instStabilizerModule (C : StabCode n) : Module (ZMod 2) (Additive C.Stabilizer) :=
  C.binaryAddEquiv.module (ZMod 2)

/-- The binary bridge preserves the existing additive operations on stabilizers. -/
def binaryLinearEquiv (C : StabCode n) : Additive C.Stabilizer ≃ₗ[ZMod 2]
    C.stabSymplecticSpace := C.binaryAddEquiv.linearEquiv (ZMod 2)

@[simp]
theorem binaryLinearEquiv_apply_coe (C : StabCode n) (s : Additive C.Stabilizer) :
    (C.binaryLinearEquiv s : BinSympPauli n) =
      Pauli_toBinSympPauli (C.toPauli s.toMul) := rfl

/-- Lift a binary stabilizer vector, including its phase, back to the code. -/
def ofBinary (C : StabCode n) (v : C.stabSymplecticSpace) : C.Stabilizer :=
  C.binaryEquiv.symm (Multiplicative.ofAdd v)

@[simp]
theorem toBinary_ofBinary (C : StabCode n) (v : C.stabSymplecticSpace) :
    C.toBinary (C.ofBinary v) = v :=
  congrArg Multiplicative.toAdd (C.binaryEquiv.apply_symm_apply _)

@[simp]
theorem ofBinary_toBinary (C : StabCode n) (s : C.Stabilizer) :
    C.ofBinary (C.toBinary s) = s :=
  C.binaryEquiv.symm_apply_apply s

@[simp]
theorem binaryEquiv_ofBinary (C : StabCode n) (v : C.stabSymplecticSpace) :
    C.binaryEquiv (C.ofBinary v) = Multiplicative.ofAdd v :=
  C.binaryEquiv.apply_symm_apply _

@[simp]
theorem ofBinary_binaryEquiv (C : StabCode n) (s : C.Stabilizer) :
    C.ofBinary (Multiplicative.toAdd (C.binaryEquiv s)) = s :=
  C.binaryEquiv.symm_apply_apply s

/-- Every stabilizer has order dividing two. -/
@[simp]
theorem stabilizer_mul_self (C : StabCode n) (s : C.Stabilizer) : s * s = 1 := by
  have h : (2 : ZMod 2) • Additive.ofMul s = 0 := by
    rw [show (2 : ZMod 2) = 0 by decide, zero_smul]
  rw [two_smul] at h
  exact congrArg Additive.toMul h

namespace Presentation

variable {C : StabCode n} {ι : Type*} [Fintype ι]

/-- Generator coefficients act through a linear map; its kernel records all relations. -/
def coefficientLinearMap (P : C.Presentation ι) :
    (ι → ZMod 2) →ₗ[ZMod 2] Additive C.Stabilizer :=
  Fintype.linearCombination (ZMod 2) (fun i => Additive.ofMul (P.generator i))

@[simp]
theorem coefficientLinearMap_apply (P : C.Presentation ι) (c : ι → ZMod 2) :
    P.coefficientLinearMap c = Additive.ofMul (P.combination c) := by
  rw [coefficientLinearMap, Fintype.linearCombination_apply, combination, ofMul_prod]
  apply Finset.sum_congr rfl
  intro i _
  rcases zmod2_eq_zero_or_one (c i) with h | h <;> simp [h]

@[simp]
theorem combination_zero (P : C.Presentation ι) : P.combination 0 = 1 := by
  apply Additive.ofMul.injective
  simpa only [coefficientLinearMap_apply] using P.coefficientLinearMap.map_zero

@[simp]
theorem combination_add (P : C.Presentation ι) (c d : ι → ZMod 2) :
    P.combination (c + d) = P.combination c * P.combination d := by
  apply Additive.ofMul.injective
  simpa only [coefficientLinearMap_apply] using P.coefficientLinearMap.map_add c d

@[simp]
theorem combination_neg (P : C.Presentation ι) (c : ι → ZMod 2) :
    P.combination (-c) = (P.combination c)⁻¹ := by
  apply Additive.ofMul.injective
  simpa only [coefficientLinearMap_apply] using P.coefficientLinearMap.map_neg c

@[simp]
theorem combination_single [DecidableEq ι] (P : C.Presentation ι) (i : ι) :
    P.combination (Pi.single i 1) = P.generator i := by
  apply Additive.ofMul.injective
  rw [← coefficientLinearMap_apply]
  change Fintype.linearCombination (ZMod 2) (fun j => Additive.ofMul (P.generator j))
    (Pi.single i 1) = _
  simpa only [one_smul] using
    (Fintype.linearCombination_apply_single (ZMod 2)
      (fun j => Additive.ofMul (P.generator j)) i 1)

/-- Generation by the presentation gives coefficient representatives for every stabilizer. -/
theorem combination_surjective (P : C.Presentation ι) : Function.Surjective P.combination := by
  classical
  have h : ∀ s ∈ C.stabs, ∃ c, C.toPauli (P.combination c) = s := by
    rw [← P.generates]
    intro s hs
    induction hs using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact ⟨Pi.single i 1, by simp⟩
    | one => exact ⟨0, by simp⟩
    | mul a b _ _ ha hb =>
      obtain ⟨c, rfl⟩ := ha
      obtain ⟨d, rfl⟩ := hb
      exact ⟨c + d, by rw [P.combination_add, map_mul]⟩
    | inv x _ hx =>
      obtain ⟨c, rfl⟩ := hx
      exact ⟨-c, by rw [P.combination_neg, map_inv]⟩
  intro s
  obtain ⟨c, hc⟩ := h (C.toPauli s) (C.stabilizer_mem s)
  exact ⟨c, C.toPauli_injective hc⟩

theorem coefficientLinearMap_surjective (P : C.Presentation ι) :
    Function.Surjective P.coefficientLinearMap := by
  intro s
  obtain ⟨c, hc⟩ := P.combination_surjective s.toMul
  exact ⟨c, by simp only [coefficientLinearMap_apply, hc]; rfl⟩

@[simp]
theorem range_coefficientLinearMap (P : C.Presentation ι) :
    LinearMap.range P.coefficientLinearMap = ⊤ :=
  LinearMap.range_eq_top.mpr P.coefficientLinearMap_surjective

end Presentation

end StabCode

namespace BinSympMatrix

variable {k n : ℕ}

theorem stabSymplecticSpace_ofBinSympMatrix (B : BinSympMatrix k n)
    (hm : negIdPauli n ∉ B.pauliSubgroup) :
    (StabCode.ofBinSympMatrix B hm).stabSymplecticSpace = B.rowSpace :=
  B.stabSymplecticSpace_eq_rowSpace (B.isCommuting_of_negId_not_mem hm) hm

/-- Check-matrix users can work in the matrix row space directly. -/
def stabilizerRowEquiv (B : BinSympMatrix k n)
    (hm : negIdPauli n ∉ B.pauliSubgroup) :
    Additive (StabCode.ofBinSympMatrix B hm).Stabilizer ≃ₗ[ZMod 2] B.rowSpace :=
  (StabCode.ofBinSympMatrix B hm).binaryLinearEquiv.trans
    (LinearEquiv.ofEq _ _ (B.stabSymplecticSpace_ofBinSympMatrix hm))

/-- The new presentation reuses the original row-product computation. -/
theorem presentation_combination_toPauli (B : BinSympMatrix k n)
    (hm : negIdPauli n ∉ B.pauliSubgroup) (c : Fin k → ZMod 2) :
    (StabCode.ofBinSympMatrix B hm).toPauli ((B.presentation hm).combination c) =
      B.rowProduct (B.isCommuting_of_negId_not_mem hm) c := rfl

/-- Generator selection becomes ordinary binary matrix multiplication. -/
theorem presentation_combination_binaryImage (B : BinSympMatrix k n)
    (hm : negIdPauli n ∉ B.pauliSubgroup) (c : Fin k → ZMod 2) :
    Pauli_toBinSympPauli
      ((StabCode.ofBinSympMatrix B hm).toPauli ((B.presentation hm).combination c)) =
      (B.X.transpose.mulVec c, B.Z.transpose.mulVec c) := by
  rw [B.presentation_combination_toPauli]
  exact B.rowProduct_binaryImage _ c

/-- Every stabilizer is represented by some binary selection of matrix rows. -/
theorem presentation_combination_surjective (B : BinSympMatrix k n)
    (hm : negIdPauli n ∉ B.pauliSubgroup) :
    Function.Surjective (B.presentation hm).combination :=
  (B.presentation hm).combination_surjective

end BinSympMatrix
