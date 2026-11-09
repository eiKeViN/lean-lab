module

public import QuantumInfo.Measurements.POVM

@[expose] public section
noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace E2Base

variable {a X : Type*} [Fintype a] [DecidableEq a] [Fintype X] [DecidableEq X]

/-- The effect of accepting an outcome with its specified soft weight. -/
def testEffect (E : POVM X a) (w : X → ℝ) : HermitianMat a ℂ :=
  ∑ x, w x • E.mats x

/-- Every weight in `[0,1]` gives an effect in the operator interval `[0,I]`. -/
theorem testEffect_bounds (E : POVM X a) (w : X → ℝ)
    (hw0 : ∀ x, 0 ≤ w x) (hw1 : ∀ x, w x ≤ 1) :
    0 ≤ testEffect E w ∧ testEffect E w ≤ 1 := by
  constructor
  · exact Finset.sum_nonneg (fun x _ => smul_nonneg (hw0 x) (E.nonneg x))
  · calc
      testEffect E w ≤ ∑ x, E.mats x := by
        apply Finset.sum_le_sum
        intro x _
        simpa using smul_le_smul_of_nonneg_right (hw1 x) (E.nonneg x)
      _ = 1 := E.normalized

/-- The binary measurement with acceptance outcome `0` and rejection outcome `1`. -/
def binary (E : POVM X a) (w : X → ℝ)
    (hw0 : ∀ x, 0 ≤ w x) (hw1 : ∀ x, w x ≤ 1) : POVM (Fin 2) a where
  mats b := if b = 0 then testEffect E w else 1 - testEffect E w
  nonneg b := by
    split_ifs
    · exact (testEffect_bounds E w hw0 hw1).1
    · exact sub_nonneg.mpr (testEffect_bounds E w hw0 hw1).2
  normalized := by
    simp [Fin.sum_univ_two]

@[simp] theorem binary_zero (E : POVM X a) (w : X → ℝ)
    (hw0 : ∀ x, 0 ≤ w x) (hw1 : ∀ x, w x ≤ 1) :
    (binary E w hw0 hw1).mats 0 = testEffect E w := by
  simp [binary]

@[simp] theorem binary_one (E : POVM X a) (w : X → ℝ)
    (hw0 : ∀ x, 0 ≤ w x) (hw1 : ∀ x, w x ≤ 1) :
    (binary E w hw0 hw1).mats 1 = 1 - testEffect E w := by
  simp [binary]

/-- Acceptance has the weighted Born probability. -/
theorem accept_probability (E : POVM X a) (w : X → ℝ)
    (hw0 : ∀ x, 0 ≤ w x) (hw1 : ∀ x, w x ≤ 1) (ρ : MState a) :
    ((binary E w hw0 hw1).measure ρ 0 : ℝ) =
      ∑ x, w x * (E.measure ρ x : ℝ) := by
  change ⟪(binary E w hw0 hw1).mats 0, ρ.M⟫ = _
  rw [binary_zero, testEffect, sum_inner]
  apply Finset.sum_congr rfl
  intro x _
  change ⟪w x • E.mats x, ρ.M⟫ = w x * ⟪E.mats x, ρ.M⟫
  exact HermitianMat.inner_smul_left _ _ _

/-- Rejection is the complement of the weighted Born probability. -/
theorem reject_probability (E : POVM X a) (w : X → ℝ)
    (hw0 : ∀ x, 0 ≤ w x) (hw1 : ∀ x, w x ≤ 1) (ρ : MState a) :
    ((binary E w hw0 hw1).measure ρ 1 : ℝ) =
      1 - ∑ x, w x * (E.measure ρ x : ℝ) := by
  have h := ((binary E w hw0 hw1).measure ρ).normalized
  rw [Fin.sum_univ_two, accept_probability E w hw0 hw1 ρ] at h
  linarith

end E2Base
