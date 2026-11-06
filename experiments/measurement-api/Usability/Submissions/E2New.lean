module

public import MeasurementAPI

@[expose] public section

open BigOperators
open scoped RealInnerProductSpace
noncomputable section

namespace E2New

variable {X a : Type*} [Fintype X] [Fintype a] [DecidableEq a]

/-- Accept the original reading `x` with probability `w x`. -/
def effect (E : POVM X a) (w : X → ℝ) : HermitianMat a ℂ :=
  ∑ x, w x • E.mats x

/-- Arbitrary weights in `[0,1]` give a legal effect, without any sum condition. -/
theorem effect_bounds (E : POVM X a) (w : X → ℝ)
    (hw : ∀ x, 0 ≤ w x ∧ w x ≤ 1) :
    0 ≤ effect E w ∧ effect E w ≤ 1 := by
  constructor
  · exact Finset.sum_nonneg (fun x _ => smul_nonneg (hw x).1 (E.nonneg x))
  · calc
      effect E w ≤ ∑ x, E.mats x := by
        apply Finset.sum_le_sum
        intro x _
        simpa only [one_smul] using
          smul_le_smul_of_nonneg_right (hw x).2 (E.nonneg x)
      _ = 1 := E.normalized

/-- The soft binary decision, with acceptance labeled by `0 : Fin 2`. -/
def decision (E : POVM X a) (w : X → ℝ)
    (hw : ∀ x, 0 ≤ w x ∧ w x ≤ 1) : POVM (Fin 2) a :=
  POVM.binary (effect E w) (effect_bounds E w hw)

@[simp] theorem decision_zero (E : POVM X a) (w : X → ℝ)
    (hw : ∀ x, 0 ≤ w x ∧ w x ≤ 1) :
    (decision E w hw).mats 0 = effect E w := by
  exact POVM.binary_zero _ _

@[simp] theorem decision_one (E : POVM X a) (w : X → ℝ)
    (hw : ∀ x, 0 ≤ w x ∧ w x ≤ 1) :
    (decision E w hw).mats 1 = 1 - effect E w := by
  simp [decision, POVM.binary]

/-- The Born expectation of the weighted effect is the weighted reading probability. -/
theorem effect_expectation (E : POVM X a) (w : X → ℝ) (ρ : MState a) :
    ρ.exp_val (effect E w) = ∑ x, w x * (E.measure ρ x : ℝ) := by
  simp [effect, MState.exp_val, inner_sum, POVM.measure_apply]

/-- The acceptance probability of the constructed binary POVM. -/
theorem decision_prob_zero (E : POVM X a) (w : X → ℝ)
    (hw : ∀ x, 0 ≤ w x ∧ w x ≤ 1) (ρ : MState a) :
    ((decision E w hw).measure ρ (0 : Fin 2) : ℝ) =
      ∑ x, w x * (E.measure ρ x : ℝ) := by
  rw [POVM.measure_apply, decision_zero, effect_expectation]

/-- The rejection probability of the constructed binary POVM. -/
theorem decision_prob_one (E : POVM X a) (w : X → ℝ)
    (hw : ∀ x, 0 ≤ w x ∧ w x ≤ 1) (ρ : MState a) :
    ((decision E w hw).measure ρ (1 : Fin 2) : ℝ) =
      1 - ∑ x, w x * (E.measure ρ x : ℝ) := by
  rw [POVM.measure_apply, decision_one, MState.exp_val_sub,
    MState.exp_val_one, effect_expectation]

end E2New
