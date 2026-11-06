module

public import MeasurementAPI

@[expose] public section

open BigOperators

noncomputable section

namespace E1New

variable {a X Y : Type*} [Fintype a] [DecidableEq a] [Fintype X] [Fintype Y]

/-- Relabel the outcomes using a bijection, without changing the effects. -/
def rename (E : POVM X a) (e : X ≃ Y) : POVM Y a where
  mats y := E.mats (e.symm y)
  nonneg y := E.nonneg (e.symm y)
  normalized := by
    rw [e.symm.sum_comp E.mats, E.normalized]

/-- The renamed effect at `y` is the original effect at its inverse image. -/
@[simp] theorem rename_mats (E : POVM X a) (e : X ≃ Y) (y : Y) :
    (rename E e).mats y = E.mats (e.symm y) := rfl

/-- Renaming preserves the probability of each corresponding outcome. -/
theorem rename_probability (E : POVM X a) (e : X ≃ Y) (ρ : MState a) (x : X) :
    (rename E e).measure ρ (e x) = E.measure ρ x := by
  apply Subtype.ext
  simp [POVM.measure_apply]

/-- Renaming by the inverse equivalence recovers the original POVM. -/
@[simp] theorem rename_inverse (E : POVM X a) (e : X ≃ Y) :
    rename (rename E e) e.symm = E := by
  apply POVM.ext
  intro x
  simp

end E1New
