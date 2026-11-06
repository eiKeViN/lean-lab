module

public import MeasurementAPI.POVM
public import Mathlib.Data.Fintype.BigOperators

@[expose] public section
open Classical BigOperators
noncomputable section

namespace POVM
variable {X Y a : Type*} [Fintype X] [Fintype Y] [Fintype a] [DecidableEq a]

/-- Forgetting the second component of an outcome gives the first marginal effect. -/
@[simp] theorem coarsegrain_fst_mats (P : POVM (X × Y) a) (x : X) :
    (P.coarsegrain Prod.fst).mats x = ∑ y, P.mats (x, y) := by
  simp only [coarsegrain_mats, Finset.sum_filter, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  simp

/-- Forgetting the first component gives the second marginal effect. -/
@[simp] theorem coarsegrain_snd_mats (P : POVM (X × Y) a) (y : Y) :
    (P.coarsegrain Prod.snd).mats y = ∑ x, P.mats (x, y) := by
  simp [coarsegrain_mats, Finset.sum_filter, Fintype.sum_prod_type]

end POVM
