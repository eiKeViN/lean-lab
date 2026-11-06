module

public import MeasurementAPI.POVM

@[expose] public section
open Classical BigOperators
noncomputable section

namespace POVM
variable {X a : Type*} [Fintype X] [Fintype a] [DecidableEq a]

/-- Every outcome effect belongs to the operator interval [0, I]. -/
theorem effect_le_one (P : POVM X a) (x : X) : P.mats x ≤ 1 := by
  calc
    P.mats x ≤ ∑ y, P.mats y :=
      Finset.single_le_sum (fun y _ => P.nonneg y) (Finset.mem_univ x)
    _ = 1 := P.normalized

/-- The effect of any finite event is bounded by the identity. -/
theorem sum_mats_le_one (P : POVM X a) (S : Finset X) :
    (∑ x ∈ S, P.mats x) ≤ 1 := by
  calc
    (∑ x ∈ S, P.mats x) ≤ ∑ x, P.mats x :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
        (fun x _ _ => P.nonneg x)
    _ = 1 := P.normalized

end POVM
