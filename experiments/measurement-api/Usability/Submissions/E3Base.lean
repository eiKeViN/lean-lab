module

public import QuantumInfo.Measurements.POVM

@[expose] public section

noncomputable section

open BigOperators
open scoped RealInnerProductSpace

namespace E3Base

variable {X Y a : Type*} [Fintype X] [Fintype Y] [Fintype a]
  [DecidableEq X] [DecidableEq Y] [DecidableEq a]

/-- Forget the classical labels according to the map `f`. -/
def coarse (E : POVM X a) (f : X → Y) : POVM Y a where
  mats y := ∑ x ∈ Finset.univ.filter (fun x => f x = y), E.mats x
  nonneg y := Finset.sum_nonneg fun x _ => E.nonneg x
  normalized := by
    rw [Finset.sum_fiberwise]
    exact E.normalized

theorem coarse_mats (E : POVM X a) (f : X → Y) (y : Y) :
    (coarse E f).mats y = ∑ x ∈ Finset.univ.filter (fun x => f x = y), E.mats x :=
  rfl

/-- The real-valued probability supplied by the original measurement API. -/
def born (E : POVM X a) (ρ : MState a) (x : X) : ℝ :=
  (E.measure ρ x : ℝ)

theorem born_eq_inner (E : POVM X a) (ρ : MState a) (x : X) :
    born E ρ x = ⟪E.mats x, ρ.M⟫ :=
  rfl

theorem born_eq_re_trace (E : POVM X a) (ρ : MState a) (x : X) :
    born E ρ x = ((E.mats x).mat * ρ.M.mat).trace.re := by
  rw [born_eq_inner, HermitianMat.inner_eq_re_trace]
  rfl

theorem coarse_born (E : POVM X a) (f : X → Y) (ρ : MState a) (y : Y) :
    born (coarse E f) ρ y =
      ∑ x ∈ Finset.univ.filter (fun x => f x = y), born E ρ x := by
  simp only [born_eq_inner, coarse_mats, sum_inner]

/-- Grouping arbitrary real numbers by a finite map contracts their absolute sum. -/
theorem abs_sum_fibers_le (f : X → Y) (u : X → ℝ) :
    (∑ y : Y, |∑ x ∈ Finset.univ.filter (fun x => f x = y), u x|) ≤
      ∑ x : X, |u x| := by
  calc
    _ ≤ ∑ y : Y, ∑ x ∈ Finset.univ.filter (fun x => f x = y), |u x| := by
      apply Finset.sum_le_sum
      intro y _
      exact Finset.abs_sum_le_sum_abs _ _
    _ = _ := Finset.sum_fiberwise Finset.univ f (fun x => |u x|)

/-- Forgetting labels cannot increase the real-valued L1 distance of outcome laws. -/
theorem coarse_measure_l1_le (E : POVM X a) (f : X → Y) (ρ σ : MState a) :
    (∑ y : Y, |born (coarse E f) ρ y - born (coarse E f) σ y|) ≤
      ∑ x : X, |born E ρ x - born E σ x| := by
  simp_rw [coarse_born, ← Finset.sum_sub_distrib]
  exact abs_sum_fibers_le f (fun x => born E ρ x - born E σ x)

end E3Base
