/-
Copyright (c) 2026 Kevin Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Zhao
-/
module

public import Mathlib.Basic.NNReal.Basic
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic

/-!
# Earliest schedules with arbitrary nonnegative real times

This is the real-time counterpart of `Giallar.Scheduling`. Starts and durations live in `ℝ≥0`,
so time is not discretized. Events are numbered topologically: every dependency points from a
smaller to a larger index. Resource users must already be ordered by that dependency relation.

## Main results

* `earliest_feasible`: the recursively constructed schedule respects precedence and resources.
* `earliest_le_finite`: every feasible finite real-time schedule is pointwise no earlier.
* `earliest_makespan_le`: the construction minimizes makespan for the fixed resource order.
* `earliest_le_real`: the same minimality statement for ordinary real-valued times.

The real-valued Boolean test is noncomputable. Executable exact-tick checking is provided by
`Giallar.Scheduling.checkSchedule`; the use of real times here makes no numerical-decision claim.
-/

@[expose] public section

open scoped NNReal

namespace Giallar.RealScheduling

/-- Earliest real-valued start times in a topological numbering. -/
noncomputable def earliest (r : ℕ → ℕ → Prop) [DecidableRel r]
    (duration : ℕ → ℝ≥0) (n : ℕ) : ℝ≥0 :=
  Finset.univ.sup fun i : Fin n =>
    if r i n then earliest r duration i + duration i else 0
termination_by n

/-- An earlier dependency has finished at the recursively computed start time. -/
theorem finish_le_earliest (r : ℕ → ℕ → Prop) [DecidableRel r]
    (duration : ℕ → ℝ≥0) {u v : ℕ} (huv : u < v) (hr : r u v) :
    earliest r duration u + duration u ≤ earliest r duration v := by
  rw [earliest.eq_def r duration v]
  simpa [hr] using
    (Finset.le_sup (f := fun i : Fin v =>
      if r i v then earliest r duration i + duration i else 0)
      (Finset.mem_univ (⟨u, huv⟩ : Fin v)))

/-- The earliest construction is pointwise least among all nonnegative real schedules. -/
theorem earliest_le (r : ℕ → ℕ → Prop) [DecidableRel r] (duration t : ℕ → ℝ≥0)
    (ht : ∀ u v, r u v → t u + duration u ≤ t v) (n : ℕ) :
    earliest r duration n ≤ t n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [earliest, Finset.sup_le_iff]
    intro i _
    split_ifs with h
    · exact (add_le_add (ih i i.isLt) le_rfl).trans (ht i n h)
    · exact zero_le

/-- Feasibility of a finite real-time schedule, including exclusive-resource constraints. -/
structure Feasible {n k : ℕ} (r : Fin n → Fin n → Prop)
    (duration : Fin n → ℝ≥0) (resources : Fin n → Finset (Fin k))
    (start : Fin n → ℝ≥0) : Prop where
  /-- Each event has positive duration. -/
  duration_pos : ∀ v, 0 < duration v
  /-- Every dependency completes before its successor starts. -/
  precedence : ∀ u v, r u v → start u + duration u ≤ start v
  /-- Distinct events sharing any exclusive resource have disjoint interiors. -/
  exclusion : ∀ u v, u ≠ v → ¬ Disjoint (resources u) (resources v) →
    start u + duration u ≤ start v ∨ start v + duration v ≤ start u

/-- A logical Boolean reflection of real-time feasibility; it is not a numerical algorithm. -/
noncomputable def checkSchedule {n k : ℕ} (r : Fin n → Fin n → Prop)
    (duration : Fin n → ℝ≥0) (resources : Fin n → Finset (Fin k))
    (start : Fin n → ℝ≥0) : Bool :=
  by classical exact decide (Feasible r duration resources start)

/-- The real-time test reflects exactly its stated feasibility predicate. -/
@[simp]
theorem checkSchedule_eq_true {n k : ℕ} (r : Fin n → Fin n → Prop)
    (duration : Fin n → ℝ≥0) (resources : Fin n → Finset (Fin k))
    (start : Fin n → ℝ≥0) :
    checkSchedule r duration resources start = true ↔ Feasible r duration resources start := by
  simp only [checkSchedule, decide_eq_true_eq]

/-- Ordering every shared-resource pair reduces exclusion to the precedence constraints. -/
theorem feasible_of_ordered_resources {n k : ℕ} (r : Fin n → Fin n → Prop)
    (duration : Fin n → ℝ≥0) (resources : Fin n → Finset (Fin k))
    (start : Fin n → ℝ≥0) (hd : ∀ v, 0 < duration v)
    (hp : ∀ u v, r u v → start u + duration u ≤ start v)
    (hr : ∀ u v, u ≠ v → ¬ Disjoint (resources u) (resources v) → r u v ∨ r v u) :
    Feasible r duration resources start where
  duration_pos := hd
  precedence := hp
  exclusion u v huv huv' := (hr u v huv huv').imp (hp u v) (hp v u)

/-- The real-time earliest schedule is feasible for a fixed topological resource order. -/
theorem earliest_feasible {n k : ℕ} (r : ℕ → ℕ → Prop) [DecidableRel r]
    (duration : ℕ → ℝ≥0) (resources : Fin n → Finset (Fin k))
    (hd : ∀ v : Fin n, 0 < duration v)
    (ho : ∀ u v : Fin n, r u v → u.val < v.val)
    (hr : ∀ u v : Fin n, u ≠ v → ¬ Disjoint (resources u) (resources v) →
      r u v ∨ r v u) :
    Feasible (fun u v : Fin n => r u v) (fun v => duration v) resources
      (fun v => earliest r duration v) := by
  apply feasible_of_ordered_resources _ _ _ _ hd _ hr
  intro u v h
  exact finish_le_earliest r duration (ho u v h) h

/-- Finite competitors need satisfy constraints only among the specified finite events. -/
theorem earliest_le_finite (r : ℕ → ℕ → Prop) [DecidableRel r]
    (duration : ℕ → ℝ≥0) {N : ℕ} (t : Fin N → ℝ≥0)
    (ht : ∀ u v : Fin N, r u v → t u + duration u ≤ t v)
    {n : ℕ} (hn : n < N) : earliest r duration n ≤ t ⟨n, hn⟩ := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [earliest, Finset.sup_le_iff]
    intro i _
    split_ifs with h
    · exact (add_le_add (ih i i.isLt (i.isLt.trans hn)) le_rfl).trans
        (ht ⟨i, i.isLt.trans hn⟩ ⟨n, hn⟩ h)
    · exact zero_le

/-- Latest finishing time, with makespan zero for an empty schedule. -/
noncomputable def makespan {n : ℕ} (duration start : Fin n → ℝ≥0) : ℝ≥0 :=
  Finset.univ.sup fun v => start v + duration v

/-- Pointwise no-later starts imply no-greater makespan over real times. -/
theorem makespan_mono {n : ℕ} (duration s t : Fin n → ℝ≥0) (h : ∀ v, s v ≤ t v) :
    makespan duration s ≤ makespan duration t := by
  apply Finset.sup_le_iff.mpr
  intro v hv
  exact (add_le_add (h v) le_rfl).trans
    (Finset.le_sup (f := fun w => t w + duration w) hv)

/-- The earliest real-time construction minimizes makespan under the chosen precedence order. -/
theorem earliest_makespan_le (r : ℕ → ℕ → Prop) [DecidableRel r]
    (duration : ℕ → ℝ≥0) {N : ℕ} (t : Fin N → ℝ≥0)
    (ht : ∀ u v : Fin N, r u v → t u + duration u ≤ t v) :
    makespan (fun v : Fin N => duration v) (fun v => earliest r duration v) ≤
      makespan (fun v => duration v) t := by
  exact makespan_mono _ _ _ fun v => earliest_le_finite r duration t ht v.isLt

/-- Ordinary nonnegative real times can be supplied without discretization or rounding. -/
theorem earliest_le_real (r : ℕ → ℕ → Prop) [DecidableRel r]
    (duration t : ℕ → ℝ) (hd : ∀ v, 0 ≤ duration v) (ht : ∀ v, 0 ≤ t v)
    (hp : ∀ u v, r u v → t u + duration u ≤ t v) (n : ℕ) :
    (earliest r (fun v => NNReal.mk (duration v) (hd v)) n : ℝ) ≤ t n := by
  have h := earliest_le r (fun v => NNReal.mk (duration v) (hd v)) (fun v => NNReal.mk (t v) (ht v))
    (fun u v huv => hp u v huv) n
  exact h

end Giallar.RealScheduling
