/-
Copyright (c) 2026 Kevin Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Zhao
-/
module

public import Mathlib.Data.Finset.Sort
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Group.List.Basic

import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-!
# Finite endpoint partitions for real pulse schedules

A finite collection of real pulse start and finish times admits a sorted common partition.
Every event is a contiguous group of partition intervals, and the interval lengths telescope
to exactly the original duration. This supplies the real-time geometric data used by pulse
segmentation; it makes no hypothesis about equality of quantum evolutions.
-/

@[expose] public section

namespace Giallar.RealPulsePartition

/-- Enumerate the finite set in increasing order, extended by zero outside its valid indices. -/
noncomputable def cut (s : Finset ℝ) (k : ℕ) : ℝ :=
  if hk : k < s.card then s.orderEmbOfFin rfl ⟨k, hk⟩ else 0

/-- The sorted index of a member of a finite endpoint set. -/
noncomputable def index (s : Finset ℝ) (x : s) : ℕ :=
  ((s.orderIsoOfFin rfl).symm x).val

/-- Every endpoint's index is in the enumerated range. -/
theorem index_lt (s : Finset ℝ) (x : s) : index s x < s.card :=
  ((s.orderIsoOfFin rfl).symm x).isLt

/-- Looking up an endpoint at its sorted index recovers that endpoint. -/
theorem cut_index (s : Finset ℝ) (x : s) : cut s (index s x) = x := by
  unfold cut
  rw [dite_eq_left (index_lt s x)]
  exact congrArg Subtype.val ((s.orderIsoOfFin rfl).apply_symm_apply x)

/-- Endpoint enumeration is strictly increasing throughout its finite domain. -/
theorem strictMonoOn_cut (s : Finset ℝ) : StrictMonoOn (cut s) (Set.Iio s.card) := by
  intro i hi j hj hij
  change i < s.card at hi
  change j < s.card at hj
  unfold cut
  rw [dite_eq_left hi, dite_eq_left hj]
  exact (s.orderEmbOfFin rfl).strictMono (show (⟨i, hi⟩ : Fin s.card) < ⟨j, hj⟩ from hij)

/-- Every finite real schedule admits one common sorted cut sequence including all endpoints. -/
theorem exists_partition {E : Type*} [Finite E] (start duration : E → ℝ) :
    ∃ (m : ℕ) (cuts : ℕ → ℝ) (lo hi : E → ℕ),
      StrictMonoOn cuts (Set.Icc 0 m) ∧
      ∀ e, lo e ≤ m ∧ hi e ≤ m ∧ cuts (lo e) = start e ∧
        cuts (hi e) = start e + duration e := by
  classical
  let _ := Fintype.ofFinite E
  let s : Finset ℝ := {0} ∪ Finset.univ.image start ∪
    Finset.univ.image (fun e => start e + duration e)
  have hpos : 0 < s.card := Finset.card_pos.mpr ⟨0, by simp [s]⟩
  have hstart (e : E) : start e ∈ s := by simp [s]
  have hfinish (e : E) : start e + duration e ∈ s := by simp [s]
  let lo : E → ℕ := fun e => index s ⟨start e, hstart e⟩
  let hi : E → ℕ := fun e => index s ⟨start e + duration e, hfinish e⟩
  refine ⟨s.card - 1, cut s, lo, hi, ?_, ?_⟩
  · apply (strictMonoOn_cut s).mono
    intro k hk
    change k < s.card
    obtain ⟨_, hk⟩ := hk
    omega
  · intro e
    have hlo := index_lt s ⟨start e, hstart e⟩
    have hhi := index_lt s ⟨start e + duration e, hfinish e⟩
    refine ⟨by dsimp [lo]; omega, by dsimp [hi]; omega, ?_, ?_⟩
    · exact cut_index s ⟨start e, hstart e⟩
    · exact cut_index s ⟨start e + duration e, hfinish e⟩

/-- A finite list of consecutive interval lengths telescopes to the endpoint difference. -/
theorem sum_range'_sub_length (cuts : ℕ → ℝ) (lo length : ℕ) :
    ((List.range' lo length).map (fun k => cuts (k + 1) - cuts k)).sum =
      cuts (lo + length) - cuts lo := by
  induction length generalizing lo with
  | zero => simp
  | succ n ih =>
    rw [List.range'_succ, List.map_cons, List.sum_cons, ih]
    have heq : lo + 1 + n = lo + (n + 1) := by omega
    rw [heq]
    linarith

/-- The contiguous fragment range has exactly the intended real duration. -/
theorem sum_range'_sub (cuts : ℕ → ℝ) (lo hi : ℕ) (h : lo ≤ hi) :
    ((List.range' lo (hi - lo)).map (fun k => cuts (k + 1) - cuts k)).sum =
      cuts hi - cuts lo := by
  rw [sum_range'_sub_length, Nat.add_sub_cancel' h]

/-- Strictly ordered cuts give every partition interval positive length. -/
theorem interval_length_pos {m : ℕ} {cuts : ℕ → ℝ}
    (hc : StrictMonoOn cuts (Set.Icc 0 m)) {k : ℕ} (hk : k < m) :
    0 < cuts (k + 1) - cuts k := by
  apply sub_pos.mpr
  apply hc ⟨Nat.zero_le _, hk.le⟩ ⟨Nat.zero_le _, by omega⟩
  omega

/-- Positive event duration forces its start index to precede its finish index. -/
theorem start_lt_finish {m : ℕ} {cuts : ℕ → ℝ}
    (hc : StrictMonoOn cuts (Set.Icc 0 m)) {lo hi : ℕ}
    (hlo : lo ≤ m) (hhi : hi ≤ m) (hd : cuts lo < cuts hi) : lo < hi := by
  by_contra h
  have hle : hi ≤ lo := Nat.le_of_not_gt h
  have hm := hc.monotoneOn ⟨Nat.zero_le _, hhi⟩ ⟨Nat.zero_le _, hlo⟩ hle
  exact not_lt_of_ge hm hd

/-- A physical finish-before-start constraint implies the corresponding endpoint index order. -/
theorem finish_le_start {m : ℕ} {cuts : ℕ → ℝ}
    (hc : StrictMonoOn cuts (Set.Icc 0 m)) {hi lo : ℕ}
    (hhi : hi ≤ m) (hlo : lo ≤ m) (ht : cuts hi ≤ cuts lo) : hi ≤ lo := by
  by_contra h
  have hlt : lo < hi := Nat.lt_of_not_ge h
  have hm := hc ⟨Nat.zero_le _, hlo⟩ ⟨Nat.zero_le _, hhi⟩ hlt
  exact not_lt_of_ge ht hm

end Giallar.RealPulsePartition
