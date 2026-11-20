/-
Copyright (c) 2026 Kevin Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Zhao
-/
module

public import Giallar.PulseSchedule
public import Giallar.SchedulePartition
public import Mathlib.Data.List.FinRange

/-!
# Actual rectangular-pulse timelines on an exact clock

For integer start times and durations, each event is split into its active unit-clock intervals.
`tickTimeline` groups these concrete fragments by time. The main theorem derives the target pulse
gates from this timeline using only precedence feasibility and commutation of incomparable
Hamiltonians. The finite segment permutation, grouping, and interval counts are constructed here,
not supplied as correctness assumptions.

The matrices are finite-dimensional. Time is measured in clock ticks, and `ℏ = 1`. There are no
additional drift, crosstalk, dissipation, measurement or feedback terms in this model.
-/

@[expose] public section

namespace Giallar.PulseSchedule

open NormedSpace
open scoped Matrix.Norms.L2Operator

variable {n : ℕ}

/-- The concrete unit-time fragments of one event. -/
def eventTicks (start duration : Fin n → ℕ) (v : Fin n) : List (ℕ × Fin n) :=
  (List.range' (start v) (duration v)).map fun t => (t, v)

/-- The concrete fragments grouped in topological event order. -/
def eventTickBlocks (start duration : Fin n → ℕ) : List (List (ℕ × Fin n)) :=
  (List.finRange n).map (eventTicks start duration)

/-- All concrete fragments, with each event contributing exactly its duration in clock ticks. -/
def allTicks (start duration : Fin n → ℕ) : List (ℕ × Fin n) :=
  (eventTickBlocks start duration).flatten

/-- Every concrete fragment is active at its stored time. -/
@[simp]
theorem mem_allTicks (start duration : Fin n → ℕ) (f : ℕ × Fin n) :
    f ∈ allTicks start duration ↔ start f.2 ≤ f.1 ∧ f.1 < start f.2 + duration f.2 := by
  rcases f with ⟨t, v⟩
  simp [allTicks, eventTickBlocks, eventTicks, List.mem_flatten, List.mem_map]

/-- Every event contributes each of its active clock intervals exactly once. -/
theorem allTicks_nodup (start duration : Fin n → ℕ) : (allTicks start duration).Nodup := by
  change List.Pairwise (fun a b : ℕ × Fin n => a ≠ b)
    (eventTickBlocks start duration).flatten
  apply List.pairwise_flatten.mpr
  constructor
  · intro b hb
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hb
    apply List.Nodup.map (fun a b h => congrArg Prod.fst h)
    exact List.nodup_range'
  · apply List.pairwise_map.mpr
    apply (List.pairwise_lt_finRange n).imp
    intro u v huv a ha b hb h
    obtain ⟨ta, hta, rfl⟩ := List.mem_map.mp ha
    obtain ⟨tb, htb, rfl⟩ := List.mem_map.mp hb
    exact (ne_of_lt huv) (congrArg Prod.snd h)

/-- Chronological pulse intervals, including empty idle intervals up to makespan. -/
def tickTimeline (start duration : Fin n → ℕ) : List (List (ℕ × Fin n)) :=
  partitionBy Prod.fst (List.range (Scheduling.makespan duration start)) (allTicks start duration)

/-- Grouping fragments by time preserves exactly the event fragments. -/
theorem tickTimeline_flatten_perm (start duration : Fin n → ℕ) :
    (tickTimeline start duration).flatten.Perm (allTicks start duration) := by
  apply partitionBy_flatten_perm _ _ _ List.nodup_range
  intro f hf
  have hf' := (mem_allTicks start duration f).mp hf
  have hfinish : start f.2 + duration f.2 ≤ Scheduling.makespan duration start :=
    Finset.le_sup (f := fun v => start v + duration v) (Finset.mem_univ f.2)
  exact List.mem_range.mpr (hf'.2.trans_le hfinish)

/-- The fragments in the actual timeline are nondecreasing in time. -/
theorem tickTimeline_pairwise (start duration : Fin n → ℕ) :
    (tickTimeline start duration).flatten.Pairwise (fun a b => a.1 ≤ b.1) :=
  partitionBy_pairwise Prod.fst _ _ (· ≤ ·) (fun _ => le_rfl) List.pairwise_le_range

private theorem pairwise_of_mem {F : Type*} (r : F → F → Prop) (xs : List F)
    (h : ∀ x ∈ xs, ∀ y ∈ xs, r x y) : xs.Pairwise r := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    exact List.pairwise_cons.mpr ⟨fun y hy => h x (by simp) y (by simp [hy]),
      ih (fun a ha b hb => h a (by simp [ha]) b (by simp [hb]))⟩

/-- No fragment from a predecessor can occur after a fragment from its successor. -/
theorem tickTimeline_respects (r : Fin n → Fin n → Prop) (start duration : Fin n → ℕ)
    (hp : ∀ u v, r u v → start u + duration u ≤ start v) :
    Scheduling.Respects (fun a b : ℕ × Fin n => r a.2 b.2)
      (tickTimeline start duration).flatten := by
  apply (tickTimeline_pairwise start duration).imp_of_mem
  intro a b ha hb hab hba
  have ha' := (mem_allTicks start duration a).mp
    ((tickTimeline_flatten_perm start duration).mem_iff.mp ha)
  have hb' := (mem_allTicks start duration b).mp
    ((tickTimeline_flatten_perm start duration).mem_iff.mp hb)
  have h := hp b.2 a.2 hba
  omega

/-- Topologically numbered event blocks respect every dependency. -/
theorem eventTickBlocks_respects (r : Fin n → Fin n → Prop) (start duration : Fin n → ℕ)
    (ho : ∀ u v, r u v → u < v) :
    Scheduling.Respects (fun a b : ℕ × Fin n => r a.2 b.2)
      (eventTickBlocks start duration).flatten := by
  apply List.pairwise_flatten.mpr
  constructor
  · intro b hb
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hb
    apply pairwise_of_mem
    intro a ha b hb h
    have ha' : a.2 = v := by
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp ha
      rfl
    have hb' : b.2 = v := by
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hb
      rfl
    exact (lt_irrefl v) (ho v v (by simpa [ha', hb'] using h))
  · apply List.pairwise_map.mpr
    apply (List.pairwise_lt_finRange n).imp
    intro u v huv a ha b hb h
    have ha' : a.2 = u := by
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp ha
      rfl
    have hb' : b.2 = v := by
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hb
      rfl
    have h' := ho v u (by simpa [ha', hb'] using h)
    exact (not_lt_of_ge huv.le) h'

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Each unit fragment has the event's Schrödinger generator. -/
noncomputable def tickGenerator (H : Fin n → Operator ι) (f : ℕ × Fin n) : Operator ι :=
  -Complex.I • H f.2

omit [DecidableEq ι] in
/-- Two incomparable event fragments have commuting generators. -/
theorem tickGenerator_commute (r : Fin n → Fin n → Prop) (H : Fin n → Operator ι)
    (hc : ∀ u v, ¬ r u v → ¬ r v u → Commute (H u) (H v))
    (a b : ℕ × Fin n) (hab : ¬ r a.2 b.2) (hba : ¬ r b.2 a.2) :
    Commute (tickGenerator H a) (tickGenerator H b) :=
  ((hc a.2 b.2 hab hba).smul_left (-Complex.I)).smul_right (-Complex.I)

omit [DecidableEq ι] in
/-- Simultaneously active fragments commute, derived from the schedule constraints. -/
theorem tickTimeline_commute (r : Fin n → Fin n → Prop) (H : Fin n → Operator ι)
    (start duration : Fin n → ℕ)
    (hp : ∀ u v, r u v → start u + duration u ≤ start v)
    (hc : ∀ u v, ¬ r u v → ¬ r v u → Commute (H u) (H v)) :
    ∀ b ∈ tickTimeline start duration, (b.map (tickGenerator H)).Pairwise Commute := by
  intro b hb
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hb
  apply List.pairwise_map.mpr
  apply pairwise_of_mem
  intro a ha b hb
  have haM := List.mem_filter.mp ha
  have hbM := List.mem_filter.mp hb
  have hat : a.1 = t := by simpa using haM.2
  have hbt : b.1 = t := by simpa using hbM.2
  have ha' := (mem_allTicks start duration a).mp haM.1
  have hb' := (mem_allTicks start duration b).mp hbM.1
  apply tickGenerator_commute r H hc
  · intro h
    have h' := hp a.2 b.2 h
    omega
  · intro h
    have h' := hp b.2 a.2 h
    omega

omit [DecidableEq ι] in
/-- Every homogeneous event block consists of commuting pieces. -/
theorem eventTickBlocks_commute (H : Fin n → Operator ι) (start duration : Fin n → ℕ) :
    ∀ b ∈ eventTickBlocks start duration, (b.map (tickGenerator H)).Pairwise Commute := by
  intro b hb
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hb
  apply List.pairwise_map.mpr
  apply pairwise_of_mem
  intro a ha b hb
  have ha' : a.2 = v := by
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp ha
    rfl
  have hb' : b.2 = v := by
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hb
    rfl
  simp only [tickGenerator, ha', hb']
  exact Commute.refl _

/-- Grouped unit fragments give exactly the list of full pulse gates. -/
theorem eventTickBlocks_gate_list (H : Fin n → Operator ι) (start duration : Fin n → ℕ) :
    (((eventTickBlocks start duration).map (List.map (tickGenerator H))).map
      fun b => exp b.sum) =
      (List.finRange n).map (fun v => evolution (H v) (duration v)) := by
  unfold eventTickBlocks
  simp only [List.map_map]
  apply List.map_congr_left
  intro v hv
  have hsum : ((eventTicks start duration v).map (tickGenerator H)).sum =
      (duration v : ℂ) • (-Complex.I • H v) := by
    have hm : (eventTicks start duration v).map (tickGenerator H) =
        List.replicate (duration v) (-Complex.I • H v) := by
      simp [eventTicks, List.map_map, Function.comp_def, tickGenerator]
    rw [hm, List.sum_replicate]
    exact (Nat.cast_smul_eq_nsmul ℂ (duration v) (-Complex.I • H v)).symm
  change exp ((eventTicks start duration v).map (tickGenerator H)).sum = _
  rw [hsum]
  rfl

/-- Grouped unit fragments combine to each full pulse gate. -/
theorem eventTickBlocks_evolution (H : Fin n → Operator ι) (start duration : Fin n → ℕ) :
    segmentedEvolution ((eventTickBlocks start duration).map (List.map (tickGenerator H))) =
      ((List.finRange n).map fun v => evolution (H v) (duration v)).prod :=
  congrArg List.prod (eventTickBlocks_gate_list H start duration)

/-- Grouped unit fragments combine to the chronological pulse circuit. -/
theorem chronological_eventTickBlocks_evolution (H : Fin n → Operator ι)
    (start duration : Fin n → ℕ) :
    chronologicalEvolution ((eventTickBlocks start duration).map (List.map (tickGenerator H))) =
      (((List.finRange n).map fun v => evolution (H v) (duration v)).reverse).prod :=
  congrArg (fun l => l.reverse.prod) (eventTickBlocks_gate_list H start duration)

/-- The actual integer-clock pulse timeline realizes the target circuit in topological order. -/
theorem tickTimeline_evolution (r : Fin n → Fin n → Prop) (H : Fin n → Operator ι)
    (start duration : Fin n → ℕ) (ho : ∀ u v, r u v → u < v)
    (hp : ∀ u v, r u v → start u + duration u ≤ start v)
    (hc : ∀ u v, ¬ r u v → ¬ r v u → Commute (H u) (H v)) :
    segmentedEvolution ((tickTimeline start duration).map (List.map (tickGenerator H))) =
      ((List.finRange n).map fun v => evolution (H v) (duration v)).prod := by
  rw [← eventTickBlocks_evolution H start duration]
  apply segmented_evolution_eq (fun a b : ℕ × Fin n => r a.2 b.2)
    (fun a h => (lt_irrefl a.2) (ho _ _ h)) (tickGenerator H)
    (tickGenerator_commute r H hc) (tickTimeline start duration)
    (eventTickBlocks start duration)
    (tickTimeline_flatten_perm start duration)
    (tickTimeline_respects r start duration hp)
    (eventTickBlocks_respects r start duration ho)
    (tickTimeline_commute r H start duration hp hc)
    (eventTickBlocks_commute H start duration)

/-- The physical tick timeline equals the target circuit in chronological operator convention. -/
theorem chronological_tickTimeline_evolution (r : Fin n → Fin n → Prop)
    (H : Fin n → Operator ι) (start duration : Fin n → ℕ)
    (ho : ∀ u v, r u v → u < v)
    (hp : ∀ u v, r u v → start u + duration u ≤ start v)
    (hc : ∀ u v, ¬ r u v → ¬ r v u → Commute (H u) (H v)) :
    chronologicalEvolution ((tickTimeline start duration).map (List.map (tickGenerator H))) =
      (((List.finRange n).map fun v => evolution (H v) (duration v)).reverse).prod := by
  rw [← chronological_eventTickBlocks_evolution H start duration]
  apply chronological_segmented_evolution_eq (fun a b : ℕ × Fin n => r a.2 b.2)
    (fun a h => (lt_irrefl a.2) (ho _ _ h)) (tickGenerator H)
    (tickGenerator_commute r H hc) (tickTimeline start duration)
    (eventTickBlocks start duration)
    (tickTimeline_flatten_perm start duration)
    (tickTimeline_respects r start duration hp)
    (eventTickBlocks_respects r start duration ho)
    (tickTimeline_commute r H start duration hp hc)
    (eventTickBlocks_commute H start duration)

end Giallar.PulseSchedule
