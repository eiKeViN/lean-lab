/-
Copyright (c) 2026 Kevin Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Zhao
-/
module

public import Giallar.RealPulsePartition
public import Giallar.WeightedPulseSchedule

import Mathlib.Tactic.Linarith

/-!
# Rectangular pulses with arbitrary real endpoints

A finite sorted partition containing every real start and finish time is constructed by
`endpointPartition`. `realTimelineEvolution` splits actual pulses at these endpoints and composes
the constant-interval matrix exponentials chronologically. No equality of evolutions is included
in a partition's data.

`realTimelineEvolution_eq` proves that every feasible schedule with commuting incomparable
Hamiltonians realizes the target gate circuit. Endpoint-index ordering and interval duration sums
are derived from the actual real schedule. Hermiticity is unnecessary for the algebraic identity;
for physical unitary evolution the input Hamiltonians are Hermitian.

## References

The accompanying `Specification.md`, section E3, gives the continuous-time rectangular model.
-/

@[expose] public section

namespace Giallar.PulseSchedule

open NormedSpace
open scoped Matrix.Norms.L2Operator

variable {n : ℕ}

/-- A sorted common partition containing all event start and finish times. -/
structure EndpointPartition (start duration : Fin n → ℝ) where
  /-- Number of intervals between the cuts. -/
  intervals : ℕ
  /-- Cut times, with values outside `0,...,intervals` ignored. -/
  cuts : ℕ → ℝ
  /-- Index of each event's first cut. -/
  lo : Fin n → ℕ
  /-- Index of each event's last cut. -/
  hi : Fin n → ℕ
  /-- Distinct valid cuts are strictly ordered. -/
  mono : StrictMonoOn cuts (Set.Icc 0 intervals)
  /-- Start indices are valid. -/
  lo_le : ∀ v, lo v ≤ intervals
  /-- Finish indices are valid. -/
  hi_le : ∀ v, hi v ≤ intervals
  /-- Looking up the first cut gives the actual start time. -/
  cut_lo : ∀ v, cuts (lo v) = start v
  /-- Looking up the last cut gives the actual finish time. -/
  cut_hi : ∀ v, cuts (hi v) = start v + duration v

/-- Sorted endpoint partitions exist for every finite real schedule. -/
theorem nonempty_endpointPartition (start duration : Fin n → ℝ) :
    Nonempty (EndpointPartition start duration) := by
  obtain ⟨m, cuts, lo, hi, hc, he⟩ := RealPulsePartition.exists_partition start duration
  exact ⟨⟨m, cuts, lo, hi, hc, fun v => (he v).1, fun v => (he v).2.1,
    fun v => (he v).2.2.1, fun v => (he v).2.2.2⟩⟩

/-- A chosen finite endpoint partition; all choices give the same evolution by the main theorem. -/
noncomputable def endpointPartition (start duration : Fin n → ℝ) :
    EndpointPartition start duration :=
  Classical.choice (nonempty_endpointPartition start duration)

/-- Number of partition intervals occupied by one event. -/
def EndpointPartition.count {start duration : Fin n → ℝ}
    (p : EndpointPartition start duration) (v : Fin n) : ℕ := p.hi v - p.lo v

/-- Length of one partition interval. -/
def EndpointPartition.delta {start duration : Fin n → ℝ}
    (p : EndpointPartition start duration) (k : ℕ) : ℝ := p.cuts (k + 1) - p.cuts k

/-- Positive pulse duration implies a nonempty contiguous interval range. -/
theorem EndpointPartition.lo_lt_hi {start duration : Fin n → ℝ}
    (p : EndpointPartition start duration) (hd : ∀ v, 0 < duration v) (v : Fin n) :
    p.lo v < p.hi v := by
  apply RealPulsePartition.start_lt_finish p.mono (p.lo_le v) (p.hi_le v)
  rw [p.cut_lo, p.cut_hi]
  linarith [hd v]

/-- Physical precedence implies precedence of the event interval ranges. -/
theorem EndpointPartition.precedence {start duration : Fin n → ℝ}
    (p : EndpointPartition start duration) (hd : ∀ v, 0 < duration v)
    (r : Fin n → Fin n → Prop)
    (hp : ∀ u v, r u v → start u + duration u ≤ start v)
    (u v : Fin n) (huv : r u v) : p.lo u + p.count u ≤ p.lo v := by
  rw [count, Nat.add_sub_cancel' (p.lo_lt_hi hd u).le]
  apply RealPulsePartition.finish_le_start p.mono (p.hi_le u) (p.lo_le v)
  simpa only [p.cut_hi, p.cut_lo] using hp u v huv

/-- The partition interval lengths sum exactly to each event's real duration. -/
theorem EndpointPartition.duration_sum {start duration : Fin n → ℝ}
    (p : EndpointPartition start duration) (hd : ∀ v, 0 < duration v) (v : Fin n) :
    ((List.range' (p.lo v) (p.count v)).map p.delta).sum = duration v := by
  unfold count delta
  rw [RealPulsePartition.sum_range'_sub p.cuts (p.lo v) (p.hi v) (p.lo_lt_hi hd v).le,
    p.cut_hi, p.cut_lo]
  ring

/-- Every physically used partition interval has positive real length. -/
theorem EndpointPartition.delta_pos {start duration : Fin n → ℝ}
    (p : EndpointPartition start duration) {k : ℕ} (hk : k < p.intervals) :
    0 < p.delta k :=
  RealPulsePartition.interval_length_pos p.mono hk

/-- A generated interval/event pair is active exactly when the entire interval is contained in
that event's real start/finish interval. -/
theorem EndpointPartition.active_iff {start duration : Fin n → ℝ}
    (p : EndpointPartition start duration) (hd : ∀ v, 0 < duration v)
    {k : ℕ} (hk : k < p.intervals) (v : Fin n) :
    (k, v) ∈ allTicks p.lo p.count ↔
      start v ≤ p.cuts k ∧ p.cuts (k + 1) ≤ start v + duration v := by
  rw [mem_allTicks]
  have hcount : p.lo v + p.count v = p.hi v :=
    Nat.add_sub_cancel' (p.lo_lt_hi hd v).le
  rw [hcount, ← p.cut_hi v, ← p.cut_lo v]
  constructor
  · intro h
    exact ⟨p.mono.monotoneOn ⟨Nat.zero_le _, p.lo_le v⟩ ⟨Nat.zero_le _, hk.le⟩ h.1,
      p.mono.monotoneOn ⟨Nat.zero_le _, by omega⟩ ⟨Nat.zero_le _, p.hi_le v⟩
        (by omega)⟩
  · intro h
    have hlo := RealPulsePartition.finish_le_start p.mono (p.lo_le v) hk.le h.1
    have hhi := RealPulsePartition.finish_le_start p.mono (show k + 1 ≤ p.intervals by omega)
      (p.hi_le v) h.2
    exact ⟨hlo, by omega⟩

/-- Throughout each half-open partition interval, generated fragments coincide exactly with the
physical active-event predicate `start ≤ t < finish`. -/
theorem EndpointPartition.active_at {start duration : Fin n → ℝ}
    (p : EndpointPartition start duration) (hd : ∀ v, 0 < duration v)
    {k : ℕ} (hk : k < p.intervals) (v : Fin n) (t : ℝ)
    (hlt : p.cuts k ≤ t) (htr : t < p.cuts (k + 1)) :
    (k, v) ∈ allTicks p.lo p.count ↔ start v ≤ t ∧ t < start v + duration v := by
  constructor
  · intro h
    have ha := (p.active_iff hd hk v).mp h
    exact ⟨ha.1.trans hlt, htr.trans_le ha.2⟩
  · intro h
    have hlo : p.lo v ≤ k := by
      by_contra h'
      have hi : k + 1 ≤ p.lo v := by omega
      have hm := p.mono.monotoneOn ⟨Nat.zero_le _, by omega⟩
        ⟨Nat.zero_le _, p.lo_le v⟩ hi
      rw [p.cut_lo] at hm
      linarith
    have hhi : k < p.hi v := by
      by_contra h'
      have hi : p.hi v ≤ k := by omega
      have hm := p.mono.monotoneOn ⟨Nat.zero_le _, p.hi_le v⟩
        ⟨Nat.zero_le _, hk.le⟩ hi
      rw [p.cut_hi] at hm
      linarith
    apply (mem_allTicks p.lo p.count (k, v)).mpr
    exact ⟨hlo, by simpa only [EndpointPartition.count,
      Nat.add_sub_cancel' (p.lo_lt_hi hd v).le] using hhi⟩

/-- Every fragment constructed from a positive-duration event has positive real length. -/
theorem EndpointPartition.fragment_delta_pos {start duration : Fin n → ℝ}
    (p : EndpointPartition start duration) (hd : ∀ v, 0 < duration v)
    (f : ℕ × Fin n) (hf : f ∈ allTicks p.lo p.count) : 0 < p.delta f.1 := by
  have h := (mem_allTicks p.lo p.count f).mp hf
  have hcount : p.lo f.2 + p.count f.2 = p.hi f.2 :=
    Nat.add_sub_cancel' (p.lo_lt_hi hd f.2).le
  rw [hcount] at h
  exact p.delta_pos (h.2.trans_le (p.hi_le f.2))

/-- Events active in the `k`th interval, each listed once. -/
def EndpointPartition.activeEvents {start duration : Fin n → ℝ}
    (p : EndpointPartition start duration) (k : ℕ) : List (Fin n) :=
  (List.finRange n).filter fun v => p.lo v ≤ k ∧ k < p.hi v

/-- Generated fragments in one partition interval. -/
def EndpointPartition.intervalFragments {start duration : Fin n → ℝ}
    (p : EndpointPartition start duration) (k : ℕ) : List (ℕ × Fin n) :=
  (allTicks p.lo p.count).filter fun f => f.1 = k

/-- Interval fragments contain each active event exactly once, with the same interval index. -/
theorem EndpointPartition.intervalFragments_perm {start duration : Fin n → ℝ}
    (p : EndpointPartition start duration) (hd : ∀ v, 0 < duration v) (k : ℕ) :
    (p.intervalFragments k).Perm ((p.activeEvents k).map fun v => (k, v)) := by
  have hl : (p.intervalFragments k).Nodup := (allTicks_nodup p.lo p.count).filter _
  have hr : ((p.activeEvents k).map fun v => (k, v)).Nodup :=
    ((List.nodup_finRange n).filter _).map (fun a b h => congrArg Prod.snd h)
  apply (List.perm_ext_iff_of_nodup hl hr).mpr
  intro f
  rcases f with ⟨t, v⟩
  have hcount : p.lo v + p.count v = p.hi v :=
    Nat.add_sub_cancel' (p.lo_lt_hi hd v).le
  simp only [intervalFragments, activeEvents, List.mem_filter, List.mem_map, mem_allTicks,
    List.mem_finRange, true_and, decide_eq_true_eq, Prod.mk.injEq, hcount]
  constructor
  · rintro ⟨hact, heq⟩
    subst t
    exact ⟨v, hact, rfl, rfl⟩
  · rintro ⟨a, hact, heq, hav⟩
    subst a
    subst t
    exact ⟨hact, rfl⟩

/-- On a half-open partition interval, the finite active-event list is exactly the physical one. -/
theorem EndpointPartition.mem_activeEvents_iff {start duration : Fin n → ℝ}
    (p : EndpointPartition start duration) (hd : ∀ v, 0 < duration v)
    {k : ℕ} (hk : k < p.intervals) (v : Fin n) (t : ℝ)
    (hlt : p.cuts k ≤ t) (htr : t < p.cuts (k + 1)) :
    v ∈ p.activeEvents k ↔ start v ≤ t ∧ t < start v + duration v := by
  have hcount : p.lo v + p.count v = p.hi v :=
    Nat.add_sub_cancel' (p.lo_lt_hi hd v).le
  simpa [activeEvents, hcount] using p.active_at hd hk v t hlt htr

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The chronological evolution obtained by splitting actual events at the partition endpoints. -/
noncomputable def EndpointPartition.evolution {start duration : Fin n → ℝ}
    (p : EndpointPartition start duration) (H : Fin n → Operator ι) : Operator ι :=
  chronologicalEvolution
    ((tickTimeline p.lo p.count).map (List.map (weightedTickGenerator H p.delta)))

omit [Fintype ι] [DecidableEq ι] in
/-- The sum of interval fragment generators is the physical Hamiltonian sum multiplied by
`-I` and by the real interval length. No active event is omitted or counted twice. -/
theorem EndpointPartition.interval_generator_eq {start duration : Fin n → ℝ}
    (p : EndpointPartition start duration) (H : Fin n → Operator ι)
    (hd : ∀ v, 0 < duration v) (k : ℕ) :
    ((p.intervalFragments k).map (weightedTickGenerator H p.delta)).sum =
      (p.delta k : ℂ) • (-Complex.I • ((p.activeEvents k).map H).sum) := by
  rw [(p.intervalFragments_perm hd k).map (weightedTickGenerator H p.delta) |>.sum_eq]
  simp only [List.map_map, Function.comp_def, weightedTickGenerator, tickGenerator]
  generalize p.activeEvents k = events
  induction events with
  | nil => simp
  | cons v events ih => simp only [List.map_cons, List.sum_cons, smul_add, ih]

/-- The segment-defined real evolution is literally the chronological product of exponentials
of the physical active-event Hamiltonian sums, one for each real partition interval. -/
theorem EndpointPartition.evolution_eq_interval_product {start duration : Fin n → ℝ}
    (p : EndpointPartition start duration) (H : Fin n → Operator ι)
    (hd : ∀ v, 0 < duration v) :
    p.evolution H =
      (((List.range (Scheduling.makespan p.count p.lo)).map fun k =>
        exp ((p.delta k : ℂ) • (-Complex.I • ((p.activeEvents k).map H).sum))).reverse).prod := by
  unfold EndpointPartition.evolution chronologicalEvolution tickTimeline partitionBy
  simp only [List.map_map]
  apply congrArg (fun l : List (Operator ι) => l.reverse.prod)
  apply List.map_congr_left
  intro k hk
  change exp ((p.intervalFragments k).map (weightedTickGenerator H p.delta)).sum = _
  rw [p.interval_generator_eq H hd k]

/-- Every common endpoint partition of a feasible real schedule realizes the target
pulse circuit. -/
theorem EndpointPartition.evolution_eq {start duration : Fin n → ℝ}
    (p : EndpointPartition start duration) (r : Fin n → Fin n → Prop)
    (H : Fin n → Operator ι) (hd : ∀ v, 0 < duration v)
    (ho : ∀ u v, r u v → u < v)
    (hp : ∀ u v, r u v → start u + duration u ≤ start v)
    (hc : ∀ u v, ¬ r u v → ¬ r v u → Commute (H u) (H v)) :
    p.evolution H =
      (((List.finRange n).map fun v =>
        Giallar.PulseSchedule.evolution (H v) (duration v)).reverse).prod :=
  weighted_timeline_evolution r H p.lo p.count p.delta duration ho
    (p.precedence hd r hp) (p.duration_sum hd) hc

/-- The pulse timeline semantics for an arbitrary finite real schedule. -/
noncomputable def realTimelineEvolution (H : Fin n → Operator ι)
    (start duration : Fin n → ℝ) : Operator ι :=
  (endpointPartition start duration).evolution H

/-- A feasible real pulse schedule with commuting incomparable Hamiltonians realizes the same
chronological quantum circuit, including arbitrary overlap between independent events. -/
theorem realTimelineEvolution_eq (r : Fin n → Fin n → Prop) (H : Fin n → Operator ι)
    (start duration : Fin n → ℝ) (hd : ∀ v, 0 < duration v)
    (ho : ∀ u v, r u v → u < v)
    (hp : ∀ u v, r u v → start u + duration u ≤ start v)
    (hc : ∀ u v, ¬ r u v → ¬ r v u → Commute (H u) (H v)) :
    realTimelineEvolution H start duration =
      (((List.finRange n).map fun v =>
        Giallar.PulseSchedule.evolution (H v) (duration v)).reverse).prod :=
  (endpointPartition start duration).evolution_eq r H hd ho hp hc

/-- The real pulse semantics is independent of the chosen common endpoint refinement. -/
theorem EndpointPartition.evolution_eq_of_partitions {start duration : Fin n → ℝ}
    (p q : EndpointPartition start duration) (r : Fin n → Fin n → Prop)
    (H : Fin n → Operator ι) (hd : ∀ v, 0 < duration v)
    (ho : ∀ u v, r u v → u < v)
    (hp : ∀ u v, r u v → start u + duration u ≤ start v)
    (hc : ∀ u v, ¬ r u v → ¬ r v u → Commute (H u) (H v)) :
    p.evolution H = q.evolution H := by
  rw [p.evolution_eq r H hd ho hp hc, q.evolution_eq r H hd ho hp hc]

end Giallar.PulseSchedule
