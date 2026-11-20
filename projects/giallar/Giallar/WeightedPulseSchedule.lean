/-
Copyright (c) 2026 Kevin Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Zhao
-/
module

public import Giallar.TickPulseSchedule

/-!
# Nonuniform real interval lengths in a pulse timeline

Time indices need not denote unit intervals: `weightedTickGenerator` multiplies each Hamiltonian
by its real interval length. The concrete fragment construction is reused from `TickPulseSchedule`,
while `weighted_timeline_evolution` combines interval lengths into each event's total duration.
This is the algebraic interface for a sorted partition containing all real pulse endpoints.
-/

@[expose] public section

namespace Giallar.PulseSchedule

open NormedSpace
open scoped Matrix.Norms.L2Operator

variable {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Schrödinger generator contribution over one real-length interval. -/
noncomputable def weightedTickGenerator (H : Fin n → Operator ι) (delta : ℕ → ℝ)
    (f : ℕ × Fin n) : Operator ι :=
  (delta f.1 : ℂ) • tickGenerator H f

omit [DecidableEq ι] in
/-- Scaling each commuting fragment by its own duration preserves commutation. -/
theorem weighted_blocks_commute (H : Fin n → Operator ι) (delta : ℕ → ℝ)
    (xs : List (ℕ × Fin n)) (hc : (xs.map (tickGenerator H)).Pairwise Commute) :
    (xs.map (weightedTickGenerator H delta)).Pairwise Commute := by
  apply List.pairwise_map.mpr
  have h := List.pairwise_map.mp hc
  apply h.imp
  intro a b hab
  exact (hab.smul_left (delta a.1 : ℂ)).smul_right (delta b.1 : ℂ)

/-- A weighted event block realizes the pulse with the sum of its interval durations. -/
theorem weighted_event_gate_list (H : Fin n → Operator ι) (lo count : Fin n → ℕ)
    (delta : ℕ → ℝ) (duration : Fin n → ℝ)
    (hdelta : ∀ v, ((List.range' (lo v) (count v)).map delta).sum = duration v) :
    (((eventTickBlocks lo count).map (List.map (weightedTickGenerator H delta))).map
      fun b => exp b.sum) =
      (List.finRange n).map (fun v => evolution (H v) (duration v)) := by
  unfold eventTickBlocks
  simp only [List.map_map]
  apply List.map_congr_left
  intro v hv
  change exp ((eventTicks lo count v).map (weightedTickGenerator H delta)).sum = _
  have hs := fragmentGenerator_sum H Prod.snd (fun f : ℕ × Fin n => delta f.1)
    v (eventTicks lo count v) (by
      intro f hf
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hf
      rfl)
  have hm : ((eventTicks lo count v).map fun f => delta f.1).sum = duration v := by
    simpa [eventTicks, List.map_map, Function.comp_def] using hdelta v
  change ((eventTicks lo count v).map (weightedTickGenerator H delta)).sum = _ at hs
  rw [hs, hm]
  rfl

/-- Chronological evolution of a concrete, nonuniform interval partition equals the target pulse
circuit, with total durations derived by finite interval sums. -/
theorem weighted_timeline_evolution (r : Fin n → Fin n → Prop) (H : Fin n → Operator ι)
    (lo count : Fin n → ℕ) (delta : ℕ → ℝ) (duration : Fin n → ℝ)
    (ho : ∀ u v, r u v → u < v)
    (hp : ∀ u v, r u v → lo u + count u ≤ lo v)
    (hdelta : ∀ v, ((List.range' (lo v) (count v)).map delta).sum = duration v)
    (hc : ∀ u v, ¬ r u v → ¬ r v u → Commute (H u) (H v)) :
    chronologicalEvolution
      ((tickTimeline lo count).map (List.map (weightedTickGenerator H delta))) =
      (((List.finRange n).map fun v => evolution (H v) (duration v)).reverse).prod := by
  calc
    _ = chronologicalEvolution
        ((eventTickBlocks lo count).map (List.map (weightedTickGenerator H delta))) := by
      apply chronological_segmented_evolution_eq (fun a b : ℕ × Fin n => r a.2 b.2)
        (fun a h => (lt_irrefl a.2) (ho _ _ h)) (weightedTickGenerator H delta)
        (fun a b hab hba =>
          ((tickGenerator_commute r H hc a b hab hba).smul_left (delta a.1 : ℂ)).smul_right
            (delta b.1 : ℂ)) (tickTimeline lo count) (eventTickBlocks lo count)
        (tickTimeline_flatten_perm lo count) (tickTimeline_respects r lo count hp)
        (eventTickBlocks_respects r lo count ho)
      · intro b hb
        exact weighted_blocks_commute H delta b (tickTimeline_commute r H lo count hp hc b hb)
      · intro b hb
        exact weighted_blocks_commute H delta b (eventTickBlocks_commute H lo count b hb)
    _ = _ := congrArg (fun l => l.reverse.prod)
      (weighted_event_gate_list H lo count delta duration hdelta)

end Giallar.PulseSchedule
