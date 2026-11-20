/-
Copyright (c) 2026 Kevin Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Zhao
-/
module

import Giallar.ControlledPhase
import Giallar.PhaseSynthesis
import Giallar.Routing
import Giallar.Scheduling
import Giallar.Worklist

/-!
# Cross-module integration clients

These clients instantiate actual two-qubit phase matrices, a phase-extraction and merging
pipeline, finite schedule and routing checkers, and a terminating task-expansion compiler.
The Boolean acceptance and rejection examples are checked by kernel reduction with `decide`.
-/

open scoped Matrix.Norms.L2Operator

namespace Giallar.Integration

/-- Worklist execution uses precisely the same chronological multiplication as the circuit API. -/
theorem worklist_eval_eq_eval_map {Task M : Type*} [Monoid M] (sem : Task → M)
    (tasks : List Task) : Worklist.eval sem tasks = Giallar.eval (tasks.map sem) := by
  induction tasks with
  | nil => rfl
  | cons t ts ih => simp [Worklist.eval, ih]

/-- A concrete controlled phase of angle π/8 has at most π/8 operator error on deletion. -/
theorem controlled_pi_eighth_error :
    ‖ControlledPhase.controlled (0 : Fin 2) 1 (Real.pi / 8) - 1‖ ≤ Real.pi / 8 := by
  simpa [abs_of_nonneg (show 0 ≤ Real.pi / 8 by positivity)] using
    ControlledPhase.norm_controlled_sub_one_le (0 : Fin 2) 1 (Real.pi / 8)

/-- A concrete source fragment includes CNOTs and phases on both wires. -/
noncomputable def phaseCircuit : List (PhasePolynomial.Gate (Fin 2)) :=
  [.cx 0 1 (by decide), .phase 1 (Real.pi / 4), .phase 0 (Real.pi / 8),
    .phase 1 (Real.pi / 4), .cx 0 1 (by decide)]

/-- Extracting and globally merging that fragment preserves its complex matrix exactly. -/
theorem phase_pipeline_correct :
    (PhasePolynomial.extract phaseCircuit).merge.action.matrix =
      (PhasePolynomial.execute phaseCircuit PhasePolynomial.Action.one).matrix := by
  rw [PhasePolynomial.Representation.merge_correct, PhasePolynomial.extract_matrix_correct]

/-- The complete extract/merge/Gaussian-resynthesis pipeline preserves the same client circuit. -/
theorem phase_resynthesis_correct :
    (PhasePolynomial.execute (PhasePolynomial.optimize phaseCircuit)
      PhasePolynomial.Action.one).matrix =
        (PhasePolynomial.execute phaseCircuit PhasePolynomial.Action.one).matrix :=
  PhasePolynomial.optimize_correct phaseCircuit

/-- The two independent events both require the sole exclusive controller. -/
def resources (_ : Fin 2) : Finset (Fin 1) := {0}

/-- Sequencing the resource users passes the finite schedule checker. -/
theorem sequential_schedule_accepted :
    Scheduling.checkSchedule (fun _ _ : Fin 2 => False) (fun _ => 1) resources
      (fun v => v.val) = true := by decide

/-- Starting both users simultaneously fails the same checker. -/
theorem overlapping_schedule_rejected :
    Scheduling.checkSchedule (fun _ _ : Fin 2 => False) (fun _ => 1) resources
      (fun _ => 0) = false := by decide

/-- Acceptance also supplies the semantic feasibility proposition, not only a Boolean result. -/
theorem sequential_schedule_feasible :
    Scheduling.Feasible (fun _ _ : Fin 2 => False) (fun _ => 1) resources
      (fun v => v.val) :=
  (Scheduling.checkSchedule_eq_true _ _ _ _).mp sequential_schedule_accepted

/-- A one-gate trace with the correct layout consumes its source and is accepted. -/
theorem routing_emit_accepted :
    Routing.checkTrace (fun a b : Fin 2 => a ≠ b) (fun _ (_ : Unit) => True)
      [()] 1 [.emit 1 ()] = some 1 := by decide

/-- A self-SWAP is forbidden by the hardware predicate and is rejected before emission. -/
theorem routing_self_swap_rejected :
    Routing.checkTrace (fun a b : Fin 2 => a ≠ b) (fun _ (_ : Unit) => True)
      [()] 1 [.swap 0 0, .emit 1 ()] = none := by decide

/-- Primitive-only expansion computes a nontrivial controlled-phase power and terminates. -/
theorem controlled_phase_power_compilation :
    ∃ steps final,
      Worklist.Steps
        (fun k : ℕ => ControlledPhase.controlled (0 : Fin 2) 1 (Real.pi / 8) ^ k)
        id 2 (fun k => k ≤ 1) ⟨[7], 1⟩ steps final ∧
      final.pending = [] ∧
      final.emitted = ControlledPhase.controlled (0 : Fin 2) 1 (Real.pi / 8) ^ 7 ∧
      steps ≤ 3 ^ 7 :=
  Worklist.power_tasks_terminate (ControlledPhase.controlled (0 : Fin 2) 1 (Real.pi / 8)) 7

end Giallar.Integration
