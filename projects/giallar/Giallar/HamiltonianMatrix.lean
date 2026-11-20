/-
Copyright (c) 2026 Kevin Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Zhao
-/
module

public import Giallar.Hamiltonian
public import Giallar.PulseSchedule
import Mathlib.Tactic.NoncommRing

/-!
# Matrix Hamiltonian perturbation bounds

The general skew-adjoint estimate is instantiated to the concrete Schrödinger generator `-iH`
with the L2 operator norm on matrices. No commutation is required between ideal and actual
Hamiltonians.
-/

@[expose] public section

open scoped Matrix Matrix.Norms.L2Operator
open NormedSpace

namespace Giallar

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

noncomputable local instance : NormedAlgebra ℚ (Matrix ι ι ℂ) :=
  .restrictScalars ℚ ℂ _

omit [Nonempty ι] [Fintype ι] [DecidableEq ι] in
/-- A Hermitian Hamiltonian gives a skew-adjoint Schrödinger generator. -/
theorem star_schrodingerGenerator (H : Matrix ι ι ℂ) (hH : H.IsHermitian) :
    star (-Complex.I • H) = -(-Complex.I • H) := by
  simp [star_smul, Matrix.star_eq_conjTranspose, hH.eq]

omit [Nonempty ι] in
/-- Operator error from perturbing a constant Hermitian Hamiltonian. -/
theorem norm_hamiltonian_evolution_sub_le (H K : Matrix ι ι ℂ)
    (hH : H.IsHermitian) (hK : K.IsHermitian) {t : ℝ} (ht : 0 ≤ t) :
    ‖PulseSchedule.evolution H t - PulseSchedule.evolution K t‖ ≤ t * ‖H - K‖ := by
  have h := norm_exp_smul_sub_le (-Complex.I • H) (-Complex.I • K)
    (star_schrodingerGenerator H hH) (star_schrodingerGenerator K hK) ht
  have hg : ‖-Complex.I • H - -Complex.I • K‖ = ‖H - K‖ := by
    rw [← smul_sub, norm_smul]
    simp
  rw [hg] at h
  simpa [PulseSchedule.evolution, ← Complex.real_smul] using h

omit [Nonempty ι] in
/-- Multiplying a Hamiltonian difference by `-i` preserves its operator norm. -/
theorem norm_schrodingerGenerator_sub (H K : Matrix ι ι ℂ) :
    ‖-Complex.I • H - -Complex.I • K‖ = ‖H - K‖ := by
  rw [← smul_sub, norm_smul]
  simp

/-- Common finite refinement of two piecewise-constant Hamiltonians has additive error. -/
theorem norm_piecewise_hamiltonian_sub_le (l : List (ℝ × Matrix ι ι ℂ × Matrix ι ι ℂ))
    (h : ∀ p ∈ l, 0 ≤ p.1 ∧ p.2.1.IsHermitian ∧ p.2.2.IsHermitian) :
    ‖eval (l.map (fun p => PulseSchedule.evolution p.2.1 p.1)) -
      eval (l.map (fun p => PulseSchedule.evolution p.2.2 p.1))‖ ≤
        (l.map (fun p => p.1 * ‖p.2.1 - p.2.2‖)).sum := by
  have hg : ∀ q ∈ l.map (fun p => (p.1, -Complex.I • p.2.1, -Complex.I • p.2.2)),
      0 ≤ q.1 ∧ star q.2.1 = -q.2.1 ∧ star q.2.2 = -q.2.2 := by
    intro q hq
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
    exact ⟨(h p hp).1, star_schrodingerGenerator _ (h p hp).2.1,
      star_schrodingerGenerator _ (h p hp).2.2⟩
  have hbound := norm_evolution_sub_le _ hg
  simp only [List.map_map, Function.comp_def, norm_schrodingerGenerator_sub] at hbound
  simpa [PulseSchedule.evolution, ← Complex.real_smul] using hbound

end Giallar
