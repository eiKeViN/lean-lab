/-
Copyright (c) 2026 Kevin Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Zhao
-/
module

public import QuantumInfo.ForMathlib.MatrixNorm.TraceNorm
public import QuantumInfo.Operators.Unitary
public import QuantumInfo.States.Mixed.TraceDistance
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing

/-!
# Stable trace-norm bounds for unitary channels

These estimates apply to arbitrary matrices, not just positive states. In particular they
can be applied on a joint system containing an untouched finite reference system.
-/

@[expose] public section

open scoped Matrix Matrix.Norms.L2Operator

namespace Giallar

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The trace norm is an operator-norm bimodule norm. -/
theorem traceNorm_sandwich (A X B : Matrix ι ι ℂ) :
    (A * X * B).traceNorm ≤ ‖A‖ * X.traceNorm * ‖B‖ := by
  calc
    _ ≤ (A * X).traceNorm * ‖B‖ := Matrix.traceNorm_mul_le_traceNorm_opNorm _ _
    _ ≤ (‖A‖ * X.traceNorm) * ‖B‖ :=
      mul_le_mul_of_nonneg_right (Matrix.traceNorm_mul_le_opNorm_traceNorm _ _) (norm_nonneg _)

/-- Perturbing two unitary conjugations gives at most twice the operator error. -/
theorem traceNorm_conjugation_sub_le [Nonempty ι]
    (U V : Matrix.unitaryGroup ι ℂ) (X : Matrix ι ι ℂ) :
    ((U : Matrix ι ι ℂ) * X * (U : Matrix ι ι ℂ)ᴴ -
      (V : Matrix ι ι ℂ) * X * (V : Matrix ι ι ℂ)ᴴ).traceNorm ≤
        2 * ‖(U : Matrix ι ι ℂ) - (V : Matrix ι ι ℂ)‖ * X.traceNorm := by
  let u : Matrix ι ι ℂ := U
  let v : Matrix ι ι ℂ := V
  have hu : ‖u‖ = 1 := CStarRing.norm_coe_unitary U
  have hv : ‖v‖ = 1 := CStarRing.norm_coe_unitary V
  have heq : u * X * uᴴ - v * X * vᴴ =
      (u - v) * X * uᴴ + v * X * (u - v)ᴴ := by
    rw [Matrix.conjTranspose_sub]
    noncomm_ring
  change (u * X * uᴴ - v * X * vᴴ).traceNorm ≤ _
  rw [heq]
  calc
    _ ≤ ((u - v) * X * uᴴ).traceNorm + (v * X * (u - v)ᴴ).traceNorm :=
      Matrix.traceNorm_add_le _ _
    _ ≤ ‖u - v‖ * X.traceNorm * ‖uᴴ‖ + ‖v‖ * X.traceNorm * ‖(u - v)ᴴ‖ :=
      add_le_add (traceNorm_sandwich _ _ _) (traceNorm_sandwich _ _ _)
    _ = _ := by rw [Matrix.l2_opNorm_conjTranspose, Matrix.l2_opNorm_conjTranspose, hu, hv]; ring

/-- Trace distance of states after nearby unitary evolutions is bounded by operator distance. -/
theorem traceDistance_unitary_le [Nonempty ι]
    (U V : Matrix.unitaryGroup ι ℂ) (ρ : MState ι) :
    TrDistance (ρ.uConj U) (ρ.uConj V) ≤
      ‖(U : Matrix ι ι ℂ) - (V : Matrix ι ι ℂ)‖ := by
  have h := traceNorm_conjugation_sub_le U V ρ.m
  rw [ρ.traceNorm_eq_one, mul_one] at h
  change (1 / 2 : ℝ) *
    ((ρ.uConj U).m - (ρ.uConj V).m).traceNorm ≤ _
  have hU : (ρ.uConj U).m = (U : Matrix ι ι ℂ) * ρ.m * (U : Matrix ι ι ℂ)ᴴ := rfl
  have hV : (ρ.uConj V).m = (V : Matrix ι ι ℂ) * ρ.m * (V : Matrix ι ι ℂ)ᴴ := rfl
  rw [hU, hV]
  linarith

end Giallar
