/-
Copyright (c) 2026 Kevin Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Zhao
-/
module

public import Giallar.PhaseDistance
public import Giallar.TraceBounds

/-!
# Global phases and observable trace-distance bounds

A unit complex scalar preserves unitarity and disappears from conjugation. Applying the ordinary
operator-error bound at the attained minimizing phase therefore gives a trace-distance bound by
the actual phase distance, with no unproved phase witness assumption.

The scalar acts on the entire evolution; this result does not justify dropping relative phases
inside a controlled subroutine.
-/

@[expose] public section

open scoped Matrix Matrix.Norms.L2Operator

namespace Giallar

/-- A complex number of modulus one is a unitary scalar. -/
def scalarUnitary (z : ℂ) (hz : ‖z‖ = 1) : unitary ℂ :=
  ⟨z, by
    rw [Unitary.mem_iff]
    simp [Complex.conj_mul', Complex.mul_conj', hz]⟩

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Multiply an entire unitary matrix by a unit complex scalar. -/
def scaleUnitary (z : ℂ) (hz : ‖z‖ = 1) (U : Matrix.unitaryGroup ι ℂ) :
    Matrix.unitaryGroup ι ℂ :=
  ⟨z • (U : Matrix ι ι ℂ), Unitary.smul_mem_of_mem (scalarUnitary z hz).property U.property⟩

@[simp]
theorem coe_scaleUnitary (z : ℂ) (hz : ‖z‖ = 1) (U : Matrix.unitaryGroup ι ℂ) :
    (scaleUnitary z hz U : Matrix ι ι ℂ) = z • (U : Matrix ι ι ℂ) := rfl

omit [DecidableEq ι] in
/-- A global phase cancels from conjugation of every matrix. -/
theorem conjugation_scale_phase (z : ℂ) (hz : ‖z‖ = 1) (V X : Matrix ι ι ℂ) :
    (z • V) * X * (z • V)ᴴ = V * X * Vᴴ := by
  rw [Matrix.conjTranspose_smul, Matrix.smul_mul, smul_mul_smul]
  have hphase : z * star z = 1 := (scalarUnitary z hz).property.2
  rw [hphase, one_smul]

@[simp]
theorem uConj_scaleUnitary (z : ℂ) (hz : ‖z‖ = 1) (U : Matrix.unitaryGroup ι ℂ)
    (ρ : MState ι) : ρ.uConj (scaleUnitary z hz U) = ρ.uConj U := by
  apply MState.ext_m
  exact conjugation_scale_phase z hz (U : Matrix ι ι ℂ) ρ.m

/-- The phase-distance bound for arbitrary matrices, before specializing to normalized states. -/
theorem traceNorm_conjugation_sub_le_phaseDistance [Nonempty ι]
    (U V : Matrix.unitaryGroup ι ℂ) (X : Matrix ι ι ℂ) :
    ((U : Matrix ι ι ℂ) * X * (U : Matrix ι ι ℂ)ᴴ -
      (V : Matrix ι ι ℂ) * X * (V : Matrix ι ι ℂ)ᴴ).traceNorm ≤
        2 * phaseDistance (U : Matrix ι ι ℂ) (V : Matrix ι ι ℂ) * X.traceNorm := by
  let z := optimalPhase (U : Matrix ι ι ℂ) (V : Matrix ι ι ℂ)
  have hz : ‖z‖ = 1 := norm_optimalPhase _ _
  have h := traceNorm_conjugation_sub_le U (scaleUnitary z hz V) X
  simpa only [coe_scaleUnitary, conjugation_scale_phase z hz, phaseDistance, z] using h

/-- Output trace distance is at most the minimum operator error over all global phases. -/
theorem traceDistance_unitary_le_phaseDistance [Nonempty ι]
    (U V : Matrix.unitaryGroup ι ℂ) (ρ : MState ι) :
    TrDistance (ρ.uConj U) (ρ.uConj V) ≤
      phaseDistance (U : Matrix ι ι ℂ) (V : Matrix ι ι ℂ) := by
  let z := optimalPhase (U : Matrix ι ι ℂ) (V : Matrix ι ι ℂ)
  have hz : ‖z‖ = 1 := norm_optimalPhase _ _
  have h := traceDistance_unitary_le U (scaleUnitary z hz V) ρ
  simpa only [uConj_scaleUnitary, coe_scaleUnitary, phaseDistance, z] using h

end Giallar
