/-
Copyright (c) 2026 Kevin Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Zhao
-/
module

public import Giallar.TraceBounds
public import QuantumInfo.ForMathlib.HermitianMat.Proj

import Mathlib.Tactic.Linarith

/-!
# Trace distance controls measurement probabilities

An effect is a Hermitian operator between zero and the identity. This file proves the
half-trace-norm bound for its pairing with any trace-zero Hermitian difference. Applying the
bound to two density operators proves that their outcome probabilities differ by at most their
trace distance. Together with unitary perturbation bounds this connects compiler operator error
to observable probabilities, without an assumed measurement Lipschitz property.

## Main results

* `traceNorm_eq_trace_posPart_add_negPart`: spectral positive and negative parts sum to trace norm.
* `abs_inner_le_half_traceNorm`: the trace-zero Hermitian effect bound (report L4).
* `abs_exp_val_sub_le_traceDistance`: measurement probabilities are controlled by trace distance.
* `abs_exp_val_unitary_sub_le`: unitary compilation error controls observable probabilities.
-/

@[expose] public section

open scoped RealInnerProductSpace Matrix.Norms.L2Operator

namespace Giallar

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The trace norm of a Hermitian matrix is the sum of its positive and negative masses. -/
theorem traceNorm_eq_trace_posPart_add_negPart (D : HermitianMat ι ℂ) :
    D.mat.traceNorm = (D⁺).trace + (D⁻).trace := by
  classical
  rw [Matrix.traceNorm_Hermitian_eq_sum_abs_eigenvalues D.H,
    HermitianMat.posPart_eq_cfc_max, HermitianMat.negPart_eq_cfc_min,
    HermitianMat.trace_cfc_eq, HermitianMat.trace_cfc_eq, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hdec : (fun a b : ι => Classical.propDecidable (a = b)) =
      (inferInstance : DecidableEq ι) := Subsingleton.elim _ _
  rw [hdec]
  by_cases hi : 0 ≤ D.H.eigenvalues i
  · simp [max_eq_left hi, max_eq_right (neg_nonpos.mpr hi), abs_of_nonneg hi]
  · have hn : D.H.eigenvalues i ≤ 0 := le_of_not_ge hi
    simp [max_eq_right hn, max_eq_left (neg_nonneg.mpr hn), abs_of_nonpos hn]

/-- Equal positive and negative spectral masses for a trace-zero Hermitian matrix. -/
theorem trace_posPart_eq_half_traceNorm (D : HermitianMat ι ℂ) (hD : D.trace = 0) :
    (D⁺).trace = (1 / 2 : ℝ) * D.mat.traceNorm ∧
      (D⁻).trace = (1 / 2 : ℝ) * D.mat.traceNorm := by
  have hdiff : (D⁺).trace - (D⁻).trace = 0 := by
    rw [← HermitianMat.trace_sub, HermitianMat.posPart_add_negPart, hD]
  have hsum := traceNorm_eq_trace_posPart_add_negPart D
  constructor <;> linarith

/-- An effect applied to a trace-zero Hermitian matrix is bounded by half its trace norm. -/
theorem abs_inner_le_half_traceNorm (D E : HermitianMat ι ℂ) (hD : D.trace = 0)
    (hE0 : 0 ≤ E) (hE1 : E ≤ 1) :
    |⟪D, E⟫| ≤ (1 / 2 : ℝ) * D.mat.traceNorm := by
  have hp0 := HermitianMat.inner_ge_zero (HermitianMat.posPart_nonneg D) hE0
  have hn0 := HermitianMat.inner_ge_zero (HermitianMat.negPart_nonneg D) hE0
  have hp1 := HermitianMat.inner_mono (HermitianMat.posPart_nonneg D) hE1
  have hn1 := HermitianMat.inner_mono (HermitianMat.negPart_nonneg D) hE1
  simp only [HermitianMat.inner_one] at hp1 hn1
  have hm := trace_posPart_eq_half_traceNorm D hD
  have heq : ⟪D, E⟫ = ⟪D⁺, E⟫ - ⟪D⁻, E⟫ := by
    nth_rw 1 [← HermitianMat.posPart_add_negPart D]
    exact HermitianMat.inner_sub_right _ _ _
  rw [heq, abs_le]
  constructor <;> linarith [hm.1, hm.2]

/-- The probabilities of an effect on two density operators differ by at most trace distance. -/
theorem abs_exp_val_sub_le_traceDistance (ρ σ : MState ι) (E : HermitianMat ι ℂ)
    (hE0 : 0 ≤ E) (hE1 : E ≤ 1) :
    |ρ.exp_val E - σ.exp_val E| ≤ TrDistance ρ σ := by
  have htrace : (ρ.M - σ.M).trace = 0 := by simp
  have h := abs_inner_le_half_traceNorm (ρ.M - σ.M) E htrace hE0 hE1
  simpa [MState.exp_val, HermitianMat.inner_sub_right, TrDistance] using h

/-- Two effect probabilities differ by at most one, independently of their trace distance. -/
theorem abs_exp_val_sub_le_one (ρ σ : MState ι) (E : HermitianMat ι ℂ)
    (hE0 : 0 ≤ E) (hE1 : E ≤ 1) :
    |ρ.exp_val E - σ.exp_val E| ≤ 1 := by
  have hρ := ρ.exp_val_prob ⟨hE0, hE1⟩
  have hσ := σ.exp_val_prob ⟨hE0, hE1⟩
  rw [abs_le]
  constructor <;> linarith

/-- Nearby unitary evolutions give nearby probabilities for every measurement event. -/
theorem abs_exp_val_unitary_sub_le [Nonempty ι]
    (U V : Matrix.unitaryGroup ι ℂ) (ρ : MState ι) (E : HermitianMat ι ℂ)
    (hE0 : 0 ≤ E) (hE1 : E ≤ 1) :
    |(ρ.uConj U).exp_val E - (ρ.uConj V).exp_val E| ≤
      min 1 ‖(U : Matrix ι ι ℂ) - (V : Matrix ι ι ℂ)‖ := by
  apply le_min
  · exact abs_exp_val_sub_le_one _ _ E hE0 hE1
  · exact (abs_exp_val_sub_le_traceDistance _ _ E hE0 hE1).trans
      (traceDistance_unitary_le U V ρ)

end Giallar
