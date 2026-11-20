/-
Copyright (c) 2026 Kevin Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Zhao
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Retry bounds for a randomized routing search

A retry process is represented by decreasing measurable survival events: membership in
`survival n` means that the first `n` attempts have not succeeded. Its attempt count is the
nonnegative sum of survival indicators, including `survival 0` for the first attempt.
The local hypothesis bounds the next failure probability by a fixed factor `q` times the
current failure probability. No independence is assumed.

## Main results

* `RetryProcess.survival_le_pow`: geometric tail bound from the one-step inequality.
* `RetryProcess.measure_nontermination`: infinite retry has probability zero when `q < 1`.
* `RetryProcess.expected_attempts_le`: expected attempts are bounded by `(1 - q)⁻¹`.
* `RetryProcess.expected_cost_le`: a per-attempt cost budget scales the same bound.

The model formalizes report C3, with `q = 1 - p` for a success probability lower bound `p`.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace Giallar

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Measurable nested events describing failure after each finite number of attempts. -/
structure RetryProcess (Ω : Type*) [MeasurableSpace Ω] where
  /-- `survival n` contains exactly the samples not yet successful after `n` attempts. -/
  survival : ℕ → Set Ω
  /-- Survival events are measurable. -/
  measurable_survival : ∀ n, MeasurableSet (survival n)
  /-- The first attempt is made on every sample. -/
  survival_zero : survival 0 = univ
  /-- Once a sample succeeds, it does not return to the failed population. -/
  antitone_survival : Antitone survival

namespace RetryProcess

variable (P : RetryProcess Ω)

/-- The possibly infinite number of attempts, as the sum of survival indicators. -/
noncomputable def attempts (ω : Ω) : ℝ≥0∞ :=
  ∑' n, (P.survival n).indicator (fun _ => (1 : ℝ≥0∞)) ω

/-- The attempt count is a measurable extended nonnegative random variable. -/
theorem measurable_attempts : Measurable P.attempts := by
  unfold attempts
  simp only [ENNReal.tsum_eq_iSup_sum]
  exact Measurable.iSup fun s => s.measurable_fun_sum fun n _ =>
    measurable_const.indicator (P.measurable_survival n)

/-- The nontermination event consists of samples surviving every finite attempt. -/
def nontermination : Set Ω := ⋂ n, P.survival n

/-- Leaving the survival population by stage `n` bounds the attempt count by `n`. -/
theorem attempts_le_nat_of_not_mem {ω : Ω} {n : ℕ} (hn : ω ∉ P.survival n) :
    P.attempts ω ≤ n := by
  classical
  have hz : ∀ k ∉ Finset.range n,
      (P.survival k).indicator (fun _ => (1 : ℝ≥0∞)) ω = 0 := by
    intro k hk
    apply indicator_of_notMem
    intro hω
    exact hn (P.antitone_survival (Nat.le_of_not_gt (by simpa using hk)) hω)
  rw [attempts, tsum_eq_sum hz]
  calc
    ∑ k ∈ Finset.range n, (P.survival k).indicator (fun _ => (1 : ℝ≥0∞)) ω ≤
        ∑ _k ∈ Finset.range n, (1 : ℝ≥0∞) := by
      apply Finset.sum_le_sum
      intro k _
      by_cases hk : ω ∈ P.survival k <;> simp [hk]
    _ = n := by simp

/-- The given survival events are exactly the tails of the attempt-count random variable. -/
theorem nat_lt_attempts_iff {ω : Ω} {n : ℕ} :
    (n : ℝ≥0∞) < P.attempts ω ↔ ω ∈ P.survival n := by
  classical
  constructor
  · intro hn
    by_contra hω
    exact not_lt_of_ge (P.attempts_le_nat_of_not_mem hω) hn
  · intro hn
    have hs : ((n + 1 : ℕ) : ℝ≥0∞) ≤ P.attempts ω := by
      calc
        ((n + 1 : ℕ) : ℝ≥0∞) =
            ∑ k ∈ Finset.range (n + 1),
              (P.survival k).indicator (fun _ => (1 : ℝ≥0∞)) ω := by
          symm
          calc
            _ = ∑ _k ∈ Finset.range (n + 1), (1 : ℝ≥0∞) := by
              apply Finset.sum_congr rfl
              intro k hk
              exact indicator_of_mem (P.antitone_survival
                (Nat.le_of_lt_succ (Finset.mem_range.mp hk)) hn) _
            _ = _ := by simp
        _ ≤ P.attempts ω := ENNReal.sum_le_tsum _
    exact lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self n) hs

/-- A conditional failure bound written without division, including zero-probability tails. -/
def HasFailureBound (μ : Measure Ω) (q : ℝ≥0∞) : Prop :=
  ∀ n, μ (P.survival (n + 1)) ≤ q * μ (P.survival n)

/-- A conditional failure ratio gives the division-free one-step bound. -/
theorem hasFailureBound_of_conditional [IsProbabilityMeasure μ] {q : ℝ≥0∞}
    (h : ∀ n, μ (P.survival n) ≠ 0 →
      μ (P.survival (n + 1)) / μ (P.survival n) ≤ q) : P.HasFailureBound μ q := by
  intro n
  by_cases hz : μ (P.survival n) = 0
  · have hm := measure_mono (μ := μ) (P.antitone_survival (Nat.le_succ n))
    simpa [hz] using hm
  · exact (ENNReal.div_le_iff hz (measure_ne_top _ _)).mp (h n hz)

/-- Local failure bounds imply the geometric tail estimate without independence. -/
theorem survival_le_pow [IsProbabilityMeasure μ] {q : ℝ≥0∞}
    (h : P.HasFailureBound μ q) (n : ℕ) : μ (P.survival n) ≤ q ^ n := by
  induction n with
  | zero => simp [P.survival_zero]
  | succ n ih =>
      calc
        μ (P.survival (n + 1)) ≤ q * μ (P.survival n) := h n
        _ ≤ q * q ^ n := by simpa [mul_comm] using mul_le_mul_left ih q
        _ = q ^ (n + 1) := (pow_succ' q n).symm

/-- The actual attempt-count random variable satisfies the geometric tail bound. -/
theorem measure_attempts_gt_le [IsProbabilityMeasure μ] {q : ℝ≥0∞}
    (h : P.HasFailureBound μ q) (n : ℕ) :
    μ {ω | (n : ℝ≥0∞) < P.attempts ω} ≤ q ^ n := by
  simpa [P.nat_lt_attempts_iff] using P.survival_le_pow h n

/-- The expected attempt count is exactly the sum of the tail probabilities. -/
theorem lintegral_attempts : ∫⁻ ω, P.attempts ω ∂μ = ∑' n, μ (P.survival n) := by
  unfold attempts
  rw [lintegral_tsum]
  · congr 1
    ext n
    exact lintegral_indicator_const (P.measurable_survival n) 1 |>.trans (one_mul _)
  · intro n
    exact (measurable_const.indicator (P.measurable_survival n)).aemeasurable

/-- A geometric failure factor strictly below one makes infinite retry a null event. -/
theorem measure_nontermination [IsProbabilityMeasure μ] {q : ℝ≥0∞}
    (hq : q < 1) (h : P.HasFailureBound μ q) : μ P.nontermination = 0 := by
  apply ENNReal.eq_zero_of_le_mul_pow (ε := 1) hq
  intro n
  simpa only [nontermination, ENNReal.coe_one, one_mul] using
    (measure_mono (iInter_subset P.survival n)).trans (P.survival_le_pow h n)

/-- Almost every sample succeeds after finitely many attempts. -/
theorem ae_terminates [IsProbabilityMeasure μ] {q : ℝ≥0∞}
    (hq : q < 1) (h : P.HasFailureBound μ q) :
    ∀ᵐ ω ∂μ, ∃ n, ω ∉ P.survival n := by
  rw [ae_iff]
  have heq : {ω | ¬ ∃ n, ω ∉ P.survival n} = P.nontermination := by
    ext ω
    simp [nontermination]
  rw [heq]
  exact P.measure_nontermination hq h

/-- The attempt-count random variable is finite almost surely. -/
theorem ae_attempts_lt_top [IsProbabilityMeasure μ] {q : ℝ≥0∞}
    (hq : q < 1) (h : P.HasFailureBound μ q) : ∀ᵐ ω ∂μ, P.attempts ω < ∞ := by
  filter_upwards [P.ae_terminates hq h] with ω hω
  obtain ⟨n, hn⟩ := hω
  exact (P.attempts_le_nat_of_not_mem hn).trans_lt (ENNReal.natCast_lt_top n)

/-- The expected count has the usual geometric upper bound. -/
theorem expected_attempts_le [IsProbabilityMeasure μ] {q : ℝ≥0∞}
    (h : P.HasFailureBound μ q) :
    ∫⁻ ω, P.attempts ω ∂μ ≤ (1 - q)⁻¹ := by
  rw [P.lintegral_attempts]
  calc
    ∑' n, μ (P.survival n) ≤ ∑' n, q ^ n :=
      ENNReal.tsum_le_tsum (P.survival_le_pow h)
    _ = (1 - q)⁻¹ := ENNReal.tsum_geometric q

/-- A bounded cost per attempt bounds the expected total search and checking cost. -/
theorem expected_cost_le [IsProbabilityMeasure μ] {q c : ℝ≥0∞}
    (h : P.HasFailureBound μ q) (cost : Ω → ℝ≥0∞)
    (hcost : ∀ ω, cost ω ≤ c * P.attempts ω) :
    ∫⁻ ω, cost ω ∂μ ≤ c * (1 - q)⁻¹ := by
  calc
    ∫⁻ ω, cost ω ∂μ ≤ ∫⁻ ω, c * P.attempts ω ∂μ := lintegral_mono hcost
    _ = c * ∫⁻ ω, P.attempts ω ∂μ := by
      rw [lintegral_const_mul]
      exact P.measurable_attempts
    _ ≤ c * (1 - q)⁻¹ := by
      simpa [mul_comm] using mul_le_mul_left (P.expected_attempts_le h) c

/-- Express the expected-attempt bound using the success probability `p = 1 - q`. -/
theorem expected_attempts_le_inv_success [IsProbabilityMeasure μ] {p : ℝ≥0∞}
    (hp : p ≤ 1) (h : P.HasFailureBound μ (1 - p)) :
    ∫⁻ ω, P.attempts ω ∂μ ≤ p⁻¹ := by
  simpa only [ENNReal.sub_sub_cancel ENNReal.one_ne_top hp] using P.expected_attempts_le h

/-- A strictly positive conditional success probability implies almost sure termination. -/
theorem ae_terminates_of_success [IsProbabilityMeasure μ] {p : ℝ≥0∞}
    (hp : 0 < p) (h : P.HasFailureBound μ (1 - p)) :
    ∀ᵐ ω ∂μ, ∃ n, ω ∉ P.survival n :=
  P.ae_terminates (ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hp.ne') h

/-- Full retry guarantee from a positive conditional success lower bound.
The ratio hypothesis is conditional failure probability at every nonnull survival event. -/
theorem retry_bound [IsProbabilityMeasure μ] {p : ℝ≥0∞}
    (hp : 0 < p) (hp1 : p ≤ 1)
    (hconditional : ∀ n, μ (P.survival n) ≠ 0 →
      μ (P.survival (n + 1)) / μ (P.survival n) ≤ 1 - p) :
    (∀ n : ℕ, μ {ω | (n : ℝ≥0∞) < P.attempts ω} ≤ (1 - p) ^ n) ∧
      (∀ᵐ ω ∂μ, P.attempts ω < ∞) ∧
      ∫⁻ ω, P.attempts ω ∂μ ≤ p⁻¹ := by
  have hb := P.hasFailureBound_of_conditional hconditional
  exact ⟨P.measure_attempts_gt_le hb,
    P.ae_attempts_lt_top
      (ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hp.ne') hb,
    P.expected_attempts_le_inv_success hp1 hb⟩

end RetryProcess

end Giallar
