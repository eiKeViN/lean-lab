/-
Finite real scores at a fixed input: integrals, second moments and additive variance.
Revised from the preserved UNVERIFIED_DRAFT; validation evidence is recorded separately.
-/
import PMFBridgeDraft.ChannelProduct
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Probability.Moments.Variance

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace QuantumExperiments.PMFBridgeDraft.ChannelStatistics

open ChannelProduct

variable {O : Type*} [Fintype O] [MeasurableSpace O] [MeasurableSingletonClass O]

/-- Real-only integral observation; no Integrable input on the finite carrier. -/
theorem integral_real (d : ProbDistribution O) (g : O → ℝ) :
    (∫ o, g o ∂law d) = ∑ o, (d o : ℝ) * g o := by
  simpa only [law, Bridge.toPMF_toReal, smul_eq_mul] using
    PMF.integral_eq_sum (Bridge.toPMF d) g

/-- Finite carrier supplies the second moment, including the empty-carrier boundary.
No Nonempty input or max/default element is needed for the finite bound. -/
theorem score_memLp_two (d : ProbDistribution O) (g : O → ℝ) : MemLp g 2 (law d) := by
  classical
  refine MemLp.of_bound (measurable_of_finite g).aemeasurable.aestronglyMeasurable
    (∑ o, ‖g o‖) ?_
  exact Filter.Eventually.of_forall fun o =>
    Finset.single_le_sum (fun x _ => norm_nonneg (g x)) (Finset.mem_univ o)

variable {I : Type*} {n : ℕ}

def totalScore (g : Fin n → O → ℝ) (os : Fin n → O) : ℝ := ∑ k, g k (os k)

/-- Reuse the native variance theorem with explicit task-local MemLp certificates. -/
theorem variance_totalScore_of_memLp (C : DMChannel I O) (is : Fin n → I)
    (g : Fin n → O → ℝ) (hg : ∀ k, MemLp (g k) 2 (law (C.symb_dist (is k)))) :
    ProbabilityTheory.variance (totalScore g) (law (C.on_fin I O is)) =
      ∑ k, ProbabilityTheory.variance (g k) (law (C.symb_dist (is k))) := by
  rw [law_on_fin_eq_pi]
  have hscore : totalScore g = ∑ k, fun os => g k (os k) := by
    funext os
    simp only [totalScore, Finset.sum_apply]
  rw [hscore]
  exact ProbabilityTheory.variance_sum_pi
      (μ := fun k : Fin n => law (C.symb_dist (is k))) (X := g) hg

/-- The finite real-score client needs no extra second-moment input.
The input string is fixed throughout; this is not an unconditional random-input law. -/
theorem variance_totalScore (C : DMChannel I O) (is : Fin n → I)
    (g : Fin n → O → ℝ) :
    ProbabilityTheory.variance (totalScore g) (law (C.on_fin I O is)) =
      ∑ k, ProbabilityTheory.variance (g k) (law (C.symb_dist (is k))) := by
  exact variance_totalScore_of_memLp C is g
    (fun k => score_memLp_two (C.symb_dist (is k)) (g k))

end QuantumExperiments.PMFBridgeDraft.ChannelStatistics
