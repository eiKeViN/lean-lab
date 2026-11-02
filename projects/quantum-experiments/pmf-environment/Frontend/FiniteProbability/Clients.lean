/- Proposed domain clients, actually compiled here; not evidence of upstream adoption. -/
import FiniteProbability

noncomputable section
open scoped BigOperators
namespace QuantumExperiments.FiniteProbability.Clients
open PMFComparison

/-- Expected number of flagged outputs at a fixed channel input. -/
theorem expected_flag_count {I O : Type*} [Fintype O] {n : ℕ}
    (C : DMChannel I O) (is : Fin n → I) (flag : Fin n → O → Bool) :
    Finite.mean (C.on_fin I O is) (fun os => ∑ i, if flag i (os i) then (1 : ℝ) else 0) =
      ∑ i, Finite.mean (C.symb_dist (is i)) (fun o => if flag i o then (1 : ℝ) else 0) := by
  exact mean_score_on_fin C is (fun i o => if flag i o then 1 else 0)

/-- A concrete non-Fin index client: cross moment of two independently sampled sensors. -/
theorem two_sensor_cross_moment {O : Type*} [Fintype O]
    (d : Bool → ProbDistribution O) (f g : O → ℝ) :
    productMean d (fun os => f (os false) * g (os true)) =
      Finite.mean (d false) f * Finite.mean (d true) g := by
  exact productMean_pair d false true (by decide) f g

/-- Compare two diagnostics of the same output; within-coordinate covariance is retained. -/
theorem diagnostic_covariance {I O : Type*} [Fintype O] {n : ℕ}
    (C : DMChannel I O) (is : Fin n → I) (quality cost : Fin n → O → ℝ) :
    Finite.covariance (C.on_fin I O is) (fun os => ∑ i, quality i (os i))
      (fun os => ∑ i, cost i (os i)) =
      ∑ i, Finite.covariance (C.symb_dist (is i)) (quality i) (cost i) := by
  exact covariance_on_fin C is quality cost

/-- Propagate marginal uncertainty budgets through a weighted estimator.
No equal means, equal variances, nonzero weights or unbiasedness is assumed. -/
theorem weighted_uncertainty_budget {ι O : Type*} [Fintype ι] [Fintype O]
    (d : ι → ProbDistribution O) (w v : ι → ℝ) (f : ι → O → ℝ)
    (hv : ∀ i, Finite.variance (d i) (f i) ≤ v i) :
    productVariance d (fun os => ∑ i, w i * f i (os i)) ≤ ∑ i, (w i)^2 * v i := by
  rw [weighted_variance]
  exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hv i) (sq_nonneg (w i))

end QuantumExperiments.FiniteProbability.Clients
