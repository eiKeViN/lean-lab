/- Task-facing finite sums; the representation-level Fintype instance stays internal. -/
import FiniteProbability.Moments

noncomputable section
open scoped BigOperators
namespace QuantumExperiments.FiniteProbability
open PMFComparison
open PMFBridgeDraft.ChannelProduct PMFComparison.Transport

variable {ι O α : Type*}

/-- Finite product expectation, with the same signature as the native frontend. -/
def productMean [Fintype ι] [Fintype O] (d : ι → ProbDistribution O)
    (f : (ι → O) → ℝ) : ℝ := by
  classical
  exact ∑ os, (∏ i, (d i (os i) : ℝ)) * f os

/-- Internal observation bridge; accepts any enumeration chosen by Physlib. -/
theorem productMean_eq_mean [Fintype ι] [Fintype O] [Fintype (ι → O)]
    (d : ι → ProbDistribution O) (f : (ι → O) → ℝ) :
    productMean d f = Finite.mean (product d) f := by
  classical
  unfold productMean Finite.mean
  simp only [product_apply]
  congr 1
  ext os
  simp

theorem productMean_prod [Fintype ι] [Fintype O]
    (d : ι → ProbDistribution O) (f : ι → O → ℝ) :
    productMean d (fun os => ∏ i, f i (os i)) = ∏ i, Finite.mean (d i) (f i) := by
  classical
  rw [productMean_eq_mean]
  exact mean_product_prod d f

theorem productMean_coordinate [Fintype ι] [Fintype O]
    (d : ι → ProbDistribution O) (i : ι) (f : O → ℝ) :
    productMean d (fun os => f (os i)) = Finite.mean (d i) f := by
  classical
  rw [productMean_eq_mean]
  exact mean_product_coordinate d i f

theorem productMean_pair [Fintype ι] [Fintype O]
    (d : ι → ProbDistribution O) (i j : ι) (hij : i ≠ j) (f g : O → ℝ) :
    productMean d (fun os => f (os i) * g (os j)) =
      Finite.mean (d i) f * Finite.mean (d j) g := by
  classical
  rw [productMean_eq_mean]
  exact mean_product_pair d i j hij f g

theorem productMean_sum [Fintype ι] [Fintype O] {κ : Type*} [Fintype κ]
    (d : ι → ProbDistribution O) (f : κ → (ι → O) → ℝ) :
    productMean d (fun os => ∑ k, f k os) = ∑ k, productMean d (f k) := by
  classical
  simp only [productMean_eq_mean, mean_sum]

theorem productMean_sum_coordinate [Fintype ι] [Fintype O]
    (d : ι → ProbDistribution O) (f : ι → O → ℝ) :
    productMean d (fun os => ∑ i, f i (os i)) = ∑ i, Finite.mean (d i) (f i) := by
  classical
  rw [productMean_eq_mean]
  exact mean_product_sum_coordinate d f

/-- Finite product variance expressed entirely in the finite expectation vocabulary. -/
def productVariance [Fintype ι] [Fintype O] (d : ι → ProbDistribution O)
    (f : (ι → O) → ℝ) : ℝ := productMean d (fun os => (f os - productMean d f)^2)

def productCovariance [Fintype ι] [Fintype O] (d : ι → ProbDistribution O)
    (f g : (ι → O) → ℝ) : ℝ :=
  productMean d (fun os => (f os - productMean d f) * (g os - productMean d g))

theorem productVariance_eq_variance [Fintype ι] [Fintype O] [Fintype (ι → O)]
    (d : ι → ProbDistribution O) (f : (ι → O) → ℝ) :
    productVariance d f = Finite.variance (product d) f := by
  simp only [productVariance, Finite.variance, productMean_eq_mean]

theorem productCovariance_eq_covariance [Fintype ι] [Fintype O] [Fintype (ι → O)]
    (d : ι → ProbDistribution O) (f g : (ι → O) → ℝ) :
    productCovariance d f g = Finite.covariance (product d) f g := by
  simp only [productCovariance, Finite.covariance, productMean_eq_mean]

theorem productVariance_sum [Fintype ι] [Fintype O]
    (d : ι → ProbDistribution O) (f : ι → O → ℝ) :
    productVariance d (fun os => ∑ i, f i (os i)) = ∑ i, Finite.variance (d i) (f i) := by
  classical
  rw [productVariance_eq_variance]
  exact variance_sum d f

theorem productCovariance_sum [Fintype ι] [Fintype O]
    (d : ι → ProbDistribution O) (f g : ι → O → ℝ) :
    productCovariance d (fun os => ∑ i, f i (os i)) (fun os => ∑ i, g i (os i)) =
      ∑ i, Finite.covariance (d i) (f i) (g i) := by
  classical
  rw [productCovariance_eq_covariance]
  exact covariance_sum d f g

/-- Scaling observation transported from mathlib, with discrete structure hidden. -/
theorem variance_scale [Fintype α] (d : ProbDistribution α) (c : ℝ) (f : α → ℝ) :
    Finite.variance d (fun a => c * f a) = c^2 * Finite.variance d f := by
  let : MeasurableSpace α := ⊤
  let : MeasurableSingletonClass α := ⟨fun _ => MeasurableSet.of_discrete⟩
  simpa only [variance_eq_finite] using ProbabilityTheory.variance_const_mul c f (law d)

/-- Uncertainty of a weighted estimator; no equal-distribution or unbiasedness assumption. -/
theorem weighted_variance [Fintype ι] [Fintype O]
    (d : ι → ProbDistribution O) (w : ι → ℝ) (f : ι → O → ℝ) :
    productVariance d (fun os => ∑ i, w i * f i (os i)) =
      ∑ i, (w i)^2 * Finite.variance (d i) (f i) := by
  simpa only [variance_scale] using
    productVariance_sum d (fun i o => w i * f i o)

end QuantumExperiments.FiniteProbability
