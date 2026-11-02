import FiniteProbability.Core
import PMFComparison.TransportCovariance
import Mathlib.MeasureTheory.Integral.Pi

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace QuantumExperiments.FiniteProbability
open PMFBridgeDraft.ChannelProduct PMFBridgeDraft.ChannelStatistics
open PMFComparison.Transport

open PMFComparison

variable {α ι O : Type*}

/-- Centering is finite linear algebra; no measure conversion is needed. -/
theorem mean_center [Fintype α] (d : ProbDistribution α) (f : α → ℝ) :
    Finite.mean d (fun a => f a - Finite.mean d f) = 0 := by
  simp only [Finite.mean, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul,
    d.normalized, one_mul, sub_self]

/-- General finite-index product moments, proved by measure-theoretic Fubini. -/
theorem mean_product_prod [Fintype ι] [Fintype O] [Fintype (ι → O)] (d : ι → ProbDistribution O)
    (f : ι → O → ℝ) :
    Finite.mean (product d) (fun os => ∏ i, f i (os i)) = ∏ i, Finite.mean (d i) (f i) := by
  let : MeasurableSpace O := ⊤
  let : MeasurableSingletonClass O := ⟨fun _ => MeasurableSet.of_discrete⟩
  rw [← integral_eq_mean, law_product_eq_pi, integral_fintype_prod_eq_prod]
  simp only [integral_eq_mean]

/-- Marginal observations need neither an explicit measure nor measurability evidence. -/
theorem mean_product_coordinate [Fintype ι] [Fintype O] [Fintype (ι → O)] (d : ι → ProbDistribution O)
    (i : ι) (f : O → ℝ) :
    Finite.mean (product d) (fun os => f (os i)) = Finite.mean (d i) f := by
  let : MeasurableSpace O := ⊤
  let : MeasurableSingletonClass O := ⟨fun _ => MeasurableSet.of_discrete⟩
  rw [← integral_eq_mean, law_product_eq_pi,
    integral_comp_eval (measurable_of_finite f).aestronglyMeasurable, integral_eq_mean]

/-- Distinct-coordinate cross moments, specializing the product-moment interface. -/
theorem mean_product_pair [Fintype ι] [Fintype O] [Fintype (ι → O)] (d : ι → ProbDistribution O)
    (i j : ι) (hij : i ≠ j) (f g : O → ℝ) :
    Finite.mean (product d) (fun os => f (os i) * g (os j)) =
      Finite.mean (d i) f * Finite.mean (d j) g := by
  classical
  have h := mean_product_prod d (fun k o =>
    (if k = i then f o else 1) * (if k = j then g o else 1))
  have hk (k : ι) : Finite.mean (d k) (fun o =>
      (if k = i then f o else 1) * (if k = j then g o else 1)) =
      (if k = i then Finite.mean (d i) f else 1) *
      (if k = j then Finite.mean (d j) g else 1) := by
    by_cases hi : k = i
    · subst k; simp [hij, Finite.mean]
    · by_cases hj : k = j
      · subst k; simp [hi, Finite.mean]
      · simp [hi, hj, Finite.mean, ProbDistribution.normalized]
  simp only [hk, Finset.prod_mul_distrib] at h
  simpa using h

/-- Finite linearity is shared algebra, independent of the product representation. -/
theorem mean_sum [Fintype α] {κ : Type*} [Fintype κ]
    (d : ProbDistribution α) (f : κ → α → ℝ) :
    Finite.mean d (fun a => ∑ k, f k a) = ∑ k, Finite.mean d (f k) := by
  simp only [Finite.mean, Finset.mul_sum]
  exact Finset.sum_comm

/-- Expected total score on an arbitrary finite family. -/
theorem mean_product_sum_coordinate [Fintype ι] [Fintype O] [Fintype (ι → O)]
    (d : ι → ProbDistribution O) (f : ι → O → ℝ) :
    Finite.mean (product d) (fun os => ∑ i, f i (os i)) = ∑ i, Finite.mean (d i) (f i) := by
  rw [mean_sum]
  simp only [mean_product_coordinate]

/-- Variance additivity with all finite-carrier analytic certificates internal. -/
theorem variance_sum [Fintype ι] [Fintype O] [Fintype (ι → O)]
    (d : ι → ProbDistribution O) (f : ι → O → ℝ) :
    Finite.variance (product d) (fun os => ∑ i, f i (os i)) =
      ∑ i, Finite.variance (d i) (f i) := by
  let : MeasurableSpace O := ⊤
  let : MeasurableSingletonClass O := ⟨fun _ => MeasurableSet.of_discrete⟩
  rw [← variance_eq_finite, law_product_eq_pi]
  have h := ProbabilityTheory.variance_sum_pi
    (μ := fun i => law (d i)) (X := f) (fun i => score_memLp_two (d i) (f i))
  have hfun : (∑ i, fun os : ι → O => f i (os i)) =
      (fun os => ∑ i, f i (os i)) := by
    funext os
    simp only [Finset.sum_apply]
  rw [hfun] at h
  simpa only [variance_eq_finite] using h

/-- Covariance of two additive scores on an arbitrary finite product. -/
theorem covariance_sum [Fintype ι] [Fintype O] [Fintype (ι → O)]
    (d : ι → ProbDistribution O) (f g : ι → O → ℝ) :
    Finite.covariance (product d) (fun os => ∑ i, f i (os i))
      (fun os => ∑ i, g i (os i)) = ∑ i, Finite.covariance (d i) (f i) (g i) := by
  let : MeasurableSpace O := ⊤
  let : MeasurableSingletonClass O := ⟨fun _ => MeasurableSet.of_discrete⟩
  have hsum := variance_sum d (fun i o => f i o + g i o)
  simp only [Finset.sum_add_distrib] at hsum
  rw [covariance_polarization] at hsum
  simp_rw [covariance_polarization] at hsum
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  have hf := variance_sum d f
  have hg := variance_sum d g
  linarith

end QuantumExperiments.FiniteProbability
