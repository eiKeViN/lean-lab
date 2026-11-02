/- Measurement copy: generated from the published declarations; do not edit manually. -/
import CostStudy.Common

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace QuantumExperiments.PMFComparison.Finite

variable {α ι O I : Type*}

def productMean [Fintype ι] [Fintype O] (d : ι → ProbDistribution O)
    (f : (ι → O) → ℝ) : ℝ := by
  classical
  exact ∑ os, (∏ i, (d i (os i) : ℝ)) * f os

lemma mean_center [Fintype α] (d : ProbDistribution α) (f : α → ℝ) :
    mean d (fun a => f a - mean d f) = 0 := by
  simp only [mean, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul,
    d.normalized, one_mul, sub_self]

lemma productMean_prod [Fintype ι] [Fintype O] (d : ι → ProbDistribution O)
    (f : ι → O → ℝ) : productMean d (fun os => ∏ i, f i (os i)) =
      ∏ i, mean (d i) (f i) := by
  classical
  simp only [productMean, ← Finset.prod_mul_distrib]
  simpa only [Fintype.piFinset_univ, mean] using
    Finset.sum_prod_piFinset (Finset.univ : Finset O)
      (fun i o => (d i o : ℝ) * f i o)

lemma productMean_coordinate [Fintype ι] [Fintype O] (d : ι → ProbDistribution O)
    (i : ι) (f : O → ℝ) : productMean d (fun os => f (os i)) = mean (d i) f := by
  classical
  have h := productMean_prod d (fun k o => if k = i then f o else 1)
  simpa [mean, ProbDistribution.normalized] using h

lemma productMean_pair [Fintype ι] [Fintype O] (d : ι → ProbDistribution O)
    (i j : ι) (hij : i ≠ j) (f g : O → ℝ) :
    productMean d (fun os => f (os i) * g (os j)) = mean (d i) f * mean (d j) g := by
  classical
  have h := productMean_prod d (fun k o =>
    (if k = i then f o else 1) * (if k = j then g o else 1))
  have hk (k : ι) : mean (d k) (fun o =>
      (if k = i then f o else 1) * (if k = j then g o else 1)) =
      (if k = i then mean (d i) f else 1) * (if k = j then mean (d j) g else 1) := by
    by_cases hi : k = i
    · subst k; simp [hij, mean]
    · by_cases hj : k = j
      · subst k; simp [hi, mean]
      · simp [hi, hj, mean, ProbDistribution.normalized]
  simp only [hk, Finset.prod_mul_distrib] at h
  simpa using h

lemma productMean_sum [Fintype ι] [Fintype O] {κ : Type*} [Fintype κ]
    (d : ι → ProbDistribution O) (f : κ → (ι → O) → ℝ) :
    productMean d (fun os => ∑ k, f k os) = ∑ k, productMean d (f k) := by
  simp only [productMean, Finset.mul_sum]
  exact Finset.sum_comm

lemma productMean_sum_coordinate [Fintype ι] [Fintype O]
    (d : ι → ProbDistribution O) (f : ι → O → ℝ) :
    productMean d (fun os => ∑ i, f i (os i)) = ∑ i, mean (d i) (f i) := by
  rw [productMean_sum]
  simp only [productMean_coordinate]

end QuantumExperiments.PMFComparison.Finite
