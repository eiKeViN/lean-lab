/- Maintenance consumer: covariance of two additive scores, by finite-sum polarization. -/
import PMFComparison.Finite

noncomputable section
open scoped BigOperators

namespace QuantumExperiments.PMFComparison.Finite
variable {α : Type*} [Fintype α]

lemma mean_add (d : ProbDistribution α) (f g : α → ℝ) :
    mean d (fun a => f a + g a) = mean d f + mean d g := by
  simp only [mean, mul_add, Finset.sum_add_distrib]

lemma variance_add (d : ProbDistribution α) (f g : α → ℝ) :
    variance d (fun a => f a + g a) =
      variance d f + variance d g + 2 * covariance d f g := by
  unfold variance covariance
  rw [mean_add]
  have hp (a : α) : (f a + g a - (mean d f + mean d g)) ^ 2 =
      (f a - mean d f) ^ 2 + (g a - mean d g) ^ 2 +
        2 * ((f a - mean d f) * (g a - mean d g)) := by ring
  simp_rw [hp]
  simp only [mean, mul_add, Finset.sum_add_distrib]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  ring

/-- The changed consumer reuses the variance theorem, without a new independence proof. -/
theorem covariance_on_fin {I O : Type*} [Fintype O] {n : ℕ}
    (C : DMChannel I O) (is : Fin n → I) (g h : Fin n → O → ℝ) :
    covariance (C.on_fin I O is) (fun os => ∑ k, g k (os k))
      (fun os => ∑ k, h k (os k)) =
      ∑ k, covariance (C.symb_dist (is k)) (g k) (h k) := by
  have hsum := variance_on_fin C is (fun k o => g k o + h k o)
  simp only [Finset.sum_add_distrib] at hsum
  rw [variance_add] at hsum
  simp_rw [variance_add] at hsum
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  have hg := variance_on_fin C is g
  have hh := variance_on_fin C is h
  linarith

end QuantumExperiments.PMFComparison.Finite
