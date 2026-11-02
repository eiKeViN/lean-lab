/- Measurement copy: generated from the published declarations; do not edit manually. -/
import CostStudy.NativeBase

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace QuantumExperiments.PMFComparison.Finite

variable {α ι O I : Type*}

lemma productMean_centered_sum_sq [Fintype ι] [Fintype O]
    (d : ι → ProbDistribution O) (f : ι → O → ℝ)
    (hf : ∀ i, mean (d i) (f i) = 0) :
    productMean d (fun os => (∑ i, f i (os i)) ^ 2) =
      ∑ i, mean (d i) (fun o => f i o ^ 2) := by
  classical
  simp only [pow_two, Finset.sum_mul_sum, productMean_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_eq_single i]
  · exact productMean_coordinate d i (fun o => f i o * f i o)
  · intro j hj hji
    rw [productMean_pair d i j (Ne.symm hji), hf i, zero_mul]
  · simp

theorem variance_on_fin [Fintype O] {n : ℕ} (C : DMChannel I O) (is : Fin n → I)
    (g : Fin n → O → ℝ) :
    variance (C.on_fin I O is) (fun os => ∑ i, g i (os i)) =
      ∑ i, variance (C.symb_dist (is i)) (g i) := by
  classical
  let d : Fin n → ProbDistribution O := fun i => C.symb_dist (is i)
  have hon (f : (Fin n → O) → ℝ) : mean (C.on_fin I O is) f = productMean d f := by
    unfold mean productMean
    apply Finset.sum_congr
    · ext os; simp
    · intro os _; rfl
  unfold variance
  simp only [hon]
  rw [productMean_sum_coordinate]
  simp only [← Finset.sum_sub_distrib]
  exact productMean_centered_sum_sq d (fun i o => g i o - mean (d i) (g i))
    (fun i => mean_center (d i) (g i))

end QuantumExperiments.PMFComparison.Finite
