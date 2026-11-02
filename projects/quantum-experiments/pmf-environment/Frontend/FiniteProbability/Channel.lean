/- Real Physlib channel clients are specializations of the general finite family API. -/
import FiniteProbability.Scores

noncomputable section
open scoped BigOperators
namespace QuantumExperiments.FiniteProbability
open PMFComparison
variable {I O : Type*} [Fintype O] {n : ℕ}

/-- Export the previously local connection between channel means and product means. -/
theorem mean_on_fin (C : DMChannel I O) (is : Fin n → I) (f : (Fin n → O) → ℝ) :
    Finite.mean (C.on_fin I O is) f = productMean (fun i => C.symb_dist (is i)) f := by
  rw [on_fin_eq_product, productMean_eq_mean]

theorem mean_score_on_fin (C : DMChannel I O) (is : Fin n → I) (g : Fin n → O → ℝ) :
    Finite.mean (C.on_fin I O is) (fun os => ∑ i, g i (os i)) =
      ∑ i, Finite.mean (C.symb_dist (is i)) (g i) := by
  rw [mean_on_fin, productMean_sum_coordinate]

theorem cross_moment_on_fin (C : DMChannel I O) (is : Fin n → I)
    (i j : Fin n) (hij : i ≠ j) (f g : O → ℝ) :
    Finite.mean (C.on_fin I O is) (fun os => f (os i) * g (os j)) =
      Finite.mean (C.symb_dist (is i)) f * Finite.mean (C.symb_dist (is j)) g := by
  rw [mean_on_fin]
  exact productMean_pair _ i j hij f g

theorem variance_on_fin (C : DMChannel I O) (is : Fin n → I) (g : Fin n → O → ℝ) :
    Finite.variance (C.on_fin I O is) (fun os => ∑ i, g i (os i)) =
      ∑ i, Finite.variance (C.symb_dist (is i)) (g i) := by
  rw [on_fin_eq_product]
  exact variance_sum _ g

theorem covariance_on_fin (C : DMChannel I O) (is : Fin n → I) (f g : Fin n → O → ℝ) :
    Finite.covariance (C.on_fin I O is) (fun os => ∑ i, f i (os i))
      (fun os => ∑ i, g i (os i)) =
      ∑ i, Finite.covariance (C.symb_dist (is i)) (f i) (g i) := by
  rw [on_fin_eq_product]
  exact covariance_sum _ f g

theorem weighted_variance_on_fin (C : DMChannel I O) (is : Fin n → I)
    (w : Fin n → ℝ) (g : Fin n → O → ℝ) :
    Finite.variance (C.on_fin I O is) (fun os => ∑ i, w i * g i (os i)) =
      ∑ i, (w i)^2 * Finite.variance (C.symb_dist (is i)) (g i) := by
  simpa only [variance_scale] using variance_on_fin C is (fun i o => w i * g i o)

end QuantumExperiments.FiniteProbability
