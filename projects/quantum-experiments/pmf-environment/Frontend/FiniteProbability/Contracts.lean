/- Audit-only comparison: native proofs are not imported by the public entry point. -/
import FiniteProbability.Clients
import PMFComparison.Contracts

noncomputable section
open scoped BigOperators
namespace QuantumExperiments.FiniteProbability.Contracts
open PMFComparison
variable {ι O I : Type*} [Fintype ι] [Fintype O]

theorem productMean_agrees (d : ι → ProbDistribution O) (f : (ι → O) → ℝ) :
    productMean d f = Finite.productMean d f := rfl

theorem same_product_moment (d : ι → ProbDistribution O) (f : ι → O → ℝ) :
    Finite.productMean d (fun os => ∏ i, f i (os i)) = ∏ i, Finite.mean (d i) (f i) :=
  productMean_prod d f

theorem same_coordinate_mean (d : ι → ProbDistribution O) (i : ι) (f : O → ℝ) :
    Finite.productMean d (fun os => f (os i)) = Finite.mean (d i) f :=
  productMean_coordinate d i f

theorem same_cross_moment (d : ι → ProbDistribution O) (i j : ι) (hij : i ≠ j) (f g : O → ℝ) :
    Finite.productMean d (fun os => f (os i) * g (os j)) =
      Finite.mean (d i) f * Finite.mean (d j) g := productMean_pair d i j hij f g

theorem same_sum {κ : Type*} [Fintype κ] (d : ι → ProbDistribution O)
    (f : κ → (ι → O) → ℝ) :
    Finite.productMean d (fun os => ∑ k, f k os) = ∑ k, Finite.productMean d (f k) :=
  productMean_sum d f

theorem same_score_mean (d : ι → ProbDistribution O) (f : ι → O → ℝ) :
    Finite.productMean d (fun os => ∑ i, f i (os i)) = ∑ i, Finite.mean (d i) (f i) :=
  productMean_sum_coordinate d f

theorem same_center {α : Type*} [Fintype α] (d : ProbDistribution α) (f : α → ℝ) :
    Finite.mean d (fun a => f a - Finite.mean d f) = 0 := mean_center d f

theorem same_variance {n : ℕ} (C : DMChannel I O) (is : Fin n → I) (g : Fin n → O → ℝ) :
    PMFComparison.Contracts.VarianceClaim C is g := variance_on_fin C is g

theorem same_covariance {n : ℕ} (C : DMChannel I O) (is : Fin n → I) (f g : Fin n → O → ℝ) :
    PMFComparison.Contracts.CovarianceClaim C is f g := covariance_on_fin C is f g

end QuantumExperiments.FiniteProbability.Contracts
