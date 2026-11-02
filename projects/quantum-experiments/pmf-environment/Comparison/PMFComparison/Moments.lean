/- Common finite-sum observable definitions; neither proof route is imported. -/
import QuantumInfo.ClassicalInfo.Channel

noncomputable section
open scoped BigOperators

namespace QuantumExperiments.PMFComparison.Finite
variable {α : Type*} [Fintype α]

def mean (d : ProbDistribution α) (f : α → ℝ) : ℝ :=
  ∑ a, (d a : ℝ) * f a

def variance (d : ProbDistribution α) (f : α → ℝ) : ℝ :=
  mean d (fun a => (f a - mean d f)^2)

def covariance (d : ProbDistribution α) (f g : α → ℝ) : ℝ :=
  mean d (fun a => (f a - mean d f) * (g a - mean d g))

end QuantumExperiments.PMFComparison.Finite
