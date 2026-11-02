/- Measurement copy: generated from the published declarations; do not edit manually. -/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Basic.ENNReal.BigOperators
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.MeasureTheory.Measure.Dirac.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import QuantumInfo.ClassicalInfo.Channel
import QuantumInfo.ClassicalInfo.Distribution

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace QuantumExperiments.PMFComparison.Finite

variable {α : Type*} [Fintype α]

def mean (d : ProbDistribution α) (f : α → ℝ) : ℝ :=
  ∑ a, (d a : ℝ) * f a

def variance (d : ProbDistribution α) (f : α → ℝ) : ℝ :=
  mean d (fun a => (f a - mean d f)^2)

end QuantumExperiments.PMFComparison.Finite
