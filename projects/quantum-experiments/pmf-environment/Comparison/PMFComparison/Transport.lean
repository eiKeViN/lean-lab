import PMFComparison.Moments
import PMFBridgeDraft.ChannelStatistics

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace QuantumExperiments.PMFComparison.Transport
open PMFBridgeDraft PMFBridgeDraft.ChannelProduct PMFBridgeDraft.ChannelStatistics

variable {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]

theorem integral_eq_mean (d : ProbDistribution α) (g : α → ℝ) :
    (∫ a, g a ∂law d) = Finite.mean d g := integral_real d g

theorem variance_eq_finite (d : ProbDistribution α) (g : α → ℝ) :
    ProbabilityTheory.variance g (law d) = Finite.variance d g := by
  rw [ProbabilityTheory.variance_eq_integral (measurable_of_finite g).aemeasurable]
  rw [integral_eq_mean, integral_eq_mean]
  rfl

/-- Same finite-only interface as the direct proof; discrete measurability is local. -/
theorem variance_on_fin {I O : Type*} [Fintype O] {n : ℕ}
    (C : DMChannel I O) (is : Fin n → I) (g : Fin n → O → ℝ) :
    Finite.variance (C.on_fin I O is) (fun os => ∑ k, g k (os k)) =
      ∑ k, Finite.variance (C.symb_dist (is k)) (g k) := by
  let : MeasurableSpace O := ⊤
  let : MeasurableSingletonClass O := ⟨fun _ => MeasurableSet.of_discrete⟩
  change Finite.variance (C.on_fin I O is) (totalScore g) = _
  simpa only [variance_eq_finite] using variance_totalScore C is g

end QuantumExperiments.PMFComparison.Transport
