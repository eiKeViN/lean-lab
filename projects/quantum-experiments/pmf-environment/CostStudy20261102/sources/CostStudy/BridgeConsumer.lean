/- Measurement copy: generated from the published declarations; do not edit manually. -/
import CostStudy.BridgeBase

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace QuantumExperiments.PMFBridgeDraft.ChannelStatistics
open ChannelProduct
variable {O : Type*} [Fintype O] [MeasurableSpace O] [MeasurableSingletonClass O]
variable {I : Type*} {n : ℕ}

def totalScore (g : Fin n → O → ℝ) (os : Fin n → O) : ℝ := ∑ k, g k (os k)

theorem variance_totalScore_of_memLp (C : DMChannel I O) (is : Fin n → I)
    (g : Fin n → O → ℝ) (hg : ∀ k, MemLp (g k) 2 (law (C.symb_dist (is k)))) :
    ProbabilityTheory.variance (totalScore g) (law (C.on_fin I O is)) =
      ∑ k, ProbabilityTheory.variance (g k) (law (C.symb_dist (is k))) := by
  rw [law_on_fin_eq_pi]
  have hscore : totalScore g = ∑ k, fun os => g k (os k) := by
    funext os
    simp only [totalScore, Finset.sum_apply]
  rw [hscore]
  exact ProbabilityTheory.variance_sum_pi
      (μ := fun k : Fin n => law (C.symb_dist (is k))) (X := g) hg

theorem variance_totalScore (C : DMChannel I O) (is : Fin n → I)
    (g : Fin n → O → ℝ) :
    ProbabilityTheory.variance (totalScore g) (law (C.on_fin I O is)) =
      ∑ k, ProbabilityTheory.variance (g k) (law (C.symb_dist (is k))) := by
  exact variance_totalScore_of_memLp C is g
    (fun k => score_memLp_two (C.symb_dist (is k)) (g k))

end QuantumExperiments.PMFBridgeDraft.ChannelStatistics
namespace QuantumExperiments.PMFComparison.Transport
open PMFBridgeDraft PMFBridgeDraft.ChannelProduct PMFBridgeDraft.ChannelStatistics
variable {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]

theorem variance_on_fin {I O : Type*} [Fintype O] {n : ℕ}
    (C : DMChannel I O) (is : Fin n → I) (g : Fin n → O → ℝ) :
    Finite.variance (C.on_fin I O is) (fun os => ∑ k, g k (os k)) =
      ∑ k, Finite.variance (C.symb_dist (is k)) (g k) := by
  let : MeasurableSpace O := ⊤
  let : MeasurableSingletonClass O := ⟨fun _ => MeasurableSet.of_discrete⟩
  change Finite.variance (C.on_fin I O is) (totalScore g) = _
  simpa only [variance_eq_finite] using variance_totalScore C is g

end QuantumExperiments.PMFComparison.Transport
