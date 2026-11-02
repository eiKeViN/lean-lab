import PMFComparison.Transport

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace QuantumExperiments.PMFComparison.Transport
open PMFBridgeDraft PMFBridgeDraft.ChannelProduct PMFBridgeDraft.ChannelStatistics

variable {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]

theorem covariance_eq_finite (d : ProbDistribution α) (f g : α → ℝ) :
    ProbabilityTheory.covariance f g (law d) = Finite.covariance d f g := by
  simp only [ProbabilityTheory.covariance, integral_eq_mean, Finite.covariance]

theorem covariance_polarization (d : ProbDistribution α) (f g : α → ℝ) :
    Finite.variance d (fun a => f a + g a) =
      Finite.variance d f + Finite.variance d g + 2 * Finite.covariance d f g := by
  have hp := ProbabilityTheory.variance_add (score_memLp_two d f) (score_memLp_two d g)
  have hfun : f + g = (fun a => f a + g a) := rfl
  rw [hfun] at hp
  simpa only [variance_eq_finite, covariance_eq_finite, add_right_comm] using hp

/-- Maintenance delta: two-score covariance, reusing variance by polarization. -/
theorem covariance_on_fin {I O : Type*} [Fintype O] {n : ℕ}
    (C : DMChannel I O) (is : Fin n → I) (g h : Fin n → O → ℝ) :
    Finite.covariance (C.on_fin I O is) (fun os => ∑ k, g k (os k))
      (fun os => ∑ k, h k (os k)) =
      ∑ k, Finite.covariance (C.symb_dist (is k)) (g k) (h k) := by
  let : MeasurableSpace O := ⊤
  let : MeasurableSingletonClass O := ⟨fun _ => MeasurableSet.of_discrete⟩
  have hsum := variance_on_fin C is (fun k o => g k o + h k o)
  simp only [Finset.sum_add_distrib] at hsum
  rw [covariance_polarization] at hsum
  simp_rw [covariance_polarization] at hsum
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  have hg := variance_on_fin C is g
  have hh := variance_on_fin C is h
  linarith

end QuantumExperiments.PMFComparison.Transport
