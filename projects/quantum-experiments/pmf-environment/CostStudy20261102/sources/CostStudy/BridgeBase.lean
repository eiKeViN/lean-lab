/- Measurement copy: generated from the published declarations; do not edit manually. -/
import CostStudy.Common

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace QuantumExperiments.PMFBridgeDraft.Bridge

variable {α β : Type*}

def toPMF [Fintype α] (d : ProbDistribution α) : PMF α :=
  PMF.ofFintype (fun a => ENNReal.ofReal (d a : ℝ)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => Prob.zero_le_coe)]
    rw [d.normalized, ENNReal.ofReal_one])

@[simp] theorem toPMF_apply [Fintype α] (d : ProbDistribution α) (a : α) :
    toPMF d a = ENNReal.ofReal (d a : ℝ) := rfl

@[simp] theorem toPMF_toReal [Fintype α] (d : ProbDistribution α) (a : α) :
    (toPMF d a).toReal = (d a : ℝ) := by
  rw [toPMF_apply]
  exact ENNReal.toReal_ofReal Prob.zero_le_coe

end QuantumExperiments.PMFBridgeDraft.Bridge
namespace QuantumExperiments.PMFBridgeDraft.ChannelProduct

variable {α : Type*}

def law [Fintype α] [MeasurableSpace α] (d : ProbDistribution α) : Measure α :=
  (Bridge.toPMF d).toMeasure

instance law_probability [Fintype α] [MeasurableSpace α] (d : ProbDistribution α) :
    IsProbabilityMeasure (law d) := by
  unfold law
  infer_instance

@[simp] theorem law_singleton [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (d : ProbDistribution α) (a : α) :
    law d {a} = ENNReal.ofReal (d a : ℝ) := by
  exact (PMF.toMeasure_apply_singleton (Bridge.toPMF d) a
    (MeasurableSet.singleton a)).trans (Bridge.toPMF_apply d a)

end QuantumExperiments.PMFBridgeDraft.ChannelProduct
namespace QuantumExperiments.PMFBridgeDraft.ChannelProduct

variable {I O : Type*} [Fintype O] {n : ℕ}

theorem on_fin_real_apply (C : DMChannel I O) (is : Fin n → I) (os : Fin n → O) :
    (C.on_fin I O is os : ℝ) = ∏ k, (C.symb_dist (is k) (os k) : ℝ) := rfl

end QuantumExperiments.PMFBridgeDraft.ChannelProduct
namespace QuantumExperiments.PMFBridgeDraft.ChannelProduct

variable {I O : Type*} [Fintype O] {n : ℕ}
variable [MeasurableSpace O] [MeasurableSingletonClass O]

theorem law_on_fin_eq_pi (C : DMChannel I O) (is : Fin n → I) :
    law (C.on_fin I O is) =
      Measure.pi (fun k : Fin n => law (C.symb_dist (is k))) := by
  classical
  apply Measure.ext_of_singleton
  intro os
  rw [law_singleton, Measure.pi_singleton]
  simp only [law_singleton]
  rw [on_fin_real_apply]
  exact ENNReal.ofReal_prod_of_nonneg (fun _ _ => Prob.zero_le_coe)

end QuantumExperiments.PMFBridgeDraft.ChannelProduct
namespace QuantumExperiments.PMFBridgeDraft.ChannelStatistics
open ChannelProduct
variable {O : Type*} [Fintype O] [MeasurableSpace O] [MeasurableSingletonClass O]

theorem integral_real (d : ProbDistribution O) (g : O → ℝ) :
    (∫ o, g o ∂law d) = ∑ o, (d o : ℝ) * g o := by
  simpa only [law, Bridge.toPMF_toReal, smul_eq_mul] using
    PMF.integral_eq_sum (Bridge.toPMF d) g

theorem score_memLp_two (d : ProbDistribution O) (g : O → ℝ) : MemLp g 2 (law d) := by
  classical
  refine MemLp.of_bound (measurable_of_finite g).aemeasurable.aestronglyMeasurable
    (∑ o, ‖g o‖) ?_
  exact Filter.Eventually.of_forall fun o =>
    Finset.single_le_sum (fun x _ => norm_nonneg (g x)) (Finset.mem_univ o)

end QuantumExperiments.PMFBridgeDraft.ChannelStatistics
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

end QuantumExperiments.PMFComparison.Transport
