/- Finite product distributions, with an explicit measure escape hatch. -/
import PMFBridgeDraft.ChannelStatistics
import PMFComparison.Moments

noncomputable section
open scoped BigOperators
open MeasureTheory
attribute [local instance] Classical.decEq
namespace QuantumExperiments.FiniteProbability
open PMFBridgeDraft.ChannelProduct

variable {ι O : Type*} [Fintype ι] [Fintype O]

/-- Product of a finite family; no channel or measurable structure is required. -/
def product [Fintype (ι → O)] (d : ι → ProbDistribution O) : ProbDistribution (ι → O) := by
  classical
  exact ProbDistribution.mk' (fun os => ∏ i, (d i (os i) : ℝ))
    (fun _ => Finset.prod_nonneg fun _ _ => Prob.zero_le_coe) (by
      have h := Finset.sum_prod_piFinset (Finset.univ : Finset O)
        (fun i o => (d i o : ℝ))
      simp only [Fintype.piFinset_univ] at h
      have hn : (∏ i, ∑ o, (d i o : ℝ)) = 1 :=
        Finset.prod_eq_one fun i _ => (d i).normalized
      convert h.trans hn using 1
      congr 1
      ext os
      simp)

variable [Fintype (ι → O)]

@[simp] theorem product_apply (d : ι → ProbDistribution O) (os : ι → O) :
    (product d os : ℝ) = ∏ i, (d i (os i) : ℝ) := rfl

/-- The real upstream channel output is a special case of the general product. -/
theorem on_fin_eq_product {I : Type*} {n : ℕ} (C : DMChannel I O) (is : Fin n → I) :
    C.on_fin I O is = product (fun i => C.symb_dist (is i)) := by
  apply ProbDistribution.ext
  intro os
  apply Subtype.ext
  rfl

variable [MeasurableSpace O] [MeasurableSingletonClass O]

/-- Explicit measure interface for clients that need mathlib probability theory. -/
theorem law_product_eq_pi (d : ι → ProbDistribution O) :
    law (product d) = Measure.pi (fun i => law (d i)) := by
  classical
  apply Measure.ext_of_singleton
  intro os
  rw [law_singleton, Measure.pi_singleton]
  simp only [law_singleton, product_apply]
  exact ENNReal.ofReal_prod_of_nonneg (fun _ _ => Prob.zero_le_coe)

theorem coordinates_independent (d : ι → ProbDistribution O) :
    ProbabilityTheory.iIndepFun (fun (i : ι) (os : ι → O) => os i) (law (product d)) := by
  rw [law_product_eq_pi]
  exact ProbabilityTheory.iIndepFun_pi
    (μ := fun i => law (d i)) (X := fun _ => id)
    (fun _ => measurable_id.aemeasurable)

end QuantumExperiments.FiniteProbability
