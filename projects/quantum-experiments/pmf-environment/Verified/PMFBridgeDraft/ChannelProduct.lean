/-
The actual DMChannel.on_fin at a fixed input: product law and independent coordinates.
Revised from the preserved UNVERIFIED_DRAFT; validation evidence is recorded separately.
-/
import QuantumInfo.ClassicalInfo.Channel
import PMFBridgeDraft.Bridge
import Mathlib.Basic.ENNReal.BigOperators
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Dirac.Basic
import Mathlib.Probability.Independence.Basic

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace QuantumExperiments.PMFBridgeDraft.ChannelProduct

variable {α : Type*}

/-- The PMF measure of the existing finite distribution, not a new distribution. -/
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

variable {I O : Type*} [Fintype O] {n : ℕ}

/-- Read the actual upstream mk' definition, retaining its existing normalization. -/
theorem on_fin_real_apply (C : DMChannel I O) (is : Fin n → I) (os : Fin n → O) :
    (C.on_fin I O is os : ℝ) = ∏ k, (C.symb_dist (is k) (os k) : ℝ) := rfl

variable [MeasurableSpace O] [MeasurableSingletonClass O]

/-- Fixed-input law = product measure, from singleton masses.
Probability/sigma-finiteness are derived from PMF.toMeasure, not caller premises. -/
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

/-- Independent coordinates for a FIXED input; not necessarily identically distributed. -/
theorem coordinates_iIndepFun (C : DMChannel I O) (is : Fin n → I) :
    ProbabilityTheory.iIndepFun
      (fun (k : Fin n) (os : Fin n → O) => os k) (law (C.on_fin I O is)) := by
  rw [law_on_fin_eq_pi]
  exact ProbabilityTheory.iIndepFun_pi
    (μ := fun k : Fin n => law (C.symb_dist (is k))) (X := fun _ => id)
    (fun _ => measurable_id.aemeasurable)

end QuantumExperiments.PMFBridgeDraft.ChannelProduct
