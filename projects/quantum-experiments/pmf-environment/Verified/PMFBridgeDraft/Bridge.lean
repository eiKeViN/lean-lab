/-
Explicit finite equivalence with mathlib PMF and real-valued bind observation.
Revised from the preserved UNVERIFIED_DRAFT; validation evidence is recorded separately.
-/
import QuantumInfo.ClassicalInfo.Distribution
import Mathlib.Probability.ProbabilityMassFunction.Constructions

noncomputable section
open scoped BigOperators

namespace QuantumExperiments.PMFBridgeDraft.Bridge

variable {α β : Type*}

/-- Transfer real finite normalization through ofReal. -/
def toPMF [Fintype α] (d : ProbDistribution α) : PMF α :=
  PMF.ofFintype (fun a => ENNReal.ofReal (d a : ℝ)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => Prob.zero_le_coe)]
    rw [d.normalized, ENNReal.ofReal_one])

/-- Decode the finite PMF without an extra upper-bound input. -/
def ofPMF [Fintype α] (p : PMF α) : ProbDistribution α :=
  ProbDistribution.mk' (fun a => (p a).toReal)
    (fun _ => ENNReal.toReal_nonneg) (by
      rw [← ENNReal.toReal_sum (fun a _ => p.apply_ne_top a)]
      have h : ∑ a, p a = 1 := by simpa only [tsum_fintype] using p.tsum_coe
      rw [h, ENNReal.toReal_one])

@[simp] theorem toPMF_apply [Fintype α] (d : ProbDistribution α) (a : α) :
    toPMF d a = ENNReal.ofReal (d a : ℝ) := rfl

@[simp] theorem ofPMF_apply [Fintype α] (p : PMF α) (a : α) :
    (ofPMF p a : ℝ) = (p a).toReal := rfl

@[simp] theorem toPMF_toReal [Fintype α] (d : ProbDistribution α) (a : α) :
    (toPMF d a).toReal = (d a : ℝ) := by
  rw [toPMF_apply]
  exact ENNReal.toReal_ofReal Prob.zero_le_coe

@[simp] theorem ofPMF_toPMF [Fintype α] (d : ProbDistribution α) :
    ofPMF (toPMF d) = d := by
  apply ProbDistribution.ext
  intro a
  apply Subtype.ext
  change (ENNReal.ofReal (d a : ℝ)).toReal = (d a : ℝ)
  exact ENNReal.toReal_ofReal Prob.zero_le_coe

@[simp] theorem toPMF_ofPMF [Fintype α] (p : PMF α) :
    toPMF (ofPMF p) = p := by
  apply PMF.ext
  intro a
  change ENNReal.ofReal ((p a).toReal) = p a
  exact ENNReal.ofReal_toReal (p.apply_ne_top a)

/-- No global coercions or instances are installed. -/
def equiv (α : Type*) [Fintype α] : ProbDistribution α ≃ PMF α where
  toFun := toPMF
  invFun := ofPMF
  left_inv := ofPMF_toPMF
  right_inv := toPMF_ofPMF

theorem toPMF_injective [Fintype α] : Function.Injective (toPMF (α := α)) :=
  (equiv α).injective

/-- The conversion cost needed by the real-valued bind client.
Only the source carrier is finite here; the PMF target need not be finite. -/
theorem pmf_bind_toReal [Fintype α] (p : PMF α) (k : α → PMF β) (b : β) :
    (p.bind k b).toReal = ∑ a, (p a).toReal * (k a b).toReal := by
  rw [PMF.bind_apply, tsum_fintype]
  rw [ENNReal.toReal_sum (fun a _ => ENNReal.mul_ne_top (p.apply_ne_top a) ((k a).apply_ne_top b))]
  simp only [ENNReal.toReal_mul]

end QuantumExperiments.PMFBridgeDraft.Bridge
