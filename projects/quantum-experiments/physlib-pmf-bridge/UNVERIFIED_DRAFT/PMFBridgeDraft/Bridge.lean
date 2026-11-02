/-
UNVERIFIED_DRAFT — NOT COMPILED. Expected Lean v4.35.0; pins in ../../DRAFT.md.
Contains three explicit `sorry` obligations: B01, B02, B03. NOT accepted evidence.
Real Physlib imports only; no copied replacement for Prob or ProbDistribution.
-/
import QuantumInfo.ClassicalInfo.Distribution
import Mathlib.Probability.ProbabilityMassFunction.Constructions

noncomputable section
open scoped BigOperators

namespace QuantumExperiments.PMFBridgeDraft.Bridge

variable {α β : Type*}

/-- UNVERIFIED_DRAFT B01: transfer real finite normalization through ofReal. -/
def toPMF [Fintype α] (d : ProbDistribution α) : PMF α :=
  PMF.ofFintype (fun a => ENNReal.ofReal (d a : ℝ)) (by
    -- INCOMPLETE B01. Use nonnegativity and d.normalized, then the actual pinned
    -- finite-ofReal-sum lemma. Its declaration was not in the saved snapshot.
    sorry)

/-- UNVERIFIED_DRAFT B02: decode the finite PMF without an extra upper-bound input. -/
def ofPMF [Fintype α] (p : PMF α) : ProbDistribution α :=
  ProbDistribution.mk' (fun a => (p a).toReal)
    (fun _ => ENNReal.toReal_nonneg) (by
      -- INCOMPLETE B02. PMF.tsum_coe p = 1; convert finite tsum to sum and move
      -- toReal across it using p.apply_ne_top. Exact helper signatures pending.
      sorry)

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

/-- UNVERIFIED_DRAFT: no global coercions or instances are installed. -/
def equiv (α : Type*) [Fintype α] : ProbDistribution α ≃ PMF α where
  toFun := toPMF
  invFun := ofPMF
  left_inv := ofPMF_toPMF
  right_inv := toPMF_ofPMF

theorem toPMF_injective [Fintype α] : Function.Injective (toPMF (α := α)) :=
  (equiv α).injective

/-- UNVERIFIED_DRAFT B03: the conversion cost needed by the real-valued bind client.
Only the source carrier is finite here; the PMF target need not be finite. -/
theorem pmf_bind_toReal [Fintype α] (p : PMF α) (k : α → PMF β) (b : β) :
    (p.bind k b).toReal = ∑ a, (p a).toReal * (k a b).toReal := by
  -- INCOMPLETE B03. Start from PMF.bind_apply, then finite-tsum conversion,
  -- toReal of a finite sum and product. Each factor is finite by apply_ne_top.
  -- Do not hide this unresolved pointwise contract behind the definition below.
  sorry

end QuantumExperiments.PMFBridgeDraft.Bridge
