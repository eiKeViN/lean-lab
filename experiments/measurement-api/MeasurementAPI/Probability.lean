module

public import PMFBridgeDraft.Bridge

@[expose] public section

/-! Deterministic outcome transport through the existing finite PMF equivalence. -/

noncomputable section
open Classical
open scoped BigOperators
open QuantumExperiments.PMFBridgeDraft

namespace ProbDistribution

variable {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]

def pushforward (p : ProbDistribution X) (f : X → Y) : ProbDistribution Y :=
  Bridge.ofPMF ((Bridge.toPMF p).map f)

@[simp] theorem toPMF_pushforward (p : ProbDistribution X) (f : X → Y) :
    Bridge.toPMF (p.pushforward f) = (Bridge.toPMF p).map f := by
  simp [pushforward]

@[simp] theorem pushforward_id (p : ProbDistribution X) : p.pushforward id = p := by
  apply Bridge.toPMF_injective
  simp [PMF.map_id]

@[simp] theorem pushforward_comp (p : ProbDistribution X) (f : X → Y) (g : Y → Z) :
    (p.pushforward f).pushforward g = p.pushforward (g ∘ f) := by
  apply Bridge.toPMF_injective
  simp [PMF.map_comp]

theorem pushforward_apply (p : ProbDistribution X) (f : X → Y) (y : Y) :
    (p.pushforward f y : ℝ) =
      ∑ x ∈ Finset.univ.filter (fun x => f x = y), (p x : ℝ) := by
  classical
  change (((Bridge.toPMF p).map f) y).toReal = _
  rw [PMF.map_apply, tsum_fintype]
  rw [ENNReal.toReal_sum (fun x _ => by
    split_ifs
    · exact (Bridge.toPMF p).apply_ne_top x
    · exact ENNReal.zero_ne_top)]
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : f x = y
  · rw [ite_eq_left h, ite_eq_left h.symm, Bridge.toPMF_toReal]
  · have h' : y ≠ f x := Ne.symm h
    rw [ite_eq_right h, ite_eq_right h', ENNReal.toReal_zero]

end ProbDistribution
