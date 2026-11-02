/-
UNVERIFIED_DRAFT — NOT COMPILED. No additional placeholders in this file,
but depends on Bridge's THREE explicit incomplete obligations. No acceptance claim.
Uses actual PMF.bind/bind_bind, with a real finite-sum observation for clients.
-/
import QuantumInfo.ClassicalInfo.Channel
import PMFBridgeDraft.Bridge

noncomputable section
open scoped BigOperators

namespace QuantumExperiments.PMFBridgeDraft.ViaPMF

variable {α β γ : Type*}

def bind [Fintype α] [Fintype β] (d : ProbDistribution α)
    (k : α → ProbDistribution β) : ProbDistribution β :=
  Bridge.ofPMF ((Bridge.toPMF d).bind (fun a => Bridge.toPMF (k a)))

@[simp] theorem toPMF_bind [Fintype α] [Fintype β] (d : ProbDistribution α)
    (k : α → ProbDistribution β) :
    Bridge.toPMF (bind d k) = (Bridge.toPMF d).bind (fun a => Bridge.toPMF (k a)) := by
  exact Bridge.toPMF_ofPMF _

theorem bind_apply [Fintype α] [Fintype β] (d : ProbDistribution α)
    (k : α → ProbDistribution β) (b : β) :
    (bind d k b : ℝ) = ∑ a, (d a : ℝ) * (k a b : ℝ) := by
  simp only [bind, Bridge.ofPMF_apply, Bridge.pmf_bind_toReal, Bridge.toPMF_toReal]

theorem bind_assoc [Fintype α] [Fintype β] [Fintype γ]
    (d : ProbDistribution α) (k : α → ProbDistribution β)
    (l : β → ProbDistribution γ) :
    bind (bind d k) l = bind d (fun a => bind (k a) l) := by
  apply Bridge.toPMF_injective
  simpa only [toPMF_bind] using
    PMF.bind_bind (Bridge.toPMF d) (fun a => Bridge.toPMF (k a))
      (fun b => Bridge.toPMF (l b))

variable {I O P Q : Type*}

def comp [Fintype O] [Fintype P] (C : DMChannel I O) (D : DMChannel O P) :
    DMChannel I P :=
  ⟨fun i => bind (C.symb_dist i) D.symb_dist⟩

theorem comp_apply [Fintype O] [Fintype P] (C : DMChannel I O)
    (D : DMChannel O P) (i : I) (p : P) :
    ((comp C D).symb_dist i p : ℝ) =
      ∑ o, (C.symb_dist i o : ℝ) * (D.symb_dist o p : ℝ) := by
  exact bind_apply (C.symb_dist i) D.symb_dist p

/-- Same association task as Native.comp_assoc; no stronger caller assumptions. -/
theorem comp_assoc [Fintype O] [Fintype P] [Fintype Q]
    (C : DMChannel I O) (D : DMChannel O P) (E : DMChannel P Q) :
    comp (comp C D) E = comp C (comp D E) := by
  cases C with
  | mk c =>
    cases D with
    | mk d =>
      cases E with
      | mk e =>
        change DMChannel.mk (fun i => bind (bind (c i) d) e) =
          DMChannel.mk (fun i => bind (c i) (fun o => bind (d o) e))
        congr 1
        funext i
        exact bind_assoc (c i) d e

end QuantumExperiments.PMFBridgeDraft.ViaPMF
