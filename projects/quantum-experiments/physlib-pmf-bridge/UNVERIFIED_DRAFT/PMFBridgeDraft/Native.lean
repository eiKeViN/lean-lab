/-
UNVERIFIED_DRAFT — NOT COMPILED. Two explicit `sorry` obligations N01/N02.
Strong native baseline: real finite sums, shared bind helper, no explicit PMF import.
Imports the actual Physlib Channel, not its commented-out Channel.comp sketch.
-/
import QuantumInfo.ClassicalInfo.Channel

noncomputable section
open scoped BigOperators

namespace QuantumExperiments.PMFBridgeDraft.Native

variable {α β γ : Type*}

def bind [Fintype α] [Fintype β] (d : ProbDistribution α)
    (k : α → ProbDistribution β) : ProbDistribution β :=
  ProbDistribution.mk' (fun b => ∑ a, (d a : ℝ) * (k a b : ℝ))
    (fun _ => Finset.sum_nonneg fun _ _ =>
      mul_nonneg Prob.zero_le_coe Prob.zero_le_coe) (by
        -- INCOMPLETE N01. Swap the two finite sums; each k a sums to 1, then d.
        -- Exact finite-sum exchange helper signature is not in saved sources.
        sorry)

@[simp] theorem bind_apply [Fintype α] [Fintype β] (d : ProbDistribution α)
    (k : α → ProbDistribution β) (b : β) :
    (bind d k b : ℝ) = ∑ a, (d a : ℝ) * (k a b : ℝ) := rfl

theorem bind_assoc [Fintype α] [Fintype β] [Fintype γ]
    (d : ProbDistribution α) (k : α → ProbDistribution β)
    (l : β → ProbDistribution γ) :
    bind (bind d k) l = bind d (fun a => bind (k a) l) := by
  apply ProbDistribution.ext
  intro c
  apply Subtype.ext
  change (∑ b, (∑ a, (d a : ℝ) * (k a b : ℝ)) * (l b c : ℝ)) =
    ∑ a, (d a : ℝ) * (∑ b, (k a b : ℝ) * (l b c : ℝ))
  -- INCOMPLETE N02. Distribute multiplication, exchange finite sums, associate.
  -- This may be short with shared native lemmas; do not force a weak baseline.
  sorry

variable {I O P Q : Type*}

def comp [Fintype O] [Fintype P] (C : DMChannel I O) (D : DMChannel O P) :
    DMChannel I P :=
  ⟨fun i => bind (C.symb_dist i) D.symb_dist⟩

theorem comp_apply [Fintype O] [Fintype P] (C : DMChannel I O)
    (D : DMChannel O P) (i : I) (p : P) :
    ((comp C D).symb_dist i p : ℝ) =
      ∑ o, (C.symb_dist i o : ℝ) * (D.symb_dist o p : ℝ) := rfl

/-- Same association task as ViaPMF.comp_assoc; no Fintype I or measurability. -/
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

end QuantumExperiments.PMFBridgeDraft.Native
