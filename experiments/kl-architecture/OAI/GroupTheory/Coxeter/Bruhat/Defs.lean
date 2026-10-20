import Mathlib

/-! Semantic home: OAI.GroupTheory.Coxeter.Bruhat.Defs. Source spans: Model:1.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

namespace KLInvariance
open Polynomial
universe u v u' v'
variable {B : Type u} {W : Type v} [Group W] {M : CoxeterMatrix B}
def BruhatStep (cs : CoxeterSystem M W) (x y : W) : Prop :=
  cs.length x < cs.length y ∧ ∃ t : W, cs.IsReflection t ∧ y = t * x

/-- The actual strong Bruhat order, not the weak order. -/
def BruhatLE (cs : CoxeterSystem M W) : W → W → Prop :=
  Relation.ReflTransGen (BruhatStep cs)

/-- The unlabelled interval, including both endpoints. -/
def Interval (cs : CoxeterSystem M W) (u b : W) :=
  {x : W // BruhatLE cs u x ∧ BruhatLE cs x b}

instance intervalOrder (cs : CoxeterSystem M W) (u b : W) :
    PartialOrder (Interval cs u b) where
  le left right := BruhatLE cs left.val right.val
  le_refl _ := Relation.ReflTransGen.refl
  le_trans _ _ _ forward backward := forward.trans backward
  le_antisymm left right forward backward := by
    apply Subtype.ext
    have length_mono : ∀ {lower upper : W}, BruhatLE cs lower upper →
        cs.length lower ≤ cs.length upper := by
      intro lower upper relation
      induction relation using Relation.ReflTransGen.head_induction_on with
      | refl => exact le_rfl
      | head step _ rest => exact le_trans step.1.le rest
    by_contra distinct
    rcases forward.cases_head with same | ⟨middle, step, rest⟩
    · exact distinct same
    · exact (not_lt_of_ge (length_mono backward))
        (lt_of_lt_of_le step.1 (length_mono rest))

/-- `d(x,y)` in the manuscript, used only for comparable endpoints. -/
noncomputable def rankDifference (cs : CoxeterSystem M W) (x y : W) : ℕ :=
  cs.length y - cs.length x

end KLInvariance

end OAI
