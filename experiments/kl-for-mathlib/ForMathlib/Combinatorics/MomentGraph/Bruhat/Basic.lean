module
public import Mathlib
public import ForMathlib.Combinatorics.MomentGraph.Sheaf.Basic
public import ForMathlib.GroupTheory.Coxeter.Bruhat.Basic

public section

/-! Semantic home: ForMathlib.Combinatorics.MomentGraph.Bruhat.Basic. Source spans: Tits:1.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance
namespace BruhatGraph
universe u v
variable {B : Type u} {W : Type v} [Group W] {M : CoxeterMatrix B}
  (cs : CoxeterSystem M W) (u b : W)

/-- Actual finite directed moment-graph edges, including the non-cover
reflection edges. No reconstruction from the abstract poset is assumed. -/
@[expose] def Edge := {p : Interval cs u b × Interval cs u b // BruhatStep cs p.1.val p.2.val}

@[expose] instance _root_.OAI.KLInvariance.BruhatGraph.instFiniteEdge : Finite (Edge cs u b) := by
  let := interval_finite cs u b
  unfold Edge
  infer_instance

@[expose] def source (e : Edge cs u b) : Interval cs u b := e.val.1
@[expose] def target (e : Edge cs u b) : Interval cs u b := e.val.2

@[expose] def graph : MomentGraph.OrderedGraph (Interval cs u b) (Edge cs u b) where
  source := source cs u b
  target := target cs u b
  increasing e := by
    refine ⟨Relation.ReflTransGen.single e.property, ?_⟩
    intro h
    exact (not_lt_of_ge (length_le_of_bruhat cs h)) e.property.1

/-- Genuine left reflection label; uniquely determined by the endpoints. -/
@[expose] def label (e : Edge cs u b) : W := (target cs u b e).val * (source cs u b e).val⁻¹

theorem label_isReflection (e : Edge cs u b) : cs.IsReflection (label cs u b e) := by
  obtain ⟨t, ht, htx⟩ := e.property.2
  simpa [label, source, target, htx, mul_assoc] using ht

@[simp] theorem label_mul_source (e : Edge cs u b) :
    label cs u b e * (source cs u b e).val = (target cs u b e).val := by
  simp [label, mul_assoc]

@[simp] theorem label_mul_target (e : Edge cs u b) :
    label cs u b e * (target cs u b e).val = (source cs u b e).val := by
  rw [← label_mul_source cs u b e, ← mul_assoc,
    (label_isReflection cs u b e).mul_self, one_mul]

theorem eq_of_label_source_eq {e f : Edge cs u b}
    (hl : label cs u b e = label cs u b f)
    (hs : source cs u b e = source cs u b f) : e = f := by
  have ht : target cs u b e = target cs u b f := by
    apply Subtype.ext
    rw [← label_mul_source cs u b e, ← label_mul_source cs u b f, hl, hs]
  apply Subtype.ext
  exact Prod.ext hs ht

theorem eq_of_label_target_eq {e f : Edge cs u b}
    (hl : label cs u b e = label cs u b f)
    (ht : target cs u b e = target cs u b f) : e = f := by
  have hs : source cs u b e = source cs u b f := by
    apply Subtype.ext
    rw [← label_mul_target cs u b e, ← label_mul_target cs u b f, hl, ht]
  exact eq_of_label_source_eq cs u b hl hs

theorem source_ne_target_of_label_eq {e f : Edge cs u b}
    (hl : label cs u b e = label cs u b f) :
    source cs u b e ≠ target cs u b f := by
  intro h
  have ht : target cs u b e = source cs u b f := by
    apply Subtype.ext
    rw [← label_mul_source cs u b e, hl, h, label_mul_target]
  have he := (graph cs u b).increasing e
  have hf := (graph cs u b).increasing f
  change source cs u b e < target cs u b e at he
  change source cs u b f < target cs u b f at hf
  rw [h, ht] at he
  exact lt_asymm he hf


theorem endpoints_disjoint_of_label_eq {e f : Edge cs u b} (hef : e ≠ f)
    (hl : label cs u b e = label cs u b f) :
    Disjoint ({source cs u b e, target cs u b e} : Set _)
      {source cs u b f, target cs u b f} := by
  rw [Set.disjoint_left]
  intro x hx hy
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
  rcases hx with rfl | rfl <;> rcases hy with hy | hy
  · exact hef (eq_of_label_source_eq cs u b hl hy)
  · exact source_ne_target_of_label_eq cs u b hl hy
  · exact source_ne_target_of_label_eq cs u b hl.symm hy.symm
  · exact hef (eq_of_label_target_eq cs u b hl hy)

end BruhatGraph
end KLInvariance
end

end OAI
