module
public import Mathlib
public import ForMathlib.Combinatorics.DirectedPaths.Transfer

public section

/-! Semantic home: ForMathlib.Combinatorics.DirectedPaths.SortedSchedule. Source spans: ReflectionOrders:4.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.SchedulePaths
universe u v w
variable {E : Type u} {A : Type v} {Λ : Type w} [LinearOrder A] [LinearOrder Λ]
noncomputable section
@[expose] local instance _root_.OAI.KLInvariance.SchedulePaths.instDecidable_oAI_4 (p : Prop) : Decidable p := Classical.propDecidable p
@[expose] local instance _root_.OAI.KLInvariance.SchedulePaths.instDecidableEq_oAI : DecidableEq E := Classical.decEq E

@[expose] def sortedSchedule (F : Finset E) (score : E → Λ) : List E :=
  F.toList.mergeSort (fun e f => score f ≤ score e)

@[simp] theorem mem_sortedSchedule (F : Finset E) (score : E → Λ) (e : E) :
    e ∈ sortedSchedule F score ↔ e ∈ F := by simp [sortedSchedule]

theorem sortedSchedule_nodup (F : Finset E) (score : E → Λ) :
    (sortedSchedule F score).Nodup :=
  (List.mergeSort_perm _ _).nodup_iff.mpr (Finset.nodup_toList _)

theorem sortedSchedule_pairwise (F : Finset E) (score : E → Λ) :
    (sortedSchedule F score).Pairwise (fun e f => score f ≤ score e) :=
  List.pairwise_mergeSort' _ _

@[expose] def blockValues (F : Finset E) (primary : E → A) : List A :=
  (F.image primary).sort (fun a b => b ≤ a)

@[expose] def scheduleBlock (F : Finset E) (primary : E → A) (score : E → Λ) (a : A) : List E :=
  sortedSchedule (F.filter (fun e => primary e=a)) score

@[expose] def groupedSchedule (F : Finset E) (primary : E → A) (score : E → Λ) : List E :=
  (blockValues F primary).flatMap (scheduleBlock F primary score)

@[simp] theorem mem_blockValues (F : Finset E) (primary : E → A) (a : A) :
    a ∈ blockValues F primary ↔ ∃ e ∈ F, primary e=a := by
  simp [blockValues]

omit [LinearOrder A] in
@[simp] theorem mem_scheduleBlock (F : Finset E) (primary : E → A) (score : E → Λ)
    (a : A) (e : E) : e ∈ scheduleBlock F primary score a ↔ e ∈ F ∧ primary e=a := by
  simp [scheduleBlock]

@[simp] theorem mem_groupedSchedule (F : Finset E) (primary : E → A) (score : E → Λ)
    (e : E) : e ∈ groupedSchedule F primary score ↔ e ∈ F := by
  constructor
  · intro he
    obtain ⟨a,_,ha⟩ := List.mem_flatMap.mp he
    exact ((mem_scheduleBlock F primary score a e).mp ha).1
  · intro he
    apply List.mem_flatMap.mpr
    exact ⟨primary e,(mem_blockValues F primary _).mpr ⟨e,he,rfl⟩,
      (mem_scheduleBlock F primary score _ _).mpr ⟨he,rfl⟩⟩

theorem blockValues_strict (F : Finset E) (primary : E → A) :
    (blockValues F primary).Pairwise (fun a b => b < a) := by
  have hs := Finset.pairwise_sort (F.image primary) (fun a b => b ≤ a)
  have hn := Finset.sort_nodup (F.image primary) (fun a b => b ≤ a)
  exact (List.pairwise_and_iff.mpr ⟨hs,hn⟩).imp (fun h => lt_of_le_of_ne h.1 h.2.symm)

theorem groupedSchedule_nodup (F : Finset E) (primary : E → A) (score : E → Λ) :
    (groupedSchedule F primary score).Nodup := by
  apply List.nodup_flatMap.mpr
  constructor
  · intro a _
    exact sortedSchedule_nodup _ _
  · apply (blockValues_strict F primary).imp
    intro a b hab
    apply List.disjoint_left.mpr
    intro e hea heb
    have ha := ((mem_scheduleBlock F primary score a e).mp hea).2
    have hb := ((mem_scheduleBlock F primary score b e).mp heb).2
    exact hab.ne (hb.symm.trans ha)

theorem groupedSchedule_pairwise (F : Finset E) (primary : E → A) (score : E → Λ)
    (h : ∀ e ∈ F, ∀ f ∈ F, primary f < primary e → score f ≤ score e) :
    (groupedSchedule F primary score).Pairwise (fun e f => score f ≤ score e) := by
  apply List.pairwise_flatMap.mpr
  constructor
  · intro a _
    exact sortedSchedule_pairwise _ _
  · apply (blockValues_strict F primary).imp
    intro a b hab e he f hf
    obtain ⟨he,heq⟩ := (mem_scheduleBlock F primary score a e).mp he
    obtain ⟨hf,hfq⟩ := (mem_scheduleBlock F primary score b f).mp hf
    exact h e he f hf (by simpa only [heq,hfq] using hab)

variable {V : Type*} {R : Type*} [Semiring R] (source target : E → V)

theorem dispatch_entries_eq_of_sorted (T : R) (label : E → Λ)
    (hties : ∀ e f, label e=label f → target e ≠ source f)
    (p q : List E) (hpnd : p.Nodup) (hqnd : q.Nodup)
    (hp : p.Pairwise (fun e f => label f ≤ label e))
    (hq : q.Pairwise (fun e f => label f ≤ label e))
    (hmem : ∀ e, e ∈ p ↔ e ∈ q) (x y : V) :
    dispatch source target T (fun z => if z=y then 1 else 0) p x =
      dispatch source target T (fun z => if z=y then 1 else 0) q x := by
  rw [dispatch_eq_subpaths_sum source target T p hpnd,
    dispatch_eq_subpaths_sum source target T q hqnd,
    subpaths_eq_of_sorted source target label hties p q hp hq hmem x y]

omit [LinearOrder A] in
/-- Replacement on a finite lower region requires no artificial finiteness
assumption on the ambient Coxeter group. -/
theorem dispatch_flatMap_eq_on (T : R) (S : Set V) (blocks : List A) (p q : A → List E)
    (htarget : ∀ a ∈ blocks, ∀ e ∈ p a, target e ∈ S)
    (h : ∀ a ∈ blocks, ∀ v, ∀ x ∈ S,
      dispatch source target T v (p a) x = dispatch source target T v (q a) x)
    (v : V → R) : ∀ x ∈ S,
    dispatch source target T v (blocks.flatMap p) x =
      dispatch source target T v (blocks.flatMap q) x := by
  induction blocks with
  | nil => exact fun _ _ => rfl
  | cons a l ih =>
    intro x hx
    simp only [List.flatMap_cons,dispatch_append]
    rw [dispatch_congr_on source target T S (p a) (htarget a List.mem_cons_self)
      _ _ (ih (fun b hb => htarget b (List.mem_cons_of_mem _ hb))
      (fun b hb => h b (List.mem_cons_of_mem _ hb))) x hx]
    exact h a List.mem_cons_self _ x hx

end
end KLInvariance.SchedulePaths
end

end OAI
