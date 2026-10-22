module
public import Mathlib

public section

/-! Semantic home: ForMathlib.Combinatorics.DirectedPaths.Basic. Source spans: ReflectionSchedules:14.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.SchedulePaths
universe u v w
variable {V : Type u} {E : Type v} {R : Type w}
noncomputable section
@[expose] local instance _root_.OAI.KLInvariance.SchedulePaths.instDecidable_oAI (p : Prop) : Decidable p := Classical.propDecidable p
variable (source target : E → V)

@[expose] def IsPath (x y : V) : List E → Prop
  | [] => x = y
  | e :: p => source e = x ∧ IsPath (target e) y p

variable [Semiring R]
@[expose] def pathTerm (T : R) (v : V → R) : List E → V → R
  | [], x => v x
  | e :: p, x => if source e = x then T * pathTerm T v p (target e) else 0

/-- One elementary matrix `1+T E_xy`, acting without choosing an enumeration
of the finite vertex set. -/
@[expose] def step (T : R) (e : E) (v : V → R) : V → R :=
  fun x => v x + if source e = x then T * v (target e) else 0

/-- Edges are listed in decreasing schedule order, so the chronologically
last transfer is the outermost one. -/
@[expose] def dispatch (T : R) (v : V → R) : List E → V → R
  | [] => v
  | e :: p => step source target T e (dispatch T v p)

/-- The full matrix expansion, each sublist contributing exactly one path
term. Noncomposable sublists contribute zero by the definition of pathTerm. -/
theorem dispatch_eq_path_sum (T : R) (v : V → R) (p : List E) (x : V) :
    dispatch source target T v p x =
      ((p.sublists').map (fun q => pathTerm source target T v q x)).sum := by
  classical
  induction p generalizing x with
  | nil => simp [dispatch, List.sublists', pathTerm]
  | cons e p ih =>
    rw [dispatch,step,List.sublists'_cons,List.map_append,List.sum_append,List.map_map]
    rw [ih x]
    congr 1
    by_cases he : source e = x
    · simp only [Function.comp_def,pathTerm,he,ite_true]
      rw [List.sum_map_mul_left,ih (target e)]
    · simp [Function.comp_def,he,pathTerm]

/-- With a delta initial value, a path contributes its length weight, not an
invariant defined by the desired conclusion. -/
theorem pathTerm_delta (T : R) (x y : V) (p : List E) :
    pathTerm source target T (fun z => if z = y then 1 else 0) p x =
      if IsPath source target x y p then T ^ p.length else 0 := by
  classical
  induction p generalizing x with
  | nil => simp [pathTerm,IsPath]
  | cons e p ih =>
    simp only [pathTerm,IsPath,List.length_cons]
    by_cases he : source e = x
    · rw [ite_eq_left he,ih]
      by_cases hp : IsPath source target (target e) y p
      · simp only [hp,he,and_self,ite_true,pow_succ']
      · simp [hp,he]
    · simp [he]

/-- The entry of the elementary-matrix product is exactly the sum of weights
of directed schedule-subpaths. -/
theorem entry_eq_weighted_paths (T : R) (p : List E) (x y : V) :
    dispatch source target T (fun z => if z = y then 1 else 0) p x =
      ((p.sublists').map (fun q =>
        if IsPath source target x y q then T ^ q.length else 0)).sum := by
  classical
  rw [dispatch_eq_path_sum]
  congr 1
  exact List.map_congr_left (fun q _ => pathTerm_delta source target T x y q)


section LabelOrder
variable {Λ : Type*} [LinearOrder Λ] (label : E → Λ)

/-- Ties in a legitimate reflection schedule cannot occur on a composable
pair. Hence every nonzero term in the schedule expansion has strictly
rather than merely weakly decreasing labels. -/
theorem decreasing_of_schedule_path
    (hties : ∀ e f, label e = label f → target e ≠ source f)
    {p : List E} {x y : V}
    (hp : IsPath source target x y p)
    (hs : p.Pairwise (fun e f => label f ≤ label e)) :
    p.Pairwise (fun e f => label f < label e) := by
  induction p generalizing x with
  | nil => exact List.Pairwise.nil
  | cons e p ih =>
    cases p with
    | nil => simp
    | cons f p =>
      have ht : IsPath source target (target e) y (f :: p) := hp.2
      have hef : label f < label e := by
        apply lt_of_le_of_ne ((List.pairwise_cons.mp hs).1 f (List.mem_cons_self))
        intro heq
        exact hties e f heq.symm ht.1.symm
      apply List.pairwise_cons.mpr
      refine ⟨?_,ih ht hs.tail⟩
      intro g hg
      rcases List.mem_cons.mp hg with rfl | hg
      · exact hef
      · exact lt_of_le_of_lt ((List.pairwise_cons.mp hs.tail).1 g hg) hef

/-- Every strictly decreasing edge list contained in a weakly decreasing
schedule occurs as a sublist. This also handles arbitrary ordering of ties:
a strict list can use at most one edge of each label. -/
theorem sublist_of_decreasing_subset {p schedule : List E}
    (hp : p.Pairwise (fun e f => label f < label e))
    (hs : schedule.Pairwise (fun e f => label f ≤ label e))
    (hmem : p ⊆ schedule) : List.Sublist p schedule := by
  induction schedule generalizing p with
  | nil =>
    have : p = [] := List.eq_nil_iff_forall_not_mem.mpr
      (fun a ha => List.not_mem_nil (hmem ha))
    subst p
    exact List.Sublist.refl []
  | cons e schedule ih =>
    cases p with
    | nil => exact List.nil_sublist _
    | cons f p =>
      by_cases hef : e = f
      · subst f
        apply List.Sublist.cons_cons
        apply ih hp.tail hs.tail
        intro g hg
        rcases List.mem_cons.mp (hmem (List.mem_cons_of_mem e hg)) with heq | hin
        · have hlt := (List.pairwise_cons.mp hp).1 g hg
          rw [heq] at hlt
          exact (lt_irrefl _ hlt).elim
        · exact hin
      · apply List.Sublist.cons
        apply ih hp hs.tail
        intro g hg
        have hfg : f ∈ schedule := (List.mem_cons.mp (hmem (List.mem_cons_self))).resolve_left
          (Ne.symm hef)
        have hfe : label f ≤ label e := (List.pairwise_cons.mp hs).1 f hfg
        rcases List.mem_cons.mp (hmem hg) with heq | hin
        · subst g
          rcases List.mem_cons.mp hg with h | h
          · exact (hef h).elim
          · exact (not_lt_of_ge hfe ((List.pairwise_cons.mp hp).1 e h)).elim
        · exact hin

end LabelOrder

end
end KLInvariance.SchedulePaths
end

end OAI
