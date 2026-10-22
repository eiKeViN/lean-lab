module
public import Mathlib
public import ForMathlib.Combinatorics.DirectedPaths.Basic

public section

/-! Semantic home: ForMathlib.Combinatorics.DirectedPaths.Subpaths. Source spans: DyerPaths:17, DyerPaths:19, DyerPaths:20.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.SchedulePaths
variable {V E V' E' : Type*} (source target : E → V) (source' target' : E' → V')

/-- Relabelling graph vertices and edges preserves the actual path predicate. -/
theorem IsPath.map {x y : V} {p : List E}
    (hp : IsPath source target x y p) (f : V → V') (g : E → E')
    (hs : ∀ e, source' (g e) = f (source e))
    (ht : ∀ e, target' (g e) = f (target e)) :
    IsPath source' target' (f x) (f y) (p.map g) := by
  induction p generalizing x with
  | nil => exact congrArg f hp
  | cons e p ih =>
    exact ⟨(hs e).trans (congrArg f hp.1), ht e ▸ ih hp.2⟩

/-- Every adjacent pair in a genuine path is composable. -/
theorem IsPath.isChain {x y : V} {p : List E} (hp : IsPath source target x y p) :
    p.IsChain (fun e f => target e = source f) := by
  induction p generalizing x with
  | nil => exact .nil
  | cons e p ih =>
    cases p with
    | nil => exact .singleton e
    | cons f p =>
      apply List.isChain_cons_cons.mpr
      exact ⟨hp.2.1.symm, ih hp.2⟩

/-- A path's adjacent comparisons suffice for a transitive label order. The
statement allows the comparison to change under an edge map, provided the
local relation is checked only on composable edges. -/
theorem IsPath.pairwise_map_of_local {Λ Λ' : Type*} [LinearOrder Λ] [LinearOrder Λ']
    {x y : V} {p : List E} (hp : IsPath source target x y p)
    (label : E → Λ) (label' : E' → Λ') (g : E → E')
    (hlocal : ∀ e f, target e = source f →
      label e < label f → label' (g e) < label' (g f))
    (horder : p.Pairwise (fun e f => label e < label f)) :
    (p.map g).Pairwise (fun e f => label' e < label' f) := by
  rw [← List.isChain_iff_pairwise] at horder ⊢
  rw [List.isChain_map]
  induction p generalizing x with
  | nil => exact .nil
  | cons e p ih =>
    cases p with
    | nil => exact .singleton e
    | cons f p =>
      rw [List.isChain_cons_cons] at horder ⊢
      exact ⟨hlocal e f hp.2.1.symm horder.1, ih hp.2 horder.2⟩

end KLInvariance.SchedulePaths
end


section
namespace KLInvariance.SchedulePaths
open scoped BigOperators
variable {V E R : Type*} (source target : E → V)
noncomputable section
@[expose] local instance _root_.OAI.KLInvariance.SchedulePaths.instDecidable_oAI_1 (p : Prop) : Decidable p := Classical.propDecidable p

/-- The finite set of genuine directed paths selected by an edge schedule. -/
@[expose] def subpaths (schedule : List E) (x y : V) : Finset (List E) :=
  schedule.sublists'.toFinset.filter (IsPath source target x y)

@[simp] theorem mem_subpaths (schedule : List E) (x y : V) (p : List E) :
    p ∈ subpaths source target schedule x y ↔
      p.Sublist schedule ∧ IsPath source target x y p := by
  simp [subpaths, List.mem_sublists']

variable [Semiring R]

theorem dispatch_eq_subpaths_sum (T : R) (schedule : List E) (hnd : schedule.Nodup)
    (x y : V) :
    dispatch source target T (fun z => if z=y then 1 else 0) schedule x =
      ∑ p ∈ subpaths source target schedule x y, T ^ p.length := by
  rw [entry_eq_weighted_paths, subpaths, Finset.sum_filter,
    List.sum_toFinset _ (List.nodup_sublists'.mpr hnd)]

/-- A length-preserving involution on the actual schedule-path sets proves
an operator-entry relation, with no Hecke polynomial used in the assumptions. -/
theorem dispatch_eq_of_path_involution (T : R) (schedule schedule' : List E)
    (hnd : schedule.Nodup) (hnd' : schedule'.Nodup) (x y : V) (g : E → E)
    (hg : Function.Involutive g)
    (hforward : ∀ p ∈ subpaths source target schedule x y,
      p.map g ∈ subpaths source target schedule' x y)
    (hbackward : ∀ p ∈ subpaths source target schedule' x y,
      p.map g ∈ subpaths source target schedule x y) :
    dispatch source target T (fun z => if z=y then 1 else 0) schedule x =
      dispatch source target T (fun z => if z=y then 1 else 0) schedule' x := by
  rw [dispatch_eq_subpaths_sum source target T schedule hnd,
    dispatch_eq_subpaths_sum source target T schedule' hnd']
  exact Finset.sum_nbij' (List.map g) (List.map g) hforward hbackward
    (fun p _ => List.map_involutive_iff.mpr hg p)
    (fun p _ => List.map_involutive_iff.mpr hg p) (fun p _ => by simp)

end
end KLInvariance.SchedulePaths
end


section
namespace KLInvariance.SchedulePaths
variable {V E : Type*} (source target : E → V)
noncomputable section
@[expose] local instance _root_.OAI.KLInvariance.SchedulePaths.instDecidable_oAI_2 (p : Prop) : Decidable p := Classical.propDecidable p

/-- Sorted full schedules select precisely their strictly monotone paths;
an actual graph map satisfying the adjacent comparison test transports them. -/
theorem subpaths_map_of_sorted (label label' : E → ℝ)
    (schedule schedule' : List E) (x y : V)
    (hs : schedule.Pairwise (fun e f => label f ≤ label e))
    (hs' : schedule'.Pairwise (fun e f => label' f ≤ label' e))
    (hfull' : ∀ e, e ∈ schedule')
    (hties : ∀ e f, label e = label f → target e ≠ source f)
    (f : V → V) (g : E → E)
    (hsource : ∀ e, source (g e) = f (source e))
    (htarget : ∀ e, target (g e) = f (target e))
    (hx : f x=x) (hy : f y=y)
    (hlocal : ∀ e f, target e=source f → label f<label e → label' (g f)<label' (g e))
    (p : List E) (hp : p ∈ subpaths source target schedule x y) :
    p.map g ∈ subpaths source target schedule' x y := by
  obtain ⟨hsub,hp⟩ := (mem_subpaths source target schedule x y p).mp hp
  have hstrict := decreasing_of_schedule_path source target label hties hp (hs.sublist hsub)
  have horder := hp.pairwise_map_of_local source target
    (Λ := OrderDual ℝ) (Λ' := OrderDual ℝ)
    (fun e => (label e : OrderDual ℝ)) (fun e => (label' e : OrderDual ℝ)) g hlocal hstrict
  have hp' := hp.map source target source target f g hsource htarget
  rw [hx,hy] at hp'
  exact (mem_subpaths source target schedule' x y (p.map g)).mpr
    ⟨sublist_of_decreasing_subset label' horder hs' (fun _ _ => hfull' _), hp'⟩

end
end KLInvariance.SchedulePaths
end

end OAI
