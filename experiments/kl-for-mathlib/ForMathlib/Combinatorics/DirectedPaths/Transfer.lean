module
public import Mathlib
public import ForMathlib.Combinatorics.DirectedPaths.Subpaths

public section

/-! Semantic home: ForMathlib.Combinatorics.DirectedPaths.Transfer. Source spans: ReflectionOrders:1.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.SchedulePaths
open scoped BigOperators
universe u v w
variable {V : Type u} {E : Type v} {R : Type w}
noncomputable section
@[expose] local instance _root_.OAI.KLInvariance.SchedulePaths.instDecidable_oAI_3 (p : Prop) : Decidable p := Classical.propDecidable p
variable (source target : E → V) [Semiring R]

theorem dispatch_append (T : R) (v : V → R) (p q : List E) :
    dispatch source target T v (p ++ q) =
      dispatch source target T (dispatch source target T v q) p := by
  induction p with
  | nil => rfl
  | cons e p ih => simp only [List.cons_append,dispatch,ih]

theorem dispatch_add (T : R) (v w : V → R) (p : List E) :
    dispatch source target T (v+w) p =
      dispatch source target T v p + dispatch source target T w p := by
  induction p with
  | nil => rfl
  | cons e p ih =>
    simp only [dispatch,ih]
    funext x
    simp only [step,Pi.add_apply]
    split_ifs <;> simp [mul_add,add_assoc,add_left_comm,add_comm]

theorem dispatch_mul_right (T c : R) (v : V → R) (p : List E) :
    dispatch source target T (fun x => v x*c) p =
      fun x => dispatch source target T v p x*c := by
  induction p with
  | nil => rfl
  | cons e p ih =>
    simp only [dispatch,ih]
    funext x
    simp only [step]
    split_ifs <;> simp [add_mul,mul_assoc]

theorem dispatch_zero (T : R) (p : List E) : dispatch source target T (0 : V → R) p = 0 := by
  induction p with
  | nil => rfl
  | cons e p ih =>
    simp only [dispatch,ih]
    funext x
    simp [step]

theorem dispatch_sum {A : Type*} (T : R) (F : Finset A) (v : A → V → R) (p : List E) :
    dispatch source target T (∑ a ∈ F, v a) p =
      ∑ a ∈ F, dispatch source target T (v a) p := by
  induction F using Finset.induction_on with
  | empty => simp [dispatch_zero]
  | @insert a F ha ih => simp only [Finset.sum_insert ha,dispatch_add,ih]

theorem dispatch_eq_sum_entries [Fintype V] (T : R) (v : V → R) (p : List E) (x : V) :
    dispatch source target T v p x =
      ∑ y, dispatch source target T (fun z => if z=y then 1 else 0) p x * v y := by
  have hv : v = ∑ y, (fun z => (if z=y then 1 else 0)*v y) := by
    funext z
    simp [Finset.sum_apply]
  conv_lhs => rw [hv]
  rw [dispatch_sum]
  simp only [Finset.sum_apply,dispatch_mul_right]

theorem dispatch_eq_of_entries [Fintype V] (T : R) (p q : List E)
    (h : ∀ x y, dispatch source target T (fun z => if z=y then 1 else 0) p x =
      dispatch source target T (fun z => if z=y then 1 else 0) q x) (v : V → R) :
    dispatch source target T v p = dispatch source target T v q := by
  funext x
  rw [dispatch_eq_sum_entries source target T v p x,
    dispatch_eq_sum_entries source target T v q x]
  exact Finset.sum_congr rfl (fun y _ => congrArg (fun a => a*v y) (h x y))

/-- A finite lower region is closed under every target occurring in its
edge schedule, so values outside that region never enter its product. -/
theorem dispatch_congr_on (T : R) (S : Set V) (p : List E)
    (htarget : ∀ e ∈ p, target e ∈ S) (v w : V → R)
    (hvw : ∀ x ∈ S, v x=w x) :
    ∀ x ∈ S, dispatch source target T v p x = dispatch source target T w p x := by
  induction p with
  | nil => exact hvw
  | cons e p ih =>
    have htail := ih (fun f hf => htarget f (List.mem_cons_of_mem _ hf))
    intro x hx
    simp only [dispatch,step,htail x hx,htail (target e) (htarget e List.mem_cons_self)]

theorem dispatch_eq_finite_entries (T : R) (F : Finset V) (p : List E)
    (htarget : ∀ e ∈ p, target e ∈ F) (v : V → R) (x : V) (hx : x ∈ F) :
    dispatch source target T v p x =
      ∑ y ∈ F, dispatch source target T (fun z => if z=y then 1 else 0) p x * v y := by
  let w : V → R := ∑ y ∈ F, (fun z => (if z=y then 1 else 0)*v y)
  have hvw : ∀ z ∈ (F : Set V), v z=w z := by
    intro z hz
    simp [w,Finset.sum_apply,show z ∈ F from hz]
  rw [dispatch_congr_on source target T (F : Set V) p htarget v w hvw x hx]
  dsimp only [w]
  rw [dispatch_sum]
  simp only [Finset.sum_apply,dispatch_mul_right]

theorem dispatch_eq_of_entries_on (T : R) (F : Finset V) (p q : List E)
    (hp : ∀ e ∈ p, target e ∈ F) (hq : ∀ e ∈ q, target e ∈ F)
    (h : ∀ x ∈ F, ∀ y ∈ F,
      dispatch source target T (fun z => if z=y then 1 else 0) p x =
      dispatch source target T (fun z => if z=y then 1 else 0) q x)
    (v : V → R) (x : V) (hx : x ∈ F) :
    dispatch source target T v p x = dispatch source target T v q x := by
  rw [dispatch_eq_finite_entries source target T F p hp v x hx,
    dispatch_eq_finite_entries source target T F q hq v x hx]
  exact Finset.sum_congr rfl (fun y hy => congrArg (fun a => a*v y) (h x hx y hy))

variable {Λ : Type*} [LinearOrder Λ]

/-- A genuine path in a sorted schedule is determined by its edge set and
strict label order. Arbitrary permutations of repeated reflection labels
therefore have no effect. -/
theorem subpaths_eq_of_sorted (label : E → Λ)
    (hties : ∀ e f, label e = label f → target e ≠ source f)
    (p q : List E)
    (hp : p.Pairwise (fun e f => label f ≤ label e))
    (hq : q.Pairwise (fun e f => label f ≤ label e))
    (hmem : ∀ e, e ∈ p ↔ e ∈ q) (x y : V) :
    subpaths source target p x y = subpaths source target q x y := by
  ext s
  simp only [mem_subpaths]
  constructor
  · rintro ⟨hs,hpath⟩
    refine ⟨?_,hpath⟩
    apply sublist_of_decreasing_subset label
      (decreasing_of_schedule_path source target label hties hpath (hp.sublist hs)) hq
    exact fun e he => (hmem e).mp (hs.subset he)
  · rintro ⟨hs,hpath⟩
    refine ⟨?_,hpath⟩
    apply sublist_of_decreasing_subset label
      (decreasing_of_schedule_path source target label hties hpath (hq.sublist hs)) hp
    exact fun e he => (hmem e).mpr (hs.subset he)

theorem dispatch_eq_of_sorted [Fintype V] (T : R) (label : E → Λ)
    (hties : ∀ e f, label e = label f → target e ≠ source f)
    (p q : List E) (hpnd : p.Nodup) (hqnd : q.Nodup)
    (hp : p.Pairwise (fun e f => label f ≤ label e))
    (hq : q.Pairwise (fun e f => label f ≤ label e))
    (hmem : ∀ e, e ∈ p ↔ e ∈ q) (v : V → R) :
    dispatch source target T v p = dispatch source target T v q := by
  apply dispatch_eq_of_entries
  intro x y
  rw [dispatch_eq_subpaths_sum source target T p hpnd,
    dispatch_eq_subpaths_sum source target T q hqnd,
    subpaths_eq_of_sorted source target label hties p q hp hq hmem x y]

/-- Replacing each block by an equal actual operator replaces the product. -/
theorem dispatch_flatMap_eq {A : Type*} (T : R) (blocks : List A) (p q : A → List E)
    (h : ∀ a ∈ blocks, ∀ v, dispatch source target T v (p a) =
      dispatch source target T v (q a)) (v : V → R) :
    dispatch source target T v (blocks.flatMap p) =
      dispatch source target T v (blocks.flatMap q) := by
  induction blocks with
  | nil => rfl
  | cons a l ih =>
    simp only [List.flatMap_cons,dispatch_append]
    rw [ih (fun b hb => h b (List.mem_cons_of_mem _ hb)),h a List.mem_cons_self]


variable {V' E' : Type*} (source' target' : E' → V')

theorem IsPath.map_iff (j : V' → V) (hj : Function.Injective j) (J : E' → E)
    (hs : ∀ e, source (J e)=j (source' e))
    (ht : ∀ e, target (J e)=j (target' e)) {x y : V'} {p : List E'} :
    IsPath source target (j x) (j y) (p.map J) ↔ IsPath source' target' x y p := by
  induction p generalizing x with
  | nil => exact hj.eq_iff
  | cons e p ih =>
    change (source (J e)=j x ∧ IsPath source target (target (J e)) (j y) (p.map J)) ↔ _
    rw [hs,ht,ih,hj.eq_iff]
    rfl

theorem exists_list_lift (J : E' → E) (p : List E)
    (h : ∀ e ∈ p, ∃ e', J e'=e) : ∃ p' : List E', p'.map J=p := by
  induction p with
  | nil => exact ⟨[],rfl⟩
  | cons e p ih =>
    obtain ⟨e',he⟩ := h e List.mem_cons_self
    obtain ⟨p',hp⟩ := ih (fun f hf => h f (List.mem_cons_of_mem _ hf))
    exact ⟨e'::p',by simp [he,hp]⟩

/-- If all actual paths between the specified endpoints lie in a full embedded
subgraph, its full sorted product computes the same entry. -/
theorem dispatch_entry_graph_embedding (T : R) (label : E → Λ)
    (hties : ∀ e f, label e=label f → target e ≠ source f)
    (j : V' → V) (hj : Function.Injective j) (J : E' → E) (hJ : Function.Injective J)
    (hs : ∀ e, source (J e)=j (source' e))
    (ht : ∀ e, target (J e)=j (target' e))
    (p : List E) (q : List E') (hpnd : p.Nodup) (hqnd : q.Nodup)
    (hp : p.Pairwise (fun e f => label f ≤ label e))
    (hq : q.Pairwise (fun e f => label (J f) ≤ label (J e)))
    (hqfull : ∀ e, e ∈ q) (hJmem : ∀ e, J e ∈ p)
    (x y : V')
    (hpath : ∀ r ∈ subpaths source target p (j x) (j y), ∀ e ∈ r, ∃ e', J e'=e) :
    dispatch source target T (fun z => if z=j y then 1 else 0) p (j x) =
      dispatch source' target' T (fun z => if z=y then 1 else 0) q x := by
  rw [dispatch_eq_subpaths_sum source target T p hpnd,
    dispatch_eq_subpaths_sum source' target' T q hqnd]
  symm
  have hties' : ∀ e f, label (J e)=label (J f) → target' e ≠ source' f := by
    intro e f he hf
    apply hties (J e) (J f) he
    rw [ht,hs,hf]
  apply Finset.sum_bij (fun r _ => r.map J)
  · intro r hr
    obtain ⟨hr,hpr⟩ := (mem_subpaths source' target' q x y r).mp hr
    apply (mem_subpaths source target p (j x) (j y) (r.map J)).mpr
    constructor
    · apply sublist_of_decreasing_subset label
      · rw [List.pairwise_map]
        exact decreasing_of_schedule_path source' target' (label ∘ J) hties' hpr (hq.sublist hr)
      · exact hp
      · intro e he
        obtain ⟨f,_,rfl⟩ := List.mem_map.mp he
        exact hJmem f
    · exact hpr.map source' target' source target j J hs ht
  · intro r _ s _ he
    exact List.map_injective_iff.mpr hJ he
  · intro r hr
    obtain ⟨s,he⟩ := exists_list_lift J r (hpath r hr)
    refine ⟨s,?_,he⟩
    obtain ⟨hrsub,hrpath⟩ := (mem_subpaths source target p (j x) (j y) r).mp hr
    have hspath : IsPath source' target' x y s :=
      (IsPath.map_iff source target source' target' j hj J hs ht).mp (he ▸ hrpath)
    apply (mem_subpaths source' target' q x y s).mpr
    refine ⟨?_,hspath⟩
    apply sublist_of_decreasing_subset (label ∘ J)
    · have hstrict := decreasing_of_schedule_path source target label hties hrpath (hp.sublist hrsub)
      rw [← he,List.pairwise_map] at hstrict
      exact hstrict
    · exact hq
    · exact fun e _ => hqfull e
  · intro r _
    simp

end
end KLInvariance.SchedulePaths
end

end OAI
