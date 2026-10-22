import Mathlib
import ForMathlib.GroupTheory.Coxeter.Bruhat.LowerFinset
import ForMathlib.GroupTheory.Coxeter.Roots.RatioOrder
import ForMathlib.RepresentationTheory.Hecke.Operators

/-! Semantic home: ForMathlib.RepresentationTheory.Hecke.DyerPaths.Adapted. Source spans: DyerPaths:22.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.AdaptedDyer
open TitsSpace SchedulePaths
open scoped BigOperators
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section
local instance _root_.OAI.KLInvariance.AdaptedDyer.instDecidable_oAI (p : Prop) : Decidable p := Classical.propDecidable p

abbrev Edge := {e : W × W // BruhatStep cs e.1 e.2}
def source (e : Edge cs) : W := e.val.1
def target (e : Edge cs) : W := e.val.2
def rootLabel (e : Edge cs) : PositiveRoot M cs := graphRoot e.property

@[simp] theorem rootRef_rootLabel (e : Edge cs) :
    rootRef (rootLabel cs e) = target cs e * (source cs e)⁻¹ := by
  exact congrArg Subtype.val ((positiveRootEquiv M cs).left_inv
    ⟨e.val.2 * e.val.1⁻¹,e.property.label_reflection⟩)

theorem target_eq_root (e : Edge cs) :
    target cs e = rootRef (rootLabel cs e) * source cs e := by
  rw [rootRef_rootLabel]
  group

theorem rootLabel_ne_of_join (e f : Edge cs) (h : target cs e = source cs f) :
    rootLabel cs e ≠ rootLabel cs f := by
  rcases e with ⟨⟨x,y⟩,he⟩
  rcases f with ⟨⟨z,w⟩,hf⟩
  change y=z at h
  subst z
  exact graphRoot_ne_of_path he hf

variable {cs}
def score (O : RatioOrder (M := M) (cs := cs)) (e : Edge cs) : ℝ :=
  O.slope (rootLabel cs e)

theorem score_ties (O : RatioOrder (M := M) (cs := cs)) (e f : Edge cs)
    (h : score O e = score O f) : target cs e ≠ source cs f :=
  fun hj => rootLabel_ne_of_join cs e f hj (O.slope_injective h)

variable (cs)
def edgeFinset (b : W) : Finset (Edge cs) :=
  let P := ((lowerFinset cs b).product (lowerFinset cs b)).filter
    (fun e => BruhatStep cs e.1 e.2)
  P.attach.image (fun e => (⟨e.val,by
    exact (Finset.mem_filter.mp e.property).2⟩ : Edge cs))

omit [Fintype I] in
@[simp] theorem mem_edgeFinset (b : W) (e : Edge cs) :
    e ∈ edgeFinset cs b ↔ BruhatLE cs (target cs e) b := by
  unfold edgeFinset
  constructor
  · intro h
    obtain ⟨p,_,he⟩ := Finset.mem_image.mp h
    subst e
    exact (mem_lowerFinset cs b p.val.2).mp
      (Finset.mem_product.mp (Finset.mem_filter.mp p.property).1).2
  · intro h
    apply Finset.mem_image.mpr
    have hx : BruhatLE cs (source cs e) b := (show BruhatLE cs (source cs e) (target cs e) from .single e.property).trans h
    refine ⟨⟨e.val,Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨(mem_lowerFinset cs b _).mpr hx,(mem_lowerFinset cs b _).mpr h⟩,e.property⟩⟩,
      Finset.mem_attach _ _,?_⟩
    rfl

variable {cs}
def schedule (O : RatioOrder (M := M) (cs := cs)) (b : W) : List (Edge cs) :=
  (edgeFinset cs b).toList.mergeSort (fun e f => score O e ≤ score O f)

@[simp] theorem mem_schedule (O : RatioOrder (M := M) (cs := cs)) (b : W) (e : Edge cs) :
    e ∈ schedule O b ↔ BruhatLE cs (target cs e) b := by
  simp [schedule]

theorem schedule_nodup (O : RatioOrder (M := M) (cs := cs)) (b : W) :
    (schedule O b).Nodup :=
  (List.mergeSort_perm _ _).nodup_iff.mpr (Finset.nodup_toList _)

theorem schedule_increasing (O : RatioOrder (M := M) (cs := cs)) (b : W) :
    (schedule O b).Pairwise (fun e f => score O e ≤ score O f) := by
  unfold schedule
  apply List.pairwise_mergeSort'

variable (cs)
omit [Fintype I] in
theorem path_le {x y : W} {p : List (Edge cs)}
    (hp : IsPath (source cs) (target cs) x y p) : BruhatLE cs x y := by
  induction p generalizing x with
  | nil => exact hp ▸ .refl
  | cons e p ih =>
    exact hp.1 ▸ (show BruhatLE cs (source cs e) (target cs e) from .single e.property).trans (ih hp.2)

omit [Fintype I] in
theorem path_targets_le {x y : W} {p : List (Edge cs)}
    (hp : IsPath (source cs) (target cs) x y p) :
    ∀ e ∈ p, BruhatLE cs (target cs e) y := by
  induction p generalizing x with
  | nil => simp
  | cons e p ih =>
    intro f hf
    rcases List.mem_cons.mp hf with rfl | hf
    · exact path_le cs hp.2
    · exact ih hp.2 f hf

variable {cs}
def paths (O : RatioOrder (M := M) (cs := cs)) (x y : W) : Finset (List (Edge cs)) :=
  subpaths (source cs) (target cs) (schedule O y) x y

@[simp] theorem mem_paths (O : RatioOrder (M := M) (cs := cs)) (x y : W) (p : List (Edge cs)) :
    p ∈ paths O x y ↔ IsPath (source cs) (target cs) x y p ∧
      p.Pairwise (fun e f => score O e < score O f) := by
  rw [paths,mem_subpaths]
  constructor
  · rintro ⟨hsub,hp⟩
    refine ⟨hp,?_⟩
    exact decreasing_of_schedule_path (source cs) (target cs)
      (Λ := OrderDual ℝ) (fun e => (score O e : OrderDual ℝ))
      (fun e f h => score_ties O e f h) hp ((schedule_increasing O y).sublist hsub)
  · rintro ⟨hp,hord⟩
    refine ⟨?_,hp⟩
    apply sublist_of_decreasing_subset (Λ := OrderDual ℝ)
      (fun e => (score O e : OrderDual ℝ)) hord (schedule_increasing O y)
    intro e he
    exact (mem_schedule O y e).mpr (path_targets_le cs hp e he)

def polynomial (O : RatioOrder (M := M) (cs := cs)) (x y : W) : Polynomial ℤ :=
  ∑ p ∈ paths O x y, Polynomial.X ^ p.length

theorem polynomial_dispatch (O : RatioOrder (M := M) (cs := cs)) (x y : W) :
    polynomial O x y = dispatch (source cs) (target cs) Polynomial.X
      (fun z => if z=y then 1 else 0) (schedule O y) x :=
  (dispatch_eq_subpaths_sum _ _ _ _ (schedule_nodup O y) x y).symm


variable (cs)
theorem rootRef_injective : Function.Injective (rootRef (M := M) (cs := cs)) := by
  intro a b h
  apply (positiveRootEquiv M cs).symm.injective
  exact Subtype.ext h

theorem rootLabel_simple_iff (i : I) (e : Edge cs) :
    rootLabel cs e = simplePositive i ↔ target cs e = cs.simple i * source cs e := by
  constructor
  · intro h
    rw [target_eq_root cs e,h,rootRef_simplePositive]
  · intro h
    apply rootRef_injective cs
    rw [rootRef_rootLabel,rootRef_simplePositive,h]
    group

/-- On a non-simple-labelled edge this is actual left multiplication by s.
Simple-labelled edges are fixed merely to make the extension a total involution;
all path uses below exclude them before applying this map. -/
def rotateEdge (i : I) (e : Edge cs) : Edge cs :=
  if h : target cs e = cs.simple i * source cs e then e else
    ⟨(cs.simple i * source cs e,cs.simple i * target cs e),
      bruhatStep_simple_mul cs e.property i h⟩

theorem rotateEdge_val (i : I) (e : Edge cs) (h : rootLabel cs e ≠ simplePositive i) :
    (rotateEdge cs i e).val = (cs.simple i * source cs e,cs.simple i * target cs e) := by
  rw [rotateEdge,dite_eq_right (fun hh => h ((rootLabel_simple_iff cs i e).mpr hh))]

theorem rotateEdge_root (i : I) (e : Edge cs) (h : rootLabel cs e ≠ simplePositive i) :
    rootLabel cs (rotateEdge cs i e) = positiveAction (cs.simple i) (rootLabel cs e) := by
  apply rootRef_injective cs
  rw [rootRef_rootLabel]
  change (rotateEdge cs i e).val.2 * (rotateEdge cs i e).val.1⁻¹ =
    rootRef (positiveAction (cs.simple i) (rootLabel cs e))
  have hc : rootRef (positiveAction (cs.simple i) (rootLabel cs e)) =
      cs.simple i * rootRef (rootLabel cs e) * (cs.simple i)⁻¹ :=
    rootReflection_positiveAction _ _
  rw [rotateEdge_val cs i e h,hc,rootRef_rootLabel]
  group

theorem rotateEdge_nonsimple (i : I) (e : Edge cs) (h : rootLabel cs e ≠ simplePositive i) :
    rootLabel cs (rotateEdge cs i e) ≠ simplePositive i := by
  rw [rotateEdge_root cs i e h]
  exact simple_positiveAction_ne i _ h

@[simp] theorem rotateEdge_involutive (i : I) : Function.Involutive (rotateEdge cs i) := by
  intro e
  by_cases h : rootLabel cs e = simplePositive i
  · have he : rotateEdge cs i e = e := by
      rw [rotateEdge,dite_eq_left ((rootLabel_simple_iff cs i e).mp h)]
    rw [he,he]
  · apply Subtype.ext
    rw [rotateEdge_val cs i _ (rotateEdge_nonsimple cs i e h)]
    change (cs.simple i * (rotateEdge cs i e).val.1,
      cs.simple i * (rotateEdge cs i e).val.2) = e.val
    rw [rotateEdge_val cs i e h]
    simp only [cs.simple_mul_simple_cancel_left]
    rfl

omit [Fintype I] in
theorem path_map_of_mem {E E' V V' : Type*} (src tgt : E → V) (src' tgt' : E' → V')
    {p : List E} {x y : V} (hp : IsPath src tgt x y p) (f : V → V') (g : E → E')
    (hs : ∀ e ∈ p, src' (g e) = f (src e)) (ht : ∀ e ∈ p, tgt' (g e) = f (tgt e)) :
    IsPath src' tgt' (f x) (f y) (p.map g) := by
  induction p generalizing x with
  | nil => exact congrArg f hp
  | cons e p ih =>
    refine ⟨(hs e List.mem_cons_self).trans (congrArg f hp.1),?_⟩
    rw [ht e List.mem_cons_self]
    exact ih hp.2 (fun a ha => hs a (List.mem_cons_of_mem e ha))
      (fun a ha => ht a (List.mem_cons_of_mem e ha))

theorem path_rotate {x y : W} {p : List (Edge cs)} (i : I)
    (hp : IsPath (source cs) (target cs) x y p)
    (hn : ∀ e ∈ p, rootLabel cs e ≠ simplePositive i) :
    IsPath (source cs) (target cs) (cs.simple i*x) (cs.simple i*y) (p.map (rotateEdge cs i)) := by
  apply path_map_of_mem (source cs) (target cs) (source cs) (target cs)
    hp (fun z => cs.simple i*z) (rotateEdge cs i)
  · intro e he
    exact congrArg Prod.fst (rotateEdge_val cs i e (hn e he))
  · intro e he
    exact congrArg Prod.snd (rotateEdge_val cs i e (hn e he))


@[simp] theorem rotateEdge_twice (i : I) (e : Edge cs) :
    rotateEdge cs i (rotateEdge cs i e) = e := rotateEdge_involutive cs i e

variable {cs}
def Nonsimple (i : I) (p : List (Edge cs)) : Prop :=
  ∀ e ∈ p, rootLabel cs e ≠ simplePositive i

@[simp] theorem nonsimple_map (i : I) {p : List (Edge cs)} (hn : Nonsimple i p) :
    Nonsimple i (p.map (rotateEdge cs i)) := by
  intro e he
  obtain ⟨f,hf,rfl⟩ := List.mem_map.mp he
  exact rotateEdge_nonsimple cs i f (hn f hf)

@[simp] theorem path_map_twice (i : I) (p : List (Edge cs)) :
    (p.map (rotateEdge cs i)).map (rotateEdge cs i) = p := by
  simp only [List.map_map,Function.comp_def,rotateEdge_twice]
  exact List.map_id p

theorem path_rotate_iff (i : I) {x y : W} {p : List (Edge cs)} (hn : Nonsimple i p) :
    IsPath (source cs) (target cs) (cs.simple i*x) (cs.simple i*y)
      (p.map (rotateEdge cs i)) ↔ IsPath (source cs) (target cs) x y p := by
  constructor
  · intro hp
    simpa only [cs.simple_mul_simple_cancel_left,path_map_twice] using
      path_rotate cs i hp (nonsimple_map i hn)
  · intro hp
    exact path_rotate cs i hp hn

theorem paths_rotate_iff (O O' : RatioOrder (M := M) (cs := cs)) (i : I)
    (hcmp : ∀ a b : PositiveRoot M cs, a ≠ simplePositive i → b ≠ simplePositive i →
      (O'.slope (positiveAction (cs.simple i) a) < O'.slope (positiveAction (cs.simple i) b) ↔
        O.slope a < O.slope b))
    {x y : W} {p : List (Edge cs)} (hn : Nonsimple i p) :
    p.map (rotateEdge cs i) ∈ paths O' (cs.simple i*x) (cs.simple i*y) ↔ p ∈ paths O x y := by
  rw [mem_paths,mem_paths,path_rotate_iff i hn,List.pairwise_map]
  apply and_congr_right
  intro _
  apply List.Pairwise.iff_of_mem
  intro e f he hf
  simpa only [score,rotateEdge_root cs i e (hn e he),rotateEdge_root cs i f (hn f hf)] using
    hcmp (rootLabel cs e) (rootLabel cs f) (hn e he) (hn f hf)

theorem nonsimple_of_greatest (O : RatioOrder (M := M) (cs := cs)) (i : I)
    (hmax : ∀ a : PositiveRoot M cs, a ≠ simplePositive i →
      O.slope a < O.slope (simplePositive i))
    {x y : W} (hy : ¬cs.length (cs.simple i*y) < cs.length y)
    {p : List (Edge cs)} (hp : p ∈ paths O x y) : Nonsimple i p := by
  rw [mem_paths] at hp
  rcases hp with ⟨hp,ho⟩
  induction p generalizing x with
  | nil => simp [Nonsimple]
  | cons e p ih =>
    have he : rootLabel cs e ≠ simplePositive i := by
      intro he
      cases p with
      | nil =>
        have hy' : target cs e = y := hp.2
        have hr := (rootLabel_simple_iff cs i e).mp he
        have hx' : source cs e = cs.simple i*y := by
          rw [← hy',hr,cs.simple_mul_simple_cancel_left]
        have hl := e.property.1
        change cs.length (source cs e) < cs.length (target cs e) at hl
        rw [hy',hx'] at hl
        exact hy hl
      | cons f p =>
        have hlt := (List.pairwise_cons.mp ho).1 f List.mem_cons_self
        have hle : score O f ≤ O.slope (simplePositive i) := by
          by_cases hf : rootLabel cs f = simplePositive i
          · exact le_of_eq (congrArg O.slope hf)
          · exact (hmax _ hf).le
        have hes : score O e = O.slope (simplePositive i) := congrArg O.slope he
        exact (not_lt_of_ge hle) (hes ▸ hlt)
    intro f hf
    rcases List.mem_cons.mp hf with rfl|hf
    · exact he
    · exact ih hp.2 ho.tail f hf

theorem nonsimple_tail_of_least (O : RatioOrder (M := M) (cs := cs)) (i : I)
    (hmin : ∀ a : PositiveRoot M cs, a ≠ simplePositive i →
      O.slope (simplePositive i) < O.slope a)
    {e : Edge cs} {p : List (Edge cs)}
    (ho : (e::p).Pairwise (fun e f => score O e < score O f)) : Nonsimple i p := by
  intro f hf heq
  have hef := (List.pairwise_cons.mp ho).1 f hf
  have he : O.slope (simplePositive i) ≤ score O e := by
    by_cases he : rootLabel cs e = simplePositive i
    · exact le_of_eq (congrArg O.slope he).symm
    · exact (hmin _ he).le
  have hf' : score O f = O.slope (simplePositive i) := congrArg O.slope heq
  exact (not_lt_of_ge he) (hf' ▸ hef)

theorem nonsimple_of_least_descent (O : RatioOrder (M := M) (cs := cs)) (i : I)
    (hmin : ∀ a : PositiveRoot M cs, a ≠ simplePositive i →
      O.slope (simplePositive i) < O.slope a)
    {x y : W} (hx : cs.length (cs.simple i*x) < cs.length x)
    {p : List (Edge cs)} (hp : p ∈ paths O x y) : Nonsimple i p := by
  obtain ⟨hp,ho⟩ := (mem_paths O x y p).mp hp
  cases p with
  | nil => simp [Nonsimple]
  | cons e p =>
    have he : rootLabel cs e ≠ simplePositive i := by
      intro he
      have hr := (rootLabel_simple_iff cs i e).mp he
      have hl := e.property.1
      change cs.length (source cs e) < cs.length (target cs e) at hl
      rw [hr,hp.1] at hl
      exact (lt_asymm hx hl)
    intro f hf
    rcases List.mem_cons.mp hf with rfl|hf
    · exact he
    · exact nonsimple_tail_of_least O i hmin ho f hf

def nonsimplePaths (O : RatioOrder (M := M) (cs := cs)) (i : I) (x y : W) :
    Finset (List (Edge cs)) := (paths O x y).filter (Nonsimple i)

@[simp] theorem mem_nonsimplePaths (O : RatioOrder (M := M) (cs := cs)) (i : I)
    (x y : W) (p : List (Edge cs)) :
    p ∈ nonsimplePaths O i x y ↔ p ∈ paths O x y ∧ Nonsimple i p := by
  simp [nonsimplePaths]

theorem sum_nonsimple_rotate (O O' : RatioOrder (M := M) (cs := cs)) (i : I)
    (hmax : ∀ a : PositiveRoot M cs, a ≠ simplePositive i →
      O'.slope a < O'.slope (simplePositive i))
    (hcmp : ∀ a b : PositiveRoot M cs, a ≠ simplePositive i → b ≠ simplePositive i →
      (O'.slope (positiveAction (cs.simple i) a) < O'.slope (positiveAction (cs.simple i) b) ↔
        O.slope a < O.slope b))
    (x y : W) (hy : cs.length (cs.simple i*y) < cs.length y) :
    ∑ p ∈ nonsimplePaths O i x y, (Polynomial.X : Polynomial ℤ)^p.length =
      polynomial O' (cs.simple i*x) (cs.simple i*y) := by
  unfold polynomial
  have hasc : ¬cs.length (cs.simple i*(cs.simple i*y)) < cs.length (cs.simple i*y) := by
    rw [cs.simple_mul_simple_cancel_left]
    omega
  apply Finset.sum_bij (fun p _ => p.map (rotateEdge cs i))
  · intro p hp
    obtain ⟨hp,hn⟩ := (mem_nonsimplePaths O i x y p).mp hp
    exact (paths_rotate_iff O O' i hcmp hn).mpr hp
  · intro p hp q hq he
    have := congrArg (List.map (rotateEdge cs i)) he
    simpa only [path_map_twice] using this
  · intro q hq
    have hn := nonsimple_of_greatest O' i hmax hasc hq
    refine ⟨q.map (rotateEdge cs i),?_,path_map_twice i q⟩
    have hn' := nonsimple_map i hn
    apply (mem_nonsimplePaths O i x y _).mpr
    refine ⟨?_,hn'⟩
    apply (paths_rotate_iff O O' i hcmp hn').mp
    simpa only [path_map_twice] using hq
  · intro p hp
    simp only [List.length_map]


variable (cs)
def simpleEdge (i : I) (x : W) (hx : cs.length x < cs.length (cs.simple i*x)) : Edge cs :=
  ⟨(x,cs.simple i*x),hx,cs.simple i,cs.isReflection_simple i,rfl⟩

omit [Fintype I] in
@[simp] theorem simpleEdge_source (i : I) (x : W) (hx : cs.length x < cs.length (cs.simple i*x)) :
    source cs (simpleEdge cs i x hx) = x := rfl

omit [Fintype I] in
@[simp] theorem simpleEdge_target (i : I) (x : W) (hx : cs.length x < cs.length (cs.simple i*x)) :
    target cs (simpleEdge cs i x hx) = cs.simple i*x := rfl

@[simp] theorem simpleEdge_root (i : I) (x : W) (hx : cs.length x < cs.length (cs.simple i*x)) :
    rootLabel cs (simpleEdge cs i x hx) = simplePositive i :=
  (rootLabel_simple_iff cs i _).mpr rfl

variable {cs}
theorem cons_simple_mem (O : RatioOrder (M := M) (cs := cs)) (i : I)
    (hmin : ∀ a : PositiveRoot M cs, a ≠ simplePositive i →
      O.slope (simplePositive i) < O.slope a)
    {x y : W} (hx : cs.length x < cs.length (cs.simple i*x))
    {p : List (Edge cs)} (hp : p ∈ nonsimplePaths O i (cs.simple i*x) y) :
    simpleEdge cs i x hx :: p ∈ paths O x y := by
  obtain ⟨hp,hn⟩ := (mem_nonsimplePaths O i _ _ _).mp hp
  obtain ⟨hp,ho⟩ := (mem_paths O _ _ _).mp hp
  apply (mem_paths O _ _ _).mpr
  refine ⟨⟨rfl,hp⟩,List.pairwise_cons.mpr ⟨?_,ho⟩⟩
  intro e he
  change O.slope (rootLabel cs (simpleEdge cs i x hx)) < O.slope (rootLabel cs e)
  rw [simpleEdge_root]
  exact hmin _ (hn e he)

theorem not_nonsimple_iff_cons (O : RatioOrder (M := M) (cs := cs)) (i : I)
    (hmin : ∀ a : PositiveRoot M cs, a ≠ simplePositive i →
      O.slope (simplePositive i) < O.slope a)
    {x y : W} (hx : cs.length x < cs.length (cs.simple i*x)) (p : List (Edge cs)) :
    p ∈ (paths O x y).filter (fun p => ¬Nonsimple i p) ↔
      ∃ q ∈ nonsimplePaths O i (cs.simple i*x) y, p = simpleEdge cs i x hx :: q := by
  constructor
  · intro hp
    obtain ⟨hp,hn⟩ := Finset.mem_filter.mp hp
    obtain ⟨hp,ho⟩ := (mem_paths O _ _ _).mp hp
    cases p with
    | nil => exact (hn (by simp [Nonsimple])).elim
    | cons e p =>
      have hnp : Nonsimple i p := nonsimple_tail_of_least O i hmin ho
      have he : rootLabel cs e = simplePositive i := by
        by_contra he
        apply hn
        intro f hf
        rcases List.mem_cons.mp hf with rfl|hf
        · exact he
        · exact hnp f hf
      have heq : e = simpleEdge cs i x hx := by
        apply Subtype.ext
        apply Prod.ext
        · exact hp.1
        · change target cs e = cs.simple i*x
          rw [(rootLabel_simple_iff cs i e).mp he,hp.1]
      subst e
      refine ⟨p,(mem_nonsimplePaths O i _ _ _).mpr ⟨?_,hnp⟩,rfl⟩
      exact (mem_paths O _ _ _).mpr ⟨hp.2,ho.tail⟩
  · rintro ⟨q,hq,rfl⟩
    apply Finset.mem_filter.mpr
    refine ⟨cons_simple_mem O i hmin hx hq,?_⟩
    intro hn
    exact hn _ List.mem_cons_self (simpleEdge_root cs i x hx)

theorem polynomial_split (O : RatioOrder (M := M) (cs := cs)) (i : I)
    (hmin : ∀ a : PositiveRoot M cs, a ≠ simplePositive i →
      O.slope (simplePositive i) < O.slope a)
    {x y : W} (hx : cs.length x < cs.length (cs.simple i*x)) :
    polynomial O x y =
      (∑ p ∈ nonsimplePaths O i x y, (Polynomial.X : Polynomial ℤ)^p.length) +
      Polynomial.X * (∑ p ∈ nonsimplePaths O i (cs.simple i*x) y,
        (Polynomial.X : Polynomial ℤ)^p.length) := by
  unfold polynomial
  rw [← Finset.sum_filter_add_sum_filter_not (paths O x y) (Nonsimple i)]
  congr 1
  rw [Finset.mul_sum]
  symm
  apply Finset.sum_bij (fun p _ => simpleEdge cs i x hx :: p)
  · intro p hp
    exact (not_nonsimple_iff_cons O i hmin hx _).mpr ⟨p,hp,rfl⟩
  · intro p hp q hq he
    exact List.cons.inj he |>.2
  · intro q hq
    obtain ⟨p,hp,rfl⟩ := (not_nonsimple_iff_cons O i hmin hx q).mp hq
    exact ⟨p,hp,rfl⟩
  · intro p hp
    simp only [List.length_cons,pow_succ']

/-- The path expansion satisfies exactly the genuine normalized Hecke
recursion, because the chosen geometric order can be rotated at a descent. -/
theorem polynomial_recursion (O O' : RatioOrder (M := M) (cs := cs)) (i : I)
    (hmin : ∀ a : PositiveRoot M cs, a ≠ simplePositive i →
      O.slope (simplePositive i) < O.slope a)
    (hmax : ∀ a : PositiveRoot M cs, a ≠ simplePositive i →
      O'.slope a < O'.slope (simplePositive i))
    (hcmp : ∀ a b : PositiveRoot M cs, a ≠ simplePositive i → b ≠ simplePositive i →
      (O'.slope (positiveAction (cs.simple i) a) < O'.slope (positiveAction (cs.simple i) b) ↔
        O.slope a < O.slope b))
    (x y : W) (hy : cs.length (cs.simple i*y) < cs.length y) :
    polynomial O x y = if cs.length (cs.simple i*x) < cs.length x then
      polynomial O' (cs.simple i*x) (cs.simple i*y) else
      polynomial O' (cs.simple i*x) (cs.simple i*y) +
        Polynomial.X * polynomial O' x (cs.simple i*y) := by
  split_ifs with hx
  · have heq : nonsimplePaths O i x y = paths O x y := by
      ext p
      rw [mem_nonsimplePaths]
      exact and_iff_left_of_imp (nonsimple_of_least_descent O i hmin hx)
    rw [← sum_nonsimple_rotate O O' i hmax hcmp x y hy,heq]
    rfl
  · have ha : cs.length x < cs.length (cs.simple i*x) := by
      have := cs.length_simple_mul x i
      omega
    rw [polynomial_split O i hmin ha,
      sum_nonsimple_rotate O O' i hmax hcmp x y hy,
      sum_nonsimple_rotate O O' i hmax hcmp (cs.simple i*x) y hy,
      cs.simple_mul_simple_cancel_left]


@[simp] theorem paths_diagonal (O : RatioOrder (M := M) (cs := cs)) (x : W) :
    paths O x x = {[]} := by
  ext p
  rw [mem_paths,Finset.mem_singleton]
  cases p with
  | nil => simp [IsPath]
  | cons e p =>
    constructor
    · rintro ⟨hp,_⟩
      have hl := length_le_of_bruhat cs (path_le cs hp.2)
      have he := e.property.1
      change cs.length (source cs e) < cs.length (target cs e) at he
      rw [hp.1] at he
      omega
    · simp

@[simp] theorem polynomial_diagonal (O : RatioOrder (M := M) (cs := cs)) (x : W) :
    polynomial O x x = 1 := by
  simp [polynomial]

theorem polynomial_zero (O : RatioOrder (M := M) (cs := cs)) (x y : W)
    (h : ¬BruhatLE cs x y) : polynomial O x y = 0 := by
  have hp : paths O x y = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro p hp
    exact h (path_le cs ((mem_paths O x y p).mp hp).1)
  simp [polynomial,hp]

/-- Dyer's increasing-path formula for a genuine generic geometric order
whose numerator is in the top chamber. The target is the Hecke-defined
normalized R-polynomial, not a renamed path polynomial. -/
theorem polynomial_eq_rTilde (O : RatioOrder (M := M) (cs := cs)) (x y : W)
    (hc : O.Chamber y) : polynomial O x y = Hecke.rTilde cs x y := by
  generalize hn : cs.length y = n
  induction n using Nat.strong_induction_on generalizing O x y with
  | h n ih =>
    by_cases hy : y=1
    · subst y
      by_cases hx : x=1
      · subst x
        rw [polynomial_diagonal,Hecke.rTilde_diagonal]
      · have hxy : ¬ BruhatLE cs x 1 := by
          intro h
          have hl := length_le_of_bruhat cs h
          rw [cs.length_one] at hl
          exact hx (cs.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hl))
        rw [polynomial_zero O x 1 hxy,Hecke.rTilde_zero cs x 1 hxy]
    · obtain ⟨i,O',hi,hc',hends,hcmp⟩ := O.exists_rotation hy hc
      have hi' : cs.length (cs.simple i*y) < n := hn ▸ hi
      have hsx := ih _ hi' O' (cs.simple i*x) (cs.simple i*y) hc' rfl
      have hx := ih _ hi' O' x (cs.simple i*y) hc' rfl
      rw [polynomial_recursion O O' i (fun a ha => (hends a ha).1)
        (fun a ha => (hends a ha).2) hcmp x y hi,
        Hecke.rTilde_recursion cs x y i hi,hsx,hx]

/-- An adapted geometric order exists for every top, without adding labels
or geometric data to the given interval isomorphism. -/
theorem exists_dyer_schedule (y : W) :
    ∃ O : RatioOrder (M := M) (cs := cs), O.Chamber y ∧
      ∀ x : W, polynomial O x y = Hecke.rTilde cs x y := by
  obtain ⟨O,hO⟩ := exists_ratioOrder_chamber (M := M) (cs := cs) y
  exact ⟨O,hO,fun x => polynomial_eq_rTilde O x y hO⟩

end
end KLInvariance.AdaptedDyer
end

end OAI
