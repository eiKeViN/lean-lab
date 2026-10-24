module
public import Mathlib
public import ForMathlib.Combinatorics.MomentGraph.Bruhat.Basic
public import ForMathlib.GroupTheory.Coxeter.Dihedral.Diamonds

public section

/-! Semantic home: ForMathlib.GroupTheory.Coxeter.Dihedral.IntervalTransport. Source spans: DyerPaths:6, DyerPaths:13, DyerPaths:16, DyerPaths:8.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.Dihedral
variable {G : Type*} [Group G] {N : CoxeterMatrix Bool}

/-- Exactly two intermediate vertices characterize relative rank two as soon
as one two-edge path exists. Used to rule out skipped ranks after transport. -/
theorem rank_two_of_two_step_bound (ds : CoxeterSystem N G) {x y a b : G}
    (ha : BruhatStep ds x a) (hay : BruhatStep ds a y)
    (hbound : ∀ z, BruhatStep ds x z → BruhatStep ds z y → z = a ∨ z = b) :
    ds.length y = ds.length x + 2 := by
  have hxa := (step_iff_odd ds x a).mp ha
  have hay' := (step_iff_odd ds a y).mp hay
  rw [Nat.odd_iff] at hxa hay'
  have heven : (ds.length y - ds.length x) % 2 = 0 := by omega
  by_contra hlen
  have hlarge : ds.length x + 3 < ds.length y := by omega
  obtain ⟨p,q,hpq,hlevel⟩ := two_elements_length ds
    (by omega : 0 < ds.length x+1) (w := y) (by omega)
  have hp := (hlevel p).mpr (Or.inl rfl)
  have hq := (hlevel q).mpr (Or.inr rfl)
  obtain ⟨r,s,hrs,hlevel'⟩ := two_elements_length ds
    (by omega : 0 < ds.length x+3) hlarge
  have hr := (hlevel' r).mpr (Or.inl rfl)
  have paths : ∀ z, ds.length z = ds.length x+1 ∨ ds.length z = ds.length x+3 →
      BruhatStep ds x z ∧ BruhatStep ds z y := by
    intro z hz
    rw [step_iff_odd,step_iff_odd,Nat.odd_iff,Nat.odd_iff]
    rcases hz with hz | hz <;> omega
  have pp := paths p (Or.inl hp)
  have pq := paths q (Or.inl hq)
  have pr := paths r (Or.inr hr)
  have hpr : p ≠ r := by intro he; rw [he] at hp; omega
  have hqr : q ≠ r := by intro he; rw [he] at hq; omega
  rcases hbound p pp.1 pp.2 with hp' | hp' <;>
    rcases hbound q pq.1 pq.2 with hq' | hq' <;>
    rcases hbound r pr.1 pr.2 with hr' | hr' <;> grind

end KLInvariance.Dihedral
end


section
namespace KLInvariance.Dihedral
variable {W : Type*} [Group W] {M : CoxeterMatrix Bool}
noncomputable section

/-- The genuine diagram automorphism of an arbitrary rank-two Coxeter system,
including the infinite one. -/
@[expose] def swapHom (cs : CoxeterSystem M W) : W →* W :=
  cs.lift ⟨fun i => cs.simple (!i), by
    intro i j
    have he : M i j = M (!i) (!j) := by
      cases i <;> cases j
      · simp
      · exact M.symmetric _ _
      · exact M.symmetric _ _
      · simp
    rw [he]
    exact cs.simple_mul_simple_pow _ _⟩

@[simp] theorem swapHom_simple (cs : CoxeterSystem M W) (i : Bool) :
    swapHom cs (cs.simple i) = cs.simple (!i) := cs.lift_apply_simple _ i

@[simp] theorem swapHom_involutive (cs : CoxeterSystem M W) :
    Function.Involutive (swapHom cs) := by
  intro w
  apply cs.simple_induction w
  · intro i
    simp
  · simp
  · intro a b ha hb
    simp only [map_mul,ha,hb]

@[expose] def swap (cs : CoxeterSystem M W) : W ≃* W where
  toFun := swapHom cs
  invFun := swapHom cs
  left_inv := swapHom_involutive cs
  right_inv := swapHom_involutive cs
  map_mul' := map_mul (swapHom cs)

@[simp] theorem swap_simple (cs : CoxeterSystem M W) (i : Bool) :
    swap cs (cs.simple i) = cs.simple (!i) := swapHom_simple cs i

@[simp] theorem swap_swap (cs : CoxeterSystem M W) (w : W) :
    swap cs (swap cs w) = w := swapHom_involutive cs w

theorem swap_wordProd (cs : CoxeterSystem M W) (ω : List Bool) :
    swap cs (cs.wordProd ω) = cs.wordProd (ω.map Bool.not) := by
  induction ω with
  | nil => simp
  | cons i ω ih =>
    simp only [cs.wordProd_cons, map_mul, swap_simple, List.map_cons, ih]

@[simp] theorem length_swap (cs : CoxeterSystem M W) (w : W) :
    cs.length (swap cs w) = cs.length w := by
  have hle (z : W) : cs.length (swap cs z) ≤ cs.length z := by
    obtain ⟨ω,hω,rfl⟩ := cs.exists_isReduced z
    rw [swap_wordProd, hω.eq]
    simpa using cs.length_wordProd_le (ω.map Bool.not)
  exact le_antisymm (hle w) (by simpa using hle (swap cs w))

@[simp] theorem descent_swap (cs : CoxeterSystem M W) (w : W) (i : Bool) :
    cs.IsLeftDescent (swap cs w) i ↔ cs.IsLeftDescent w (!i) := by
  unfold CoxeterSystem.IsLeftDescent
  rw [length_swap, ← Bool.not_not i, ← swap_simple, ← map_mul, length_swap]
  simp

/-- A nonzero length below an existing greater length has exactly one left
simple descent. This is not asserted for a finite dihedral longest element. -/
theorem unique_leftDescent (cs : CoxeterSystem M W) {w z : W}
    (hw : 0 < cs.length w) (hz : cs.length w < cs.length z) :
    ∃! i : Bool, cs.IsLeftDescent w i := by
  obtain ⟨i,hi⟩ := cs.exists_leftDescent_of_ne_one (w := w) (by
    intro he
    rw [he,cs.length_one] at hw
    omega)
  refine ⟨i,hi,?_⟩
  intro j hj
  by_contra hji
  have hj' : j = !i := by cases i <;> cases j <;> simp_all
  have he : cs.wordProd (alt i (cs.length w)) =
      cs.wordProd (alt (!i) (cs.length w)) := by
    rw [← eq_alt_of_descent cs i hi, ← hj', ← eq_alt_of_descent cs j hj]
  obtain ⟨a,b,hab,hab'⟩ := two_elements_length cs hw hz
  have all_eq (v : W) (hv : cs.length v = cs.length w) : v=w := by
    obtain ⟨k,hk⟩ := exists_alt cs v
    rw [hv] at hk
    have hki : k=i ∨ k=(!i) := by cases k <;> cases i <;> simp
    rcases hki with hki | hki
    · rw [hki] at hk
      exact hk.trans (eq_alt_of_descent cs i hi).symm
    · rw [hki] at hk
      exact hk.trans (he.symm.trans (eq_alt_of_descent cs i hi).symm)
  exact hab ((all_eq a ((hab' a).mpr (.inl rfl))).trans
    (all_eq b ((hab' b).mpr (.inr rfl))).symm)

/-- Internally, the diagram involution interchanges the two unique-descent
vertices of each rank. -/
theorem descent_swap_false_iff_not (cs : CoxeterSystem M W) {w z : W}
    (hw : 0 < cs.length w) (hz : cs.length w < cs.length z) :
    cs.IsLeftDescent (swap cs w) false ↔ ¬ cs.IsLeftDescent w false := by
  rw [descent_swap]
  obtain ⟨i,hi,hu⟩ := unique_leftDescent cs hw hz
  cases i
  · constructor
    · intro h
      have hh := hu true h
      contradiction
    · exact fun h => (h hi).elim
  · constructor
    · intro _ h
      have hh := hu false h
      contradiction
    · exact fun _ => hi

end
end KLInvariance.Dihedral
end


section
namespace KLInvariance.Dihedral
variable {W : Type*} [Group W] {M : CoxeterMatrix Bool}
noncomputable section
local instance _root_.OAI.KLInvariance.Dihedral.instDecidable_oAI_5 (p : Prop) : Decidable p := Classical.propDecidable p

/-- Switch the two vertices at every strictly internal rank, leaving all
other ranks fixed. The diagram involution supplies the intrinsic switch. -/
@[expose] def rankFlip (cs : CoxeterSystem M W) (L H : ℕ) (w : W) : W :=
  if L < cs.length w ∧ cs.length w < H then swap cs w else w

@[simp] theorem length_rankFlip (cs : CoxeterSystem M W) (L H : ℕ) (w : W) :
    cs.length (rankFlip cs L H w) = cs.length w := by
  unfold rankFlip
  split <;> simp

@[simp] theorem rankFlip_involutive (cs : CoxeterSystem M W) (L H : ℕ) :
    Function.Involutive (rankFlip cs L H) := by
  intro w
  unfold rankFlip
  split <;> simp_all

@[simp] theorem rankFlip_lower (cs : CoxeterSystem M W) (x y : W) :
    rankFlip cs (cs.length x) (cs.length y) x = x := by simp [rankFlip]

@[simp] theorem rankFlip_upper (cs : CoxeterSystem M W) (x y : W) :
    rankFlip cs (cs.length x) (cs.length y) y = y := by simp [rankFlip]

@[simp] theorem rankFlip_bruhat_iff (cs : CoxeterSystem M W) (L H : ℕ) (x y : W) :
    BruhatLE cs (rankFlip cs L H x) (rankFlip cs L H y) ↔ BruhatLE cs x y := by
  simp only [bruhat_iff_length_lt_or_eq, length_rankFlip,
    (rankFlip_involutive cs L H).injective.eq_iff]

@[simp] theorem rankFlip_step_iff (cs : CoxeterSystem M W) (L H : ℕ) (x y : W) :
    BruhatStep cs (rankFlip cs L H x) (rankFlip cs L H y) ↔ BruhatStep cs x y := by
  simp only [step_iff_odd, length_rankFlip]

/-- An automorphism of the unlabelled full dihedral interval, fixing its ends.
It need not arise from a Coxeter-system automorphism at those ends. -/
@[expose] def intervalFlip (cs : CoxeterSystem M W) (lo hi : W) :
    Interval cs lo hi ≃o Interval cs lo hi where
  toFun x := ⟨rankFlip cs (cs.length lo) (cs.length hi) x.val, by
    constructor
    · simpa only [rankFlip_lower] using
        (rankFlip_bruhat_iff cs (cs.length lo) (cs.length hi) lo x.val).mpr x.property.1
    · simpa only [rankFlip_upper] using
        (rankFlip_bruhat_iff cs (cs.length lo) (cs.length hi) x.val hi).mpr x.property.2⟩
  invFun x := ⟨rankFlip cs (cs.length lo) (cs.length hi) x.val, by
    constructor
    · simpa only [rankFlip_lower] using
        (rankFlip_bruhat_iff cs (cs.length lo) (cs.length hi) lo x.val).mpr x.property.1
    · simpa only [rankFlip_upper] using
        (rankFlip_bruhat_iff cs (cs.length lo) (cs.length hi) x.val hi).mpr x.property.2⟩
  left_inv x := Subtype.ext (rankFlip_involutive cs _ _ x.val)
  right_inv x := Subtype.ext (rankFlip_involutive cs _ _ x.val)
  map_rel_iff' := rankFlip_bruhat_iff cs _ _ _ _

@[simp] theorem intervalFlip_val (cs : CoxeterSystem M W) (lo hi : W)
    (x : Interval cs lo hi) :
    (intervalFlip cs lo hi x).val = rankFlip cs (cs.length lo) (cs.length hi) x.val := rfl

@[simp] theorem intervalFlip_involutive (cs : CoxeterSystem M W) (lo hi : W) :
    Function.Involutive (intervalFlip cs lo hi) :=
  fun x => Subtype.ext (rankFlip_involutive cs _ _ x.val)

@[expose] def edgeFlip (cs : CoxeterSystem M W) (lo hi : W) :
    BruhatGraph.Edge cs lo hi ≃ BruhatGraph.Edge cs lo hi where
  toFun e := ⟨(intervalFlip cs lo hi e.val.1, intervalFlip cs lo hi e.val.2),
    (rankFlip_step_iff cs _ _ _ _).mpr e.property⟩
  invFun e := ⟨(intervalFlip cs lo hi e.val.1, intervalFlip cs lo hi e.val.2),
    (rankFlip_step_iff cs _ _ _ _).mpr e.property⟩
  left_inv e := Subtype.ext (Prod.ext
    (intervalFlip_involutive cs lo hi e.val.1)
    (intervalFlip_involutive cs lo hi e.val.2))
  right_inv e := Subtype.ext (Prod.ext
    (intervalFlip_involutive cs lo hi e.val.1)
    (intervalFlip_involutive cs lo hi e.val.2))

@[simp] theorem edgeFlip_source (cs : CoxeterSystem M W) (lo hi : W)
    (e : BruhatGraph.Edge cs lo hi) :
    BruhatGraph.source cs lo hi (edgeFlip cs lo hi e) =
      intervalFlip cs lo hi (BruhatGraph.source cs lo hi e) := rfl

@[simp] theorem edgeFlip_target (cs : CoxeterSystem M W) (lo hi : W)
    (e : BruhatGraph.Edge cs lo hi) :
    BruhatGraph.target cs lo hi (edgeFlip cs lo hi e) =
      intervalFlip cs lo hi (BruhatGraph.target cs lo hi e) := rfl

@[simp] theorem edgeFlip_involutive (cs : CoxeterSystem M W) (lo hi : W) :
    Function.Involutive (edgeFlip cs lo hi) := by
  intro e
  apply Subtype.ext
  change (intervalFlip cs lo hi (intervalFlip cs lo hi e.val.1),
    intervalFlip cs lo hi (intervalFlip cs lo hi e.val.2)) = e.val
  exact Prod.ext (intervalFlip_involutive cs lo hi e.val.1)
    (intervalFlip_involutive cs lo hi e.val.2)

end
end KLInvariance.Dihedral
end


section
namespace KLInvariance.Dihedral
universe u₁ u₂
variable {D : Type u₁} [Group D] {N : CoxeterMatrix Bool} (ds : CoxeterSystem N D)
  {l r : D}

theorem exists_interval_length (hlr : BruhatLE ds l r) {n : ℕ}
    (hnl : ds.length l ≤ n) (hnr : n ≤ ds.length r) :
    ∃ z : Interval ds l r, ds.length z.val = n := by
  by_cases hl : n = ds.length l
  · exact ⟨⟨l,bruhat_refl ds l,hlr⟩,hl.symm⟩
  by_cases hr : n = ds.length r
  · exact ⟨⟨r,hlr,bruhat_refl ds r⟩,hr.symm⟩
  obtain ⟨a,b,_,ha,_⟩ := two_interval_elements_length ds
    (⟨l,bruhat_refl ds l,hlr⟩ : Interval ds l r)
    (⟨r,hlr,bruhat_refl ds r⟩ : Interval ds l r)
    (n := n) (by dsimp; omega) (by dsimp; omega)
  exact ⟨a,ha⟩

variable {D' : Type u₂} [Group D'] {N' : CoxeterMatrix Bool}
  (ds' : CoxeterSystem N' D')

theorem map_cover_length
    (f : Interval ds l r → D')
    (hgraph : ∀ x y : Interval ds l r, BruhatStep ds x.val y.val →
      BruhatStep ds' (f x) (f y))
    (htwo : ∀ x y : Interval ds l r, ds.length y.val = ds.length x.val+2 →
      ds'.length (f y) = ds'.length (f x)+2)
    (hlr : BruhatLE ds l r) (hrank : ds.length l+2 ≤ ds.length r)
    {x y : Interval ds l r} (hxy : ds.length y.val = ds.length x.val+1) :
    ds'.length (f y) = ds'.length (f x)+1 := by
  have hstep : ∀ p q : Interval ds l r, ds.length q.val = ds.length p.val+1 →
      ds'.length (f p) < ds'.length (f q) := by
    intro p q hpq
    apply (hgraph p q ?_).1
    rw [step_iff_odd,Nat.odd_iff]
    omega
  have hxy' := hstep x y hxy
  have hyr := length_le_of_bruhat ds y.property.2
  by_cases hy : ds.length y.val < ds.length r
  · obtain ⟨z,hz⟩ := exists_interval_length ds hlr
      (n := ds.length y.val+1)
      (by have := length_le_of_bruhat ds y.property.1; omega) (by omega)
    have hyz := hstep y z hz
    have hxz := htwo x z (by omega)
    omega
  · obtain ⟨z,hz⟩ := exists_interval_length ds hlr
      (n := ds.length x.val-1) (by omega) (by omega)
    have hzx := hstep z x (by omega)
    have hzy := htwo z y (by omega)
    omega

/-- A directed dihedral-interval graph injection which does not stretch any
rank-two interval preserves all relative ranks. -/
theorem map_length_affine
    (f : Interval ds l r → D')
    (hgraph : ∀ x y : Interval ds l r, BruhatStep ds x.val y.val →
      BruhatStep ds' (f x) (f y))
    (htwo : ∀ x y : Interval ds l r, ds.length y.val = ds.length x.val+2 →
      ds'.length (f y) = ds'.length (f x)+2)
    (hlr : BruhatLE ds l r) (hrank : ds.length l+2 ≤ ds.length r)
    (z : Interval ds l r) :
    ds'.length (f z) + ds.length l =
      ds'.length (f ⟨l,bruhat_refl ds l,hlr⟩) + ds.length z.val := by
  let lo : Interval ds l r := ⟨l,bruhat_refl ds l,hlr⟩
  change ds'.length (f z)+ds.length l=ds'.length (f lo)+ds.length z.val
  suffices ∀ n, ∀ z : Interval ds l r, ds.length z.val=n →
      ds'.length (f z)+ds.length l=ds'.length (f lo)+ds.length z.val from this _ z rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro z hz
    by_cases he : z=lo
    · simp [he,lo]
    have hlt : ds.length l < ds.length z.val :=
      length_lt_of_bruhat_ne ds z.property.1 (fun h => he (Subtype.ext h.symm))
    obtain ⟨p,hp⟩ := exists_interval_length ds hlr (n := ds.length z.val-1)
      (by omega) (by have := length_le_of_bruhat ds z.property.2; omega)
    have ihp := ih (ds.length p.val) (by omega) p rfl
    have hc := map_cover_length ds ds' f hgraph htwo hlr hrank (x := p) (y := z)
      (by omega)
    omega

/-- Once relative covers are recovered, the image exhausts rather than merely
embeds in the target dihedral interval. -/
theorem range_eq_interval_of_rank_two
    (f : Interval ds l r → D') (hinj : Function.Injective f)
    (hgraph : ∀ x y : Interval ds l r, BruhatStep ds x.val y.val →
      BruhatStep ds' (f x) (f y))
    (htwo : ∀ x y : Interval ds l r, ds.length y.val = ds.length x.val+2 →
      ds'.length (f y) = ds'.length (f x)+2)
    (hlr : BruhatLE ds l r) (hrank : ds.length l+2 ≤ ds.length r) :
    Set.range f = {z | BruhatLE ds' (f ⟨l,bruhat_refl ds l,hlr⟩) z ∧
      BruhatLE ds' z (f ⟨r,hlr,bruhat_refl ds r⟩)} := by
  let lo : Interval ds l r := ⟨l,bruhat_refl ds l,hlr⟩
  let hi : Interval ds l r := ⟨r,hlr,bruhat_refl ds r⟩
  have hlen (z : Interval ds l r) : ds'.length (f z)+ds.length l =
      ds'.length (f lo)+ds.length z.val :=
    map_length_affine ds ds' f hgraph htwo hlr hrank z
  have hhi : ds'.length (f hi)+ds.length l=ds'.length (f lo)+ds.length r := hlen hi
  have horder (x y : Interval ds l r) :
      BruhatLE ds' (f x) (f y) ↔ x ≤ y := by
    change BruhatLE ds' (f x) (f y) ↔ BruhatLE ds x.val y.val
    rw [bruhat_iff_length_lt_or_eq,bruhat_iff_length_lt_or_eq]
    have hx := hlen x
    have hy := hlen y
    constructor
    · rintro (h | h)
      · left; omega
      · exact Or.inr (congrArg Subtype.val (hinj h))
    · rintro (h | h)
      · left; omega
      · exact Or.inr (congrArg f (Subtype.ext h))
  apply Set.ext
  intro z
  change (∃ x, f x=z) ↔ BruhatLE ds' (f lo) z ∧ BruhatLE ds' z (f hi)
  constructor
  · rintro ⟨x,rfl⟩
    exact ⟨(horder lo x).mpr x.property.1,(horder x hi).mpr x.property.2⟩
  · intro hz
    by_cases hlo : z=f lo
    · exact ⟨lo,hlo.symm⟩
    by_cases htop : z=f hi
    · exact ⟨hi,htop.symm⟩
    have hzlo := length_lt_of_bruhat_ne ds' hz.1 (Ne.symm hlo)
    have hzhi := length_lt_of_bruhat_ne ds' hz.2 htop
    have hnlo : ds.length l < ds.length l+(ds'.length z-ds'.length (f lo)) := by omega
    have hnhi : ds.length l+(ds'.length z-ds'.length (f lo)) < ds.length r := by omega
    obtain ⟨a,b,hab,ha,hb⟩ := two_interval_elements_length ds lo hi hnlo hnhi
    have hfa : ds'.length (f a)=ds'.length z := by have := hlen a; omega
    have hfb : ds'.length (f b)=ds'.length z := by have := hlen b; omega
    obtain ⟨p,q,hpq,helements⟩ := two_elements_length ds' (by omega : 0<ds'.length z) hzhi
    have hp := (helements (f a)).mp hfa
    have hq := (helements (f b)).mp hfb
    have hr := (helements z).mp rfl
    have hab' : f a ≠ f b := fun h => hab (hinj h)
    have he : z=f a ∨ z=f b := by grind
    rcases he with he | he
    · exact ⟨a,he.symm⟩
    · exact ⟨b,he.symm⟩

end KLInvariance.Dihedral
end

end OAI
