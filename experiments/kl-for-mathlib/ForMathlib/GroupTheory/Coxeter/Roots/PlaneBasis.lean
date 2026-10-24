module
public import Mathlib
public import ForMathlib.GroupTheory.Coxeter.Dihedral.PlaneSystem
public import ForMathlib.GroupTheory.Coxeter.Roots.PlaneLength
public import ForMathlib.GroupTheory.Coxeter.Roots.PlaneSubgroup

public section

/-! Semantic home: ForMathlib.GroupTheory.Coxeter.Roots.PlaneBasis. Source spans: Decomposition:5, Decomposition:7.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.TitsSpace
open Module
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
noncomputable section

/-- Any two distinct positive roots in a two-dimensional root plane span it. -/
theorem rootPlane_eq_of_mem (a b l r : PositiveRoot M cs) (hab : a ≠ b)
    (hl : l.val ∈ rootPlane a b) (hr : r.val ∈ rootPlane a b) (hlr : l ≠ r) :
    rootPlane l r = rootPlane a b := by
  apply Submodule.eq_of_le_of_finrank_eq
  · apply Submodule.span_le.mpr
    intro z hz
    change z ∈ rootPlane a b
    rcases Set.mem_insert_iff.mp hz with hz | hz
    · rw [hz]; exact hl
    · rw [Set.mem_singleton_iff.mp hz]; exact hr
  · rw [rootPlane_finrank _ _ hlr, rootPlane_finrank _ _ hab]

/-- Slope betweenness detects the actual positive cone, not only one implication. -/
theorem positive_combination_of_slope_between (a b c : PositiveRoot M cs)
    (hc : c.val ∈ rootPlane a b)
    (hac : geometricSlope a < geometricSlope c)
    (hcb : geometricSlope c < geometricSlope b) :
    ∃ r s : ℝ, 0 < r ∧ 0 < s ∧ c.val = r • a.val + s • b.val := by
  let f := geometricFunctional (M := M) (cs := cs)
  obtain ⟨r, s, he⟩ := Submodule.mem_span_pair.mp hc
  refine ⟨r, s, ?_, ?_, he.symm⟩
  all_goals
    have ha := a.height_pos
    have hb := b.height_pos
    have hh := c.height_pos
    have hfc := congrArg f he
    have hhc := congrArg (height (I := I)) he
    simp only [map_add, map_smul, smul_eq_mul] at hfc hhc
    change f a.val / height a.val <
      f c.val / height c.val at hac
    change f c.val / height c.val <
      f b.val / height b.val at hcb
    have hab := lt_trans hac hcb
    rw [div_lt_div_iff₀ ha hb] at hab
    rw [div_lt_div_iff₀ ha hh] at hac
    rw [div_lt_div_iff₀ hh hb] at hcb
  · have heq : r * (f b.val * height a.val -
        f a.val * height b.val) =
        f b.val * height c.val -
          f c.val * height b.val := by rw [← hfc, ← hhc]; ring
    have hp : 0 < r * (f b.val * height a.val -
        f a.val * height b.val) := by rw [heq]; linarith
    exact (mul_pos_iff.mp hp).resolve_right (by intro h; linarith [h.2]) |>.1
  · have heq : s * (f b.val * height a.val -
        f a.val * height b.val) =
        f c.val * height a.val -
          f a.val * height c.val := by rw [← hfc, ← hhc]; ring
    have hp : 0 < s * (f b.val * height a.val -
        f a.val * height b.val) := by rw [heq]; linarith
    exact (mul_pos_iff.mp hp).resolve_right (by intro h; linarith [h.2]) |>.1

/-- Positivity is convex in the root cone. -/
theorem noninverted_of_positive_combination (w : W) (a b c : PositiveRoot M cs)
    {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hc : c.val = r • a.val + s • b.val)
    (ha : ¬ rootInverted w a) (hb : ¬ rootInverted w b) :
    ¬ rootInverted w c := by
  rw [not_rootInverted_iff] at ha hb ⊢
  intro i
  rw [hc, map_add, map_smul, map_smul]
  exact add_nonneg (mul_nonneg hr (ha i)) (mul_nonneg hs (hb i))

@[simp] theorem not_rootInverted_one (a : PositiveRoot M cs) :
    ¬ rootInverted (1 : W) a := by
  rw [not_rootInverted_iff]
  simp only [inv_one, map_one]
  exact a.property.2

@[simp] theorem rootInverted_ref_self (a : PositiveRoot M cs) :
    rootInverted (rootRef a) a := by
  simpa only [mul_one] using (rootInverted_mul_self 1 a).mpr (not_rootInverted_one a)

/-- A root plane has an extreme positive root. Finiteness of inversion sets
replaces the false assertion that the (real-valued) root heights are discrete. -/
theorem exists_plane_extreme_inverted (a b : PositiveRoot M cs) (hab : a ≠ b) :
    ∃ p : PositiveRoot M cs, p.val ∈ rootPlane a b ∧ rootInverted (rootRef a) p ∧
      ((∀ r : PositiveRoot M cs, r.val ∈ rootPlane a b →
          geometricSlope p ≤ geometricSlope r) ∨
       (∀ r : PositiveRoot M cs, r.val ∈ rootPlane a b →
          geometricSlope r ≤ geometricSlope p)) := by
  classical
  let S := (finite_rootInverted (M := M) (cs := cs) (rootRef a)).toFinset.filter
    (fun r => r.val ∈ rootPlane a b)
  have hS (r : PositiveRoot M cs) : r ∈ S ↔
      rootInverted (rootRef a) r ∧ r.val ∈ rootPlane a b := by
    simp only [S, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
  have haP : a.val ∈ rootPlane a b := Submodule.subset_span (Set.mem_insert _ _)
  have haS : a ∈ S := (hS a).mpr ⟨rootInverted_ref_self a, haP⟩
  obtain ⟨p, hp, hmin⟩ := S.exists_min_image geometricSlope ⟨a, haS⟩
  obtain ⟨q, hq, hmax⟩ := S.exists_max_image geometricSlope ⟨a, haS⟩
  by_cases hleft : ∀ r : PositiveRoot M cs, r.val ∈ rootPlane a b →
      geometricSlope p ≤ geometricSlope r
  · exact ⟨p, (hS p).mp hp |>.2, (hS p).mp hp |>.1, Or.inl hleft⟩
  by_cases hright : ∀ r : PositiveRoot M cs, r.val ∈ rootPlane a b →
      geometricSlope r ≤ geometricSlope q
  · exact ⟨q, (hS q).mp hq |>.2, (hS q).mp hq |>.1, Or.inr hright⟩
  push Not at hleft hright
  obtain ⟨l, hlP, hlp⟩ := hleft
  obtain ⟨r, hrP, hqr⟩ := hright
  have hla := lt_of_lt_of_le hlp (hmin a haS)
  have har := lt_of_le_of_lt (hmax a haS) hqr
  have hlr : l ≠ r := fun h => (lt_trans hla har).ne (congrArg geometricSlope h)
  have hplane := rootPlane_eq_of_mem a b l r hab hlP hrP hlr
  have hlam : ¬ rootInverted (rootRef a) l := by
    intro hi
    exact (not_le_of_gt hlp) (hmin l ((hS l).mpr ⟨hi, hlP⟩))
  have hram : ¬ rootInverted (rootRef a) r := by
    intro hi
    exact (not_le_of_gt hqr) (hmax r ((hS r).mpr ⟨hi, hrP⟩))
  obtain ⟨c, d, hc, hd, he⟩ := positive_combination_of_slope_between l r a
    (hplane.symm ▸ haP) hla har
  exact False.elim ((noninverted_of_positive_combination (rootRef a) l r a
    hc.le hd.le he hlam hram) (rootInverted_ref_self a))

/-- The canonical simple-root criterion stated on the actual ambient roots. -/
@[expose] def PlaneSimple (P : Submodule ℝ (I → ℝ)) (a : PositiveRoot M cs) : Prop :=
  a.val ∈ P ∧ ∀ b : PositiveRoot M cs, b.val ∈ P →
    (rootInverted (rootRef a) b ↔ b = a)

theorem rootInverted_ref_iff_flipped (a b : PositiveRoot M cs) :
    rootInverted (rootRef a) b ↔ flipped a b := by
  unfold rootInverted flipped
  rw [(rootReflection M cs a).property.inv]

/-- An angular extreme inverts exactly its own positive root. -/
theorem planeSimple_of_extreme {P : Submodule ℝ (I → ℝ)}
    (a : PositiveRoot M cs) (ha : a.val ∈ P)
    (hext : (∀ r : PositiveRoot M cs, r.val ∈ P → geometricSlope a ≤ geometricSlope r) ∨
      (∀ r : PositiveRoot M cs, r.val ∈ P → geometricSlope r ≤ geometricSlope a)) :
    PlaneSimple P a := by
  refine ⟨ha, fun b hb => ⟨?_, ?_⟩⟩
  · intro hinv
    by_contra hba
    have hn := (rootInverted_ref_iff_flipped a b).mp hinv
    have hp := partner_mem a b ha hb
    have hs := negative_pair_sum a b hn
    have hc := negative_pair_coefficient_pos a b hn
    have he : a.val = (form M a.val b.val)⁻¹ • b.val +
        (form M a.val b.val)⁻¹ • (partner a b).val := by
      calc
        a.val = (form M a.val b.val)⁻¹ • (form M a.val b.val • a.val) := by
          rw [smul_smul, inv_mul_cancel₀ hc.ne', one_smul]
        _ = _ := by rw [← hs, smul_add]
    have hne : geometricSlope b ≠ geometricSlope (partner a b) := by
      intro h
      exact hba (negative_partner_fixed a b hn (geometricSlope_injective h).symm)
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have hh := geometricSlope_between b (partner a b) a
        (inv_pos.mpr hc) (inv_pos.mpr hc) he hlt
      rcases hext with hmin | hmax
      · exact (not_lt_of_ge (hmin b hb)) hh.1
      · exact (not_lt_of_ge (hmax (partner a b) hp)) hh.2
    · have he' : a.val = (form M a.val b.val)⁻¹ • (partner a b).val +
          (form M a.val b.val)⁻¹ • b.val := by rw [add_comm]; exact he
      have hh := geometricSlope_between (partner a b) b a
        (inv_pos.mpr hc) (inv_pos.mpr hc) he' hlt
      rcases hext with hmin | hmax
      · exact (not_lt_of_ge (hmin (partner a b) hp)) hh.1
      · exact (not_lt_of_ge (hmax b hb)) hh.2
  · intro h
    rw [h]
    exact rootInverted_ref_self a

theorem PlaneSimple.partner_val {P : Submodule ℝ (I → ℝ)}
    {a : PositiveRoot M cs} (ha : PlaneSimple P a)
    {b : PositiveRoot M cs} (hb : b.val ∈ P) (hba : b ≠ a) :
    (partner a b).val = action M cs (rootRef a) b.val := by
  have hn : ¬ rootInverted (rootRef a) b := fun h => hba ((ha.2 b hb).mp h)
  have hp := (not_rootInverted_iff (rootRef a) b).mp hn
  rw [(rootReflection M cs a).property.inv] at hp
  exact positiveAction_eq_of_nonneg _ _ hp

theorem PlaneSimple.exists_nonpositive_pair {P : Submodule ℝ (I → ℝ)}
    {a : PositiveRoot M cs} (ha : PlaneSimple P a)
    {b : PositiveRoot M cs} (hb : b.val ∈ P) (hba : b ≠ a) :
    ∃ c : PositiveRoot M cs, c.val ∈ P ∧ c ≠ a ∧ form M a.val c.val ≤ 0 := by
  by_cases hn : form M a.val b.val ≤ 0
  · exact ⟨b, hb, hba, hn⟩
  · refine ⟨partner a b, partner_mem a b ha.1 hb,
      fun h => hba ((partner_eq_self_of_eq a b).mp h), ?_⟩
    rw [ha.partner_val hb hba, (rootReflection_represents M cs a).action_formula]
    simp only [map_sub, map_smul, smul_eq_mul, a.property.1.norm]
    linarith

theorem noninverted_ref_of_pairing_nonpos (a b : PositiveRoot M cs)
    (hab : form M a.val b.val ≤ 0) : ¬ rootInverted (rootRef b) a := by
  rw [not_rootInverted_iff, (rootReflection M cs b).property.inv,
    (rootReflection_represents M cs b).action_formula]
  have hba : form M b.val a.val ≤ 0 := by rwa [(form_symm M).eq]
  intro i
  exact sub_nonneg.mpr ((mul_nonpos_of_nonpos_of_nonneg hba (b.property.2 i)).trans
    (a.property.2 i))

/-- The other endpoint exists even in an infinite or degenerate plane. -/
theorem exists_opposite_plane_extreme (a b p : PositiveRoot M cs) (hab : a ≠ b)
    (hp : p.val ∈ rootPlane a b)
    (hext : (∀ r : PositiveRoot M cs, r.val ∈ rootPlane a b →
        geometricSlope p ≤ geometricSlope r) ∨
      (∀ r : PositiveRoot M cs, r.val ∈ rootPlane a b →
        geometricSlope r ≤ geometricSlope p)) :
    ∃ q : PositiveRoot M cs, q.val ∈ rootPlane a b ∧ q ≠ p ∧
      (((∀ r : PositiveRoot M cs, r.val ∈ rootPlane a b →
          geometricSlope p ≤ geometricSlope r) ∧
        (∀ r : PositiveRoot M cs, r.val ∈ rootPlane a b →
          geometricSlope r ≤ geometricSlope q)) ∨
       ((∀ r : PositiveRoot M cs, r.val ∈ rootPlane a b →
          geometricSlope q ≤ geometricSlope r) ∧
        (∀ r : PositiveRoot M cs, r.val ∈ rootPlane a b →
          geometricSlope r ≤ geometricSlope p))) := by
  have hs := planeSimple_of_extreme p hp hext
  have hother : ∃ r : PositiveRoot M cs, r.val ∈ rootPlane a b ∧ r ≠ p := by
    by_cases hap : a = p
    · refine ⟨b, Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)), ?_⟩
      exact fun h => hab (hap.trans h.symm)
    · exact ⟨a, Submodule.subset_span (Set.mem_insert _ _), hap⟩
  obtain ⟨r, hrP, hrp⟩ := hother
  obtain ⟨c, hcP, hcp, hcpair⟩ := hs.exists_nonpositive_pair hrP hrp
  have hn := noninverted_ref_of_pairing_nonpos p c hcpair
  have hplane := rootPlane_eq_of_mem a b c p hab hcP hp hcp
  obtain ⟨q, hqP, hqinv, hqext⟩ := exists_plane_extreme_inverted c p hcp
  rw [hplane] at hqP hqext
  have hqp : q ≠ p := fun h => hn (h ▸ hqinv)
  refine ⟨q, hqP, hqp, ?_⟩
  rcases hext with hmin | hmax
  · refine Or.inl ⟨hmin, ?_⟩
    rcases hqext with hqmin | hqmax
    · exact False.elim (hqp (geometricSlope_injective (le_antisymm
        (hqmin p hp) (hmin q hqP))))
    · exact hqmax
  · refine Or.inr ⟨?_, hmax⟩
    rcases hqext with hqmin | hqmax
    · exact hqmin
    · exact False.elim (hqp (geometricSlope_injective (le_antisymm
        (hmax q hqP) (hqmax p hp))))

/-- Canonical angular endpoints of a plane; no Coxeter-system assertion is
built into this data. The latter will be proved from the inversion criterion. -/
structure PlaneBasis (P : Submodule ℝ (I → ℝ)) where
  left : PositiveRoot M cs
  right : PositiveRoot M cs
  distinct : left ≠ right
  plane_eq : rootPlane left right = P
  left_min : ∀ r : PositiveRoot M cs, r.val ∈ P → geometricSlope left ≤ geometricSlope r
  right_max : ∀ r : PositiveRoot M cs, r.val ∈ P → geometricSlope r ≤ geometricSlope right

theorem nonempty_planeBasis (a b : PositiveRoot M cs) (hab : a ≠ b) :
    Nonempty (PlaneBasis (M := M) (cs := cs) (rootPlane a b)) := by
  obtain ⟨p, hp, _, hext⟩ := exists_plane_extreme_inverted a b hab
  obtain ⟨q, hq, hqp, hpair⟩ := exists_opposite_plane_extreme a b p hab hp hext
  rcases hpair with ⟨hl, hr⟩ | ⟨hl, hr⟩
  · exact ⟨⟨p, q, hqp.symm, rootPlane_eq_of_mem a b p q hab hp hq hqp.symm, hl, hr⟩⟩
  · exact ⟨⟨q, p, hqp, rootPlane_eq_of_mem a b q p hab hq hp hqp, hl, hr⟩⟩

namespace PlaneBasis
variable {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)

theorem left_mem : B.left.val ∈ P := by
  apply B.plane_eq.le
  exact Submodule.subset_span (Set.mem_insert _ _)

theorem right_mem : B.right.val ∈ P := by
  apply B.plane_eq.le
  exact Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))

theorem left_simple : PlaneSimple P B.left :=
  planeSimple_of_extreme B.left B.left_mem (.inl B.left_min)

theorem right_simple : PlaneSimple P B.right :=
  planeSimple_of_extreme B.right B.right_mem (.inr B.right_max)

/-- Every positive root in the plane is in its canonical nonnegative cone. -/
theorem positive_cone (r : PositiveRoot M cs) (hr : r.val ∈ P) :
    ∃ c d : ℝ, 0 ≤ c ∧ 0 ≤ d ∧ r.val = c • B.left.val + d • B.right.val := by
  by_cases hl : r = B.left
  · exact ⟨1, 0, zero_le_one, le_refl 0, by rw [hl]; simp⟩
  by_cases hh : r = B.right
  · exact ⟨0, 1, le_refl 0, zero_le_one, by rw [hh]; simp⟩
  have hlr : geometricSlope B.left < geometricSlope r :=
    lt_of_le_of_ne (B.left_min r hr) (fun h => hl (geometricSlope_injective h).symm)
  have hrr : geometricSlope r < geometricSlope B.right :=
    lt_of_le_of_ne (B.right_max r hr) (fun h => hh (geometricSlope_injective h))
  obtain ⟨c, d, hc, hd, he⟩ := positive_combination_of_slope_between B.left B.right r
    (B.plane_eq.ge hr) hlr hrr
  exact ⟨c, d, hc.le, hd.le, he⟩

end PlaneBasis


/-- Canonical-simple reflections have no extra root pair in their own plane. -/
theorem PlaneSimple.planeWeight_eq_zero {P : Submodule ℝ (I → ℝ)}
    {a : PositiveRoot M cs} (ha : PlaneSimple P a) (x : W) :
    planeWeight x a P = 0 := by
  classical
  rw [planeWeight, Finsupp.mapDomain, Finsupp.sum_apply]
  apply Finset.sum_eq_zero
  intro b _
  change (Finsupp.single (rootPlane a b) (halfVector x a b)) P = 0
  rw [Finsupp.single_apply]
  by_cases hP : rootPlane a b = P
  · rw [ite_eq_left hP]
    simp only [halfVector, rootIndicator_apply]
    apply ite_eq_right
    intro hh
    have hbP : b.val ∈ P := hP.le
      (Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
    exact hh.1.1 ((ha.2 b hbP).mp ((rootInverted_ref_iff_flipped a b).mpr hh.1.2.1))
  · exact ite_eq_right hP

/-- The relative inversion count has the genuine simple-reflection step. -/
theorem PlaneSimple.planeLength_step {P : Submodule ℝ (I → ℝ)}
    {a b : PositiveRoot M cs} (ha : PlaneSimple P a)
    (hab : a ≠ b) (hP : rootPlane a b = P) (x : W)
    (hx : ¬ rootInverted x a) :
    planeLength (M := M) (cs := cs) P (rootRef a * x) =
      planeLength (M := M) (cs := cs) P x + 1 := by
  have hh := planeWeight_relative_degree x a b hab hx
  rw [hP, ha.planeWeight_eq_zero] at hh
  linarith

theorem PlaneSimple.planeLength_step_down {P : Submodule ℝ (I → ℝ)}
    {a b : PositiveRoot M cs} (ha : PlaneSimple P a)
    (hab : a ≠ b) (hP : rootPlane a b = P) (x : W)
    (hx : rootInverted x a) :
    planeLength (M := M) (cs := cs) P (rootRef a * x) =
      planeLength (M := M) (cs := cs) P x - 1 := by
  have hy : ¬ rootInverted (rootRef a * x) a :=
    fun h => (rootInverted_mul_self x a).mp h hx
  have hh := ha.planeLength_step hab hP (rootRef a * x) hy
  rw [← mul_assoc, (rootReflection M cs a).property.mul_self, one_mul] at hh
  linarith

/-- The usual inversion bijection, proved on the actual positive roots. -/
theorem rootInverted_inverse_action (w : W) (a : PositiveRoot M cs) :
    rootInverted w⁻¹ (positiveAction w⁻¹ a) ↔ rootInverted w a := by
  have hw : action M cs w (action M cs w⁻¹ a.val) = a.val := by
    rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl
  by_cases hi : rootInverted w a
  · apply iff_of_true ?_ hi
    unfold rootInverted
    rw [inv_inv, positiveAction_eq_of_nonpos _ _ hi, map_neg, hw]
    exact fun i => neg_nonpos.mpr (a.property.2 i)
  · apply iff_of_false ?_ hi
    rw [not_rootInverted_iff, inv_inv,
      positiveAction_eq_of_nonneg _ _ ((not_rootInverted_iff w a).mp hi), hw]
    exact a.property.2

/-- Reindexing the inversion indicator by the inverse root action. -/
theorem inversionVector_inverse (w : W) :
    inversionVector (M := M) (cs := cs) w⁻¹ =
      Finsupp.mapDomain (positiveActionEquiv w⁻¹) (inversionVector w) := by
  classical
  apply (Finsupp.ext_iff).mpr
  intro b
  obtain ⟨a, rfl⟩ := (positiveActionEquiv (M := M) (cs := cs) w⁻¹).surjective b
  rw [Finsupp.mapDomain_equiv_apply, Equiv.symm_apply_apply]
  simp only [inversionVector_apply]
  change (if rootInverted w⁻¹ (positiveAction w⁻¹ a) then 1 else 0) = _
  rw [rootInverted_inverse_action]

theorem positiveAction_mem_plane {P : Submodule ℝ (I → ℝ)}
    {w : W} (hw : w ∈ planeSubgroup M cs P) (a : PositiveRoot M cs)
    (ha : a.val ∈ P) : (positiveAction w a).val ∈ P := by
  have hp := planeSubgroup_preserves hw ha
  rcases (a.property.1.act w).sign with hs | hs
  · exact (positiveAction_eq_of_nonneg w a hs).symm ▸ hp
  · exact (positiveAction_eq_of_nonpos w a hs).symm ▸ P.neg_mem hp

theorem positiveAction_mem_plane_iff {P : Submodule ℝ (I → ℝ)}
    {w : W} (hw : w ∈ planeSubgroup M cs P) (a : PositiveRoot M cs) :
    (positiveAction w a).val ∈ P ↔ a.val ∈ P := by
  refine ⟨fun h => ?_, positiveAction_mem_plane hw a⟩
  have hh := positiveAction_mem_plane ((planeSubgroup M cs P).inv_mem hw)
    (positiveAction w a) h
  rwa [← positiveAction_mul, inv_mul_cancel, positiveAction_one] at hh

/-- Relative inversion count is invariant under inverse on the actual plane subgroup. -/
theorem planeLength_inv {P : Submodule ℝ (I → ℝ)} {w : W}
    (hw : w ∈ planeSubgroup M cs P) :
    planeLength (M := M) (cs := cs) P w⁻¹ = planeLength (M := M) (cs := cs) P w := by
  classical
  rw [planeLength, inversionVector_inverse,
    Finsupp.sum_mapDomain_index (by intros; split_ifs <;> rfl)
      (by intros; split_ifs <;> simp)]
  apply Finsupp.sum_congr
  intro a _
  change (if (positiveAction w⁻¹ a).val ∈ P then _ else _) = _
  rw [positiveAction_mem_plane_iff ((planeSubgroup M cs P).inv_mem hw)]

theorem planeLength_nonneg (P : Submodule ℝ (I → ℝ)) (w : W) :
    0 ≤ planeLength (M := M) (cs := cs) P w := by
  classical
  apply Finset.sum_nonneg
  intro a _
  simp only [inversionVector_apply]
  split_ifs <;> norm_num

namespace PlaneBasis
variable {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)

/-- A plane reflection must invert at least one of the canonical endpoints.
This uses convex positivity, not any assumed Coxeter structure on the subgroup. -/
theorem reflection_inverts_endpoint (r : PositiveRoot M cs) (hr : r.val ∈ P) :
    rootInverted (rootRef r) B.left ∨ rootInverted (rootRef r) B.right := by
  by_contra h
  push Not at h
  obtain ⟨c, d, hc, hd, he⟩ := B.positive_cone r hr
  exact (noninverted_of_positive_combination (rootRef r) B.left B.right r
    hc hd he h.1 h.2) (rootInverted_ref_self r)

end PlaneBasis


/-- The second descent in a simple conjugation of a nonsimple reflection. -/
theorem PlaneSimple.inverted_after_mul {P : Submodule ℝ (I → ℝ)}
    {a r : PositiveRoot M cs} (ha : PlaneSimple P a) (hr : r.val ∈ P)
    (hra : r ≠ a) (hi : rootInverted (rootRef r) a) :
    rootInverted (rootRef r * rootRef a) a := by
  have hn := (rootInverted_ref_iff_flipped r a).mp hi
  apply (rootInverted_mul_of_nonpos (rootRef a) r a hn).mpr
  intro hinv
  have he : partner r a = a := (ha.2 (partner r a) (partner_mem r a hr ha.1)).mp hinv
  exact hra (negative_partner_fixed r a hn he).symm

/-- The honest relative length drops by two under the chosen simple conjugation. -/
theorem PlaneSimple.planeLength_conj_drop {P : Submodule ℝ (I → ℝ)}
    {a b r : PositiveRoot M cs} (ha : PlaneSimple P a)
    (hab : a ≠ b) (hP : rootPlane a b = P) (hr : r.val ∈ P)
    (hra : r ≠ a) (hi : rootInverted (rootRef r) a) :
    planeLength (M := M) (cs := cs) P (rootRef (partner a r)) =
      planeLength (M := M) (cs := cs) P (rootRef r) - 2 := by
  have har : rootRef a ∈ planeSubgroup M cs P :=
    ((rootReflection_represents M cs a).planeSubgroup_mem_iff M cs).mpr ha.1
  have hrr : rootRef r ∈ planeSubgroup M cs P :=
    ((rootReflection_represents M cs r).planeSubgroup_mem_iff M cs).mpr hr
  have hmul := (planeSubgroup M cs P).mul_mem har hrr
  have hd := ha.planeLength_step_down hab hP (rootRef r) hi
  have hd' := ha.planeLength_step_down hab hP (rootRef r * rootRef a)
    (ha.inverted_after_mul hr hra hi)
  have hli := planeLength_inv hmul
  rw [mul_inv_rev, (rootReflection M cs r).property.inv,
    (rootReflection M cs a).property.inv] at hli
  change planeLength (M := M) (cs := cs) P
    (rootReflection M cs (positiveAction (rootRef a) r)).val = _
  rw [rootReflection_positiveAction, (rootReflection M cs a).property.inv, mul_assoc]
  linarith

namespace PlaneBasis
variable {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)

/-- The canonical endpoint reflections generate every ambient reflection in the plane. -/
theorem rootRef_mem_pairClosure (r : PositiveRoot M cs) (hr : r.val ∈ P) :
    rootRef r ∈ Subgroup.closure {rootRef B.left, rootRef B.right} := by
  classical
  generalize hn : (planeLength (M := M) (cs := cs) P (rootRef r)).toNat = n
  induction n using Nat.strong_induction_on generalizing r with
  | h n ih =>
    by_cases hl : r = B.left
    · rw [hl]; exact Subgroup.subset_closure (Set.mem_insert _ _)
    by_cases hh : r = B.right
    · rw [hh]; exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
    have step (a b : PositiveRoot M cs) (ha : PlaneSimple P a)
        (hab : a ≠ b) (hP : rootPlane a b = P) (hra : r ≠ a)
        (hgen : rootRef a ∈ Subgroup.closure {rootRef B.left, rootRef B.right})
        (hi : rootInverted (rootRef r) a) :
        rootRef r ∈ Subgroup.closure {rootRef B.left, rootRef B.right} := by
      have hp : (partner a r).val ∈ P := partner_mem a r ha.1 hr
      have hdrop := ha.planeLength_conj_drop hab hP hr hra hi
      have hless : (planeLength (M := M) (cs := cs) P (rootRef (partner a r))).toNat < n := by
        have hnonneg := planeLength_nonneg (M := M) (cs := cs) P (rootRef (partner a r))
        omega
      have hind := ih _ hless (partner a r) hp rfl
      have hlen := (Subgroup.closure {rootRef B.left, rootRef B.right}).mul_mem
        ((Subgroup.closure {rootRef B.left, rootRef B.right}).mul_mem hgen hind) hgen
      change rootRef a * (rootReflection M cs (positiveAction (rootRef a) r)).val * rootRef a ∈ _ at hlen
      rw [rootReflection_positiveAction, (rootReflection M cs a).property.inv] at hlen
      rw [← mul_assoc, ← mul_assoc, (rootReflection M cs a).property.mul_self,
        one_mul, mul_assoc, (rootReflection M cs a).property.mul_self, mul_one] at hlen
      exact hlen
    rcases B.reflection_inverts_endpoint r hr with hi | hi
    · exact step B.left B.right B.left_simple B.distinct B.plane_eq hl
        (Subgroup.subset_closure (Set.mem_insert _ _)) hi
    · exact step B.right B.left B.right_simple B.distinct.symm
        (by rw [rootPlane, Set.pair_comm]; exact B.plane_eq) hh
        (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))) hi

/-- Exact identification with the manuscript's maximal root-plane subgroup. -/
theorem pairClosure_eq_planeSubgroup :
    Subgroup.closure {rootRef B.left, rootRef B.right} = planeSubgroup M cs P := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    intro t ht
    rcases Set.mem_insert_iff.mp ht with he | he
    · rw [he]
      exact ((rootReflection_represents M cs B.left).planeSubgroup_mem_iff M cs).mpr B.left_mem
    · rw [Set.mem_singleton_iff.mp he]
      exact ((rootReflection_represents M cs B.right).planeSubgroup_mem_iff M cs).mpr B.right_mem
  · apply (Subgroup.closure_le _).mpr
    rintro t ⟨a, ha, haP⟩
    let r := positiveRoot M cs ⟨t, ha.isReflection⟩
    have hre : rootRef r = t := (rootReflection_represents M cs r).reflection_unique
      (positiveRoot_represents M cs ⟨t, ha.isReflection⟩)
    have hrP : r.val ∈ P := ((positiveRoot_represents M cs
      ⟨t, ha.isReflection⟩).planeSubgroup_mem_iff M cs).mp (Subgroup.subset_closure ⟨a, ha, haP⟩)
    rw [← hre]
    exact B.rootRef_mem_pairClosure r hrP

/-- Distinct positive roots give distinct actual reflections. -/
theorem rootRef_distinct : rootRef B.left ≠ rootRef B.right := by
  intro he
  apply B.distinct
  apply (positiveRootEquiv M cs).symm.injective
  exact Subtype.ext he

theorem rootRef_ne_one (a : PositiveRoot M cs) : rootRef a ≠ 1 := by
  intro h
  exact (not_rootInverted_one a) (h ▸ rootInverted_ref_self a)

/-- The genuine dihedral matrix attached to the canonical plane endpoints. -/
@[expose] def matrix : CoxeterMatrix Bool :=
  Dihedral.pairMatrix (rootRef B.left) (rootRef B.right)
    (rootReflection M cs B.left).property.mul_self B.rootRef_distinct

/-- A proved Coxeter system on the *actual maximal plane subgroup*. -/
@[expose] def system : CoxeterSystem B.matrix (planeSubgroup M cs P) :=
  (Dihedral.pairSystem (rootRef B.left) (rootRef B.right)
    (rootReflection M cs B.left).property.mul_self
    (rootReflection M cs B.right).property.mul_self B.rootRef_distinct
    (rootRef_ne_one B.left)
    (rootRef_ne_one B.right)).map
      (MulEquiv.subgroupCongr B.pairClosure_eq_planeSubgroup)

/-- Canonical simple positive roots, indexed by Bool just like the system. -/
@[expose] def simpleRoot (i : Bool) : PositiveRoot M cs := if i then B.right else B.left

theorem simpleRoot_mem (i : Bool) : (B.simpleRoot i).val ∈ P := by
  cases i
  · exact B.left_mem
  · exact B.right_mem

theorem simpleRoot_simple (i : Bool) : PlaneSimple P (B.simpleRoot i) := by
  cases i
  · exact B.left_simple
  · exact B.right_simple

@[simp] theorem system_simple (i : Bool) :
    (B.system.simple i : W) = rootRef (B.simpleRoot i) := by
  change ((Dihedral.pairSystem (rootRef B.left) (rootRef B.right)
    (rootReflection M cs B.left).property.mul_self
    (rootReflection M cs B.right).property.mul_self B.rootRef_distinct
    (rootRef_ne_one B.left) (rootRef_ne_one B.right)).simple i : W) = _
  rw [Dihedral.pairSystem_simple]
  cases i <;> rfl

/-- The positive simple-sign criterion for the induced plane root system. -/
theorem simple_sign {t : planeSubgroup M cs P} {a : I → ℝ}
    (ha : Represents M cs t.val a) (haP : a ∈ P) (hp : ∀ k, 0 ≤ a k) (i : Bool) :
    ((∀ k, action M cs (B.system.simple i : W) a k ≤ 0) ↔ t = B.system.simple i) ∧
    ((∀ k, 0 ≤ action M cs (B.system.simple i : W) a k) ↔ t ≠ B.system.simple i) := by
  let r : PositiveRoot M cs := ⟨a, ha.isRoot, hp⟩
  have hneg : (∀ k, action M cs (B.system.simple i : W) a k ≤ 0) ↔ t = B.system.simple i := by
    rw [B.system_simple]
    change flipped (B.simpleRoot i) r ↔ _
    rw [← rootInverted_ref_iff_flipped, (B.simpleRoot_simple i).2 r haP]
    constructor
    · intro he
      apply Subtype.ext
      rw [B.system_simple]
      exact ha.reflection_unique (he ▸ rootReflection_represents M cs r)
    · intro he
      apply Subtype.ext
      have hr : Represents M cs (rootRef (B.simpleRoot i)) a := by
        simpa only [he, B.system_simple] using ha
      exact hr.unique_positive (rootReflection_represents M cs _) hp (B.simpleRoot i).property.2
  refine ⟨hneg, ?_⟩
  constructor
  · intro h he
    exact (ha.isRoot.act (B.system.simple i : W)).not_both h (hneg.mpr he)
  · intro h
    exact (ha.isRoot.act (B.system.simple i : W)).sign.resolve_right (fun hn => h (hneg.mp hn))

/-- Signed roots for the induced system. The vectors are the original ambient
roots, and membership in the actual plane is part of the relation. -/
structure InducedSigned (p : planeSubgroup M cs P × ZMod 2) (a : I → ℝ) : Prop where
  represents : Represents M cs p.1.val a
  plane_mem : a ∈ P
  sign : (p.2 = 0 ∧ ∀ i, 0 ≤ a i) ∨ (p.2 = 1 ∧ ∀ i, a i ≤ 0)

theorem InducedSigned.simple {p : planeSubgroup M cs P × ZMod 2} {a : I → ℝ}
    (ha : InducedSigned p a) (i : Bool) :
    InducedSigned (CoxeterSupport.simpleAction B.system i p)
      (action M cs (B.system.simple i : W) a) := by
  rcases p with ⟨t,z⟩
  rw [CoxeterSupport.simpleAction_apply]
  refine ⟨?_, planeSubgroup_preserves (B.system.simple i).property ha.plane_mem, ?_⟩
  · have h := ha.represents.act (B.system.simple i : W)
    have he : (B.system.simple i : W)⁻¹ = (B.system.simple i : W) :=
      congrArg Subtype.val (B.system.inv_simple i)
    simpa only [he, Subgroup.coe_mul] using h
  · rcases ha.sign with ⟨rfl,hp⟩ | ⟨rfl,hn⟩
    · by_cases heq : t = B.system.simple i
      · exact Or.inr ⟨by simp [heq],
          (B.simple_sign ha.represents ha.plane_mem hp i).1.mpr heq⟩
      · exact Or.inl ⟨by simp [heq, ZModModule.add_self],
          (B.simple_sign ha.represents ha.plane_mem hp i).2.mpr heq⟩
    · have hp : ∀ k, 0 ≤ (-a) k := fun k => neg_nonneg.mpr (hn k)
      by_cases heq : t = B.system.simple i
      · refine Or.inl ⟨by simp [heq, ZModModule.add_self], ?_⟩
        have h := (B.simple_sign ha.represents.neg (P.neg_mem ha.plane_mem) hp i).1.mpr heq
        simpa only [map_neg, Pi.neg_apply, neg_nonpos] using h
      · refine Or.inr ⟨by simp [heq], ?_⟩
        have h := (B.simple_sign ha.represents.neg (P.neg_mem ha.plane_mem) hp i).2.mpr heq
        simpa only [map_neg, Pi.neg_apply, neg_nonneg] using h

theorem InducedSigned.act {p : planeSubgroup M cs P × ZMod 2} {a : I → ℝ}
    (ha : InducedSigned p a) (w : planeSubgroup M cs P) :
    InducedSigned (CoxeterSupport.reflectionAction B.system w p)
      (action M cs (w : W) a) := by
  obtain ⟨ω,rfl⟩ := B.system.wordProd_surjective w
  induction ω with
  | nil => simpa using ha
  | cons i ω ih =>
    simpa only [B.system.wordProd_cons, map_mul, Equiv.Perm.mul_apply,
      CoxeterSupport.reflectionAction_simple, Subgroup.coe_mul,
      LinearEquiv.mul_apply] using ih.simple B i

/-- The induced positive roots have precisely the intrinsic Coxeter inversion
signs. No change of realization or extra canonical-system assumption is used. -/
theorem inversion_iff {t : planeSubgroup M cs P} {a : I → ℝ}
    (ha : Represents M cs t.val a) (haP : a ∈ P) (hp : ∀ i, 0 ≤ a i)
    (w : planeSubgroup M cs P) :
    (∀ i, action M cs (w : W)⁻¹ a i ≤ 0) ↔ B.system.IsLeftInversion w t := by
  classical
  let : BEq (planeSubgroup M cs P) := @instBEqOfDecidableEq _ (Classical.decEq _)
  obtain ⟨ω,hω,heq⟩ := B.system.exists_isReduced w
  rw [heq]
  let c : ZMod 2 := if t ∈ B.system.leftInvSeq ω then 1 else 0
  have hrec := CoxeterSupport.wordAction_record B.system ω t c
  rw [← CoxeterSupport.reflectionAction_wordProd] at hrec
  have hrec' : CoxeterSupport.reflectionAction B.system (B.system.wordProd ω)
      ((B.system.wordProd ω)⁻¹ * t * B.system.wordProd ω, c) = (t,0) := by
    by_cases hm : t ∈ B.system.leftInvSeq ω
    · have hc : c = 1 := ite_eq_left hm
      simpa only [hc, List.count_eq_one_of_mem hω.nodup_leftInvSeq hm,
        Nat.cast_one, ZModModule.add_self] using hrec
    · have hc : c = 0 := ite_eq_right hm
      simpa only [hc, List.count_eq_zero.mpr hm, Nat.cast_zero, add_zero] using hrec
  have hinv : CoxeterSupport.reflectionAction B.system (B.system.wordProd ω)⁻¹ (t,0) =
      ((B.system.wordProd ω)⁻¹ * t * B.system.wordProd ω,c) := by
    rw [map_inv, ← hrec']
    exact Equiv.symm_apply_apply _ _
  have hs : InducedSigned (t,0) a := ⟨ha,haP,Or.inl ⟨rfl,hp⟩⟩
  have hsi := hs.act B (B.system.wordProd ω)⁻¹
  rw [hinv] at hsi
  have hcount : c = if t ∈ B.system.leftInvSeq ω then 1 else 0 := rfl
  have hmem : (∀ i, action M cs (B.system.wordProd ω : W)⁻¹ a i ≤ 0) ↔
      t ∈ B.system.leftInvSeq ω := by
    by_cases hm : t ∈ B.system.leftInvSeq ω
    · have hc1 : c=1 := by simpa [hm] using hcount
      have hh := hsi.sign
      simp only [hc1] at hh
      rcases hh with ⟨hbad,_⟩ | ⟨_,hn⟩
      · norm_num at hbad
      · exact iff_of_true hn hm
    · have hc0 : c=0 := by simpa [hm] using hcount
      have hh := hsi.sign
      simp only [hc0] at hh
      rcases hh with ⟨_,hpos⟩ | ⟨hbad,_⟩
      · exact iff_of_false (fun hn => (ha.isRoot.act _).not_both hpos hn) hm
      · norm_num at hbad
  rw [hmem]
  exact ⟨B.system.isLeftInversion_of_mem_leftInvSeq hω,
    CoxeterSupport.mem_leftInvSeq_of_inversion B.system hω⟩

/-- The intrinsic reflections are exactly the ambient reflections in the
actual maximal plane subgroup. -/
theorem reflection_iff (t : planeSubgroup M cs P) :
    B.system.IsReflection t ↔ cs.IsReflection (t : W) := by
  constructor
  · rintro ⟨w,i,he⟩
    obtain ⟨z,j,hz⟩ := (rootReflection M cs (B.simpleRoot i)).property
    refine ⟨(w : W) * z,j,?_⟩
    have he' := congrArg Subtype.val he
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, B.system_simple] at he'
    change rootRef (B.simpleRoot i) = _ at hz
    rw [he', hz]
    group
  · intro ht
    let a := positiveRoot M cs ⟨(t:W),ht⟩
    have ha := positiveRoot_represents M cs ⟨(t:W),ht⟩
    have haP : a.val ∈ P := (ha.planeSubgroup_mem_iff M cs).mp t.property
    have hinv := (B.inversion_iff ha haP a.property.2 t).mp
      ((ha.inversion_iff a.property.2 (t:W)).mpr
        ⟨ht, by
          rw [ht.mul_self, cs.length_one]
          obtain ⟨k,hk⟩ := ht.odd_length
          omega⟩)
    exact hinv.1

/-- The true ambient plane inversions are in bijection with the inversions
of the canonical induced system. -/
@[expose] def inversionEquiv (w : planeSubgroup M cs P) :
    {a : PositiveRoot M cs // a.val ∈ P ∧ rootInverted (w:W) a} ≃
      {t : planeSubgroup M cs P // B.system.IsLeftInversion w t} where
  toFun a := ⟨⟨rootRef a.val,
    ((rootReflection_represents M cs a.val).planeSubgroup_mem_iff M cs).mpr a.property.1⟩,
    (B.inversion_iff (rootReflection_represents M cs a.val) a.property.1
      a.val.property.2 w).mp a.property.2⟩
  invFun t :=
    let a := positiveRoot M cs ⟨(t.val:W),(B.reflection_iff t.val).mp t.property.1⟩
    let ha := positiveRoot_represents M cs
      ⟨(t.val:W),(B.reflection_iff t.val).mp t.property.1⟩
    let haP := (ha.planeSubgroup_mem_iff M cs).mp t.val.property
    ⟨a,haP,(B.inversion_iff ha haP a.property.2 w).mpr t.property⟩
  left_inv a := by
    apply Subtype.ext
    exact (positiveRootEquiv M cs).apply_symm_apply a.val
  right_inv t := by
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun r : {r : W // cs.IsReflection r} => r.val)
      ((positiveRootEquiv M cs).symm_apply_apply
        ⟨(t.val:W),(B.reflection_iff t.val).mp t.property.1⟩)

/-- Relative inversion count is the actual Coxeter length, completing the
length identification, not merely a rank-two presentation. -/
theorem length_eq (w : planeSubgroup M cs P) :
    planeLength (M := M) (cs := cs) P (w:W) = (B.system.length w : ℤ) := by
  classical
  let f := inversionVector (M := M) (cs := cs) (w:W)
  let F := f.support.filter (fun a => a.val ∈ P)
  have hF : (F : Set (PositiveRoot M cs)) =
      {a | a.val ∈ P ∧ rootInverted (w:W) a} := by
    ext a
    simp only [F, Finset.mem_coe, Finset.mem_filter, Finsupp.mem_support_iff,
      f, inversionVector_apply, ne_eq, ite_eq_right_iff, one_ne_zero, imp_false, not_not,
      Set.mem_ofPred_eq, and_comm]
  have hcard : F.card = B.system.length w := by
    rw [← Set.ncard_coe_finset, hF, ← Nat.card_coe_set_eq]
    change Nat.card {a : PositiveRoot M cs // a.val ∈ P ∧ rootInverted (w:W) a} = _
    rw [Nat.card_congr (B.inversionEquiv w)]
    obtain ⟨ω,hω,he⟩ := B.system.exists_isReduced w
    rw [he, Nat.card_congr (leftInversionListEquiv B.matrix B.system hω),
      ← Nat.card_congr (List.Nodup.getEquiv (B.system.leftInvSeq ω) hω.nodup_leftInvSeq),
      Nat.card_fin, B.system.length_leftInvSeq, hω.eq]
  change f.sum (fun a n => if a.val ∈ P then n else 0) = _
  rw [Finsupp.sum, ← Finset.sum_filter]
  calc
    ∑ a ∈ F, f a = ∑ _a ∈ F, (1:ℤ) := by
      apply Finset.sum_congr rfl
      intro a ha
      have hm : rootInverted (w:W) a := by
        have hm := (Finset.mem_filter.mp ha).1
        simpa only [Finsupp.mem_support_iff, f, inversionVector_apply,
          ne_eq, ite_eq_right_iff, one_ne_zero, imp_false, not_not] using hm
      simp [f,hm]
    _ = _ := by simp [hcard]

/-- Intrinsic and ambient left inversions coincide on the plane subgroup. -/
theorem leftInversion_iff (w t : planeSubgroup M cs P) :
    B.system.IsLeftInversion w t ↔ cs.IsLeftInversion (w:W) (t:W) := by
  by_cases ht : cs.IsReflection (t:W)
  · let a := positiveRoot M cs ⟨(t:W),ht⟩
    have ha := positiveRoot_represents M cs ⟨(t:W),ht⟩
    have haP := (ha.planeSubgroup_mem_iff M cs).mp t.property
    exact (B.inversion_iff ha haP a.property.2 w).symm.trans
      (ha.inversion_iff a.property.2 (w:W))
  · exact iff_of_false (fun h => ht ((B.reflection_iff t).mp h.1)) (fun h => ht h.1)

/-- The intrinsic directed dihedral graph is the actual ambient graph
restricted to the maximal plane subgroup. -/
theorem bruhatStep_iff (g h : planeSubgroup M cs P) :
    BruhatStep cs (g:W) (h:W) ↔ BruhatStep B.system g h := by
  constructor
  · rintro ⟨hlen,t,ht,he⟩
    have htP : t ∈ planeSubgroup M cs P := by
      have he' : t = (h:W) * (g:W)⁻¹ := by rw [he]; group
      rw [he']
      exact (planeSubgroup M cs P).mul_mem h.property
        ((planeSubgroup M cs P).inv_mem g.property)
    let tr : planeSubgroup M cs P := ⟨t,htP⟩
    have htr : B.system.IsReflection tr := (B.reflection_iff tr).mpr ht
    have het : h=tr*g := Subtype.ext he
    have htg : t*(h:W)=(g:W) := by rw [he, ← mul_assoc, ht.mul_self, one_mul]
    have hi := (B.leftInversion_iff h tr).mpr ⟨ht,by
      change cs.length (t*(h:W)) < cs.length (h:W)
      simpa only [htg] using hlen⟩
    have htg' : tr*h=g := by rw [het, ← mul_assoc, htr.mul_self, one_mul]
    exact ⟨by simpa only [htg'] using hi.2,tr,htr,het⟩
  · rintro ⟨hlen,t,ht,he⟩
    have het : t*h=g := by rw [he, ← mul_assoc, ht.mul_self, one_mul]
    have hi := (B.leftInversion_iff h t).mp ⟨ht,by simpa only [het] using hlen⟩
    refine ⟨?_,(t:W),(B.reflection_iff t).mp ht,congrArg Subtype.val he⟩
    simpa only [← Subgroup.coe_mul, het] using hi.2

/-- The exact canonical coset graph theorem needed by the reconstruction. -/
theorem coset_step_iff {a₀ : W}
    (hmin : ∀ z ∈ planeSubgroup M cs P, cs.length a₀ ≤ cs.length (z*a₀))
    (g h : planeSubgroup M cs P) :
    BruhatStep cs ((g:W)*a₀) ((h:W)*a₀) ↔ BruhatStep B.system g h :=
  (bruhatStep_coset_iff hmin g.property h.property).trans (B.bruhatStep_iff g h)

/-- Relative dihedral paths give actual ambient Bruhat paths in the coset. -/
theorem coset_bruhat {a₀ : W}
    (hmin : ∀ z ∈ planeSubgroup M cs P, cs.length a₀ ≤ cs.length (z*a₀))
    {g h : planeSubgroup M cs P} (hgh : BruhatLE B.system g h) :
    BruhatLE cs ((g:W)*a₀) ((h:W)*a₀) := by
  induction hgh with
  | refl => exact Relation.ReflTransGen.refl
  | @tail y z _ hyz ih =>
    exact ih.tail ((B.coset_step_iff hmin y z).mpr hyz)

/-- The source inversion-count characterization holds on every minimal
representative coset, with its actual induced length. -/
theorem coset_length_eq {a₀ : W}
    (hmin : ∀ z ∈ planeSubgroup M cs P, cs.length a₀ ≤ cs.length (z*a₀))
    (w : planeSubgroup M cs P) :
    planeLength (M := M) (cs := cs) P ((w:W)*a₀) = (B.system.length w : ℤ) := by
  classical
  rw [← B.length_eq w]
  let f := inversionVector (M := M) (cs := cs) ((w:W)*a₀)
  let g := inversionVector (M := M) (cs := cs) (w:W)
  change f.sum (fun a n => if a.val ∈ P then n else 0) =
    g.sum (fun a n => if a.val ∈ P then n else 0)
  rw [Finsupp.sum_of_support_subset f Finset.subset_union_left _ (by intro a; simp),
    Finsupp.sum_of_support_subset g Finset.subset_union_right _ (by intro a; simp)]
  apply Finset.sum_congr rfl
  intro a _
  by_cases haP : a.val ∈ P
  · simp only [ite_eq_left haP, f, g, inversionVector_apply]
    congr 1
    exact propext (root_inversion_coset_iff hmin w.property a.property.1 haP)
  · simp [haP]

end PlaneBasis

/-- Every nonsaturated reflection edge has a genuine rank-two contribution
whose induced relative edge gap is at least three. -/
theorem exists_positive_plane (x : W) (a : PositiveRoot M cs)
    (hx : ¬ rootInverted x a)
    (hlen : cs.length x + 1 < cs.length (rootRef a*x)) :
    ∃ b : PositiveRoot M cs, a ≠ b ∧ 0 < planeWeight x a (rootPlane a b) := by
  classical
  have hsum := sum_planeWeight x a hx
  have hp : 0 < (planeWeight x a).sum (fun _ n => n) := by omega
  obtain ⟨P,hP,hpos⟩ := (Finset.sum_pos_iff_of_nonneg
    (fun P _ => planeWeight_nonneg x a P)).mp hp
  obtain ⟨b,hb,hbP⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hP)
  have hb' : halfRoot x a b := by
    simpa only [Finsupp.mem_support_iff, halfVector, rootIndicator_apply,
      ne_eq, ite_eq_right_iff, one_ne_zero, imp_false, not_not] using hb
  exact ⟨b,hb'.1.1.symm,hbP ▸ hpos⟩


end
end KLInvariance.TitsSpace
end


section
namespace KLInvariance.TitsSpace
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}

/-- Every genuine ambient reflection edge of length gap greater than one
contains a full eight-edge diamond. The chosen plane comes from an actual
positive inversion contribution, avoiding the false arbitrary-plane claim. -/
theorem ambient_edge_diamond {x y : W} (hxy : BruhatStep cs x y)
    (hlen : cs.length x+1 < cs.length y) :
    ∃ a b c d : W, a ≠ b ∧ c ≠ d ∧
      BruhatStep cs x a ∧ BruhatStep cs x b ∧
      BruhatStep cs a c ∧ BruhatStep cs a d ∧
      BruhatStep cs b c ∧ BruhatStep cs b d ∧
      BruhatStep cs c y ∧ BruhatStep cs d y := by
  rcases hxy.2 with ⟨t,ht,het⟩
  let a := positiveRoot M cs ⟨t,ht⟩
  have ha := positiveRoot_represents M cs ⟨t,ht⟩
  have hta : rootRef a=t := congrArg (fun r : {r : W // cs.IsReflection r} => r.val)
    ((positiveRootEquiv M cs).symm_apply_apply ⟨t,ht⟩)
  have hx : ¬ rootInverted x a := by
    intro hi
    have h := (ha.inversion_iff a.property.2 x).mp hi
    have hh : cs.length (t*x) < cs.length x := h.2
    rw [← het] at hh
    exact (not_lt_of_gt hxy.1) hh
  have hae : rootRef a*x=y := by rw [hta]; exact het.symm
  obtain ⟨b,hab,hpos⟩ := exists_positive_plane x a hx (by rwa [hae])
  obtain ⟨B⟩ := nonempty_planeBasis a b hab
  let P := rootPlane a b
  have haP : a.val ∈ P := Submodule.subset_span (Set.mem_insert _ _)
  obtain ⟨a₀,g,hg,hgx,hmin⟩ := planeCoset_exists_minimal M cs P x
  let X : planeSubgroup M cs P := ⟨g,hg⟩
  let T : planeSubgroup M cs P := ⟨rootRef a,
    ((rootReflection_represents M cs a).planeSubgroup_mem_iff M cs).mpr haP⟩
  let Y := T*X
  have hxEq : (X:W)*a₀=x := hgx.symm
  have hyEq : (Y:W)*a₀=y := by
    change (rootRef a*g)*a₀=y
    rw [mul_assoc, ← hgx, hae]
  have hrel : BruhatStep B.system X Y := (B.coset_step_iff hmin X Y).mp
    (by simpa only [hxEq,hyEq] using hxy)
  have hLx := B.coset_length_eq hmin X
  have hLy := B.coset_length_eq hmin Y
  rw [hxEq] at hLx
  rw [hyEq] at hLy
  have hdegree := planeWeight_relative_degree x a b hab hx
  rw [hae,hLx,hLy] at hdegree
  have hlen' : B.system.length X+1 < B.system.length Y := by omega
  obtain ⟨p,q,r,s,hpq,hrs,hXp,hXq,hpr,hps,hqr,hqs,hrY,hsY⟩ :=
    Dihedral.edge_diamond B.system hrel hlen'
  have hinj : Function.Injective (fun z : planeSubgroup M cs P => (z:W)*a₀) := by
    intro p q hpq
    exact Subtype.ext (mul_right_cancel hpq)
  refine ⟨(p:W)*a₀,(q:W)*a₀,(r:W)*a₀,(s:W)*a₀,
    fun h => hpq (hinj h),fun h => hrs (hinj h),?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [hxEq] using (B.coset_step_iff hmin X p).mpr hXp
  · simpa only [hxEq] using (B.coset_step_iff hmin X q).mpr hXq
  · exact (B.coset_step_iff hmin p r).mpr hpr
  · exact (B.coset_step_iff hmin p s).mpr hps
  · exact (B.coset_step_iff hmin q r).mpr hqr
  · exact (B.coset_step_iff hmin q s).mpr hqs
  · simpa only [hyEq] using (B.coset_step_iff hmin r Y).mpr hrY
  · simpa only [hyEq] using (B.coset_step_iff hmin s Y).mpr hsY

end KLInvariance.TitsSpace
end

end OAI
