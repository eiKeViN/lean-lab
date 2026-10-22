import Mathlib
import ForMathlib.GroupTheory.Coxeter.Parabolic.InversionList
import ForMathlib.GroupTheory.Coxeter.Roots.PlaneBasis

/-! Semantic home: ForMathlib.GroupTheory.Coxeter.Bruhat.Diamonds. Source spans: Decomposition:8, DyerPaths:4, DyerPaths:9.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance
variable {I W : Type*} [Fintype I] [Group W] {M : CoxeterMatrix I}

/-- General unlabelled Bruhat graph reconstruction completeness, for genuine
finite-rank Coxeter systems and arbitrary bottoms and interval ranks. -/
theorem diamondEdges_of_bruhatStep (cs : CoxeterSystem M W)
    {u b : W} {x y : Interval cs u b} (hxy : BruhatStep cs x.val y.val) :
    DiamondEdges x y := by
  suffices ∀ n : ℕ, ∀ x y : Interval cs u b,
      cs.length y.val-cs.length x.val=n → BruhatStep cs x.val y.val →
      DiamondEdges x y by
    exact this _ x y rfl hxy
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro x y hn hxy
    by_cases he : cs.length y.val=cs.length x.val+1
    · exact DiamondEdges.cover (interval_covBy_of_length_succ cs
        (Relation.ReflTransGen.single hxy) he)
    · have hn' : cs.length x.val+1 < cs.length y.val := by have := hxy.1; omega
      obtain ⟨a,bm,c,d,hab,hcd,hxa,hxb,hac,had,hbc,hbd,hcy,hdy⟩ :=
        TitsSpace.ambient_edge_diamond hxy hn'
      have leOf {p q : W} (h : BruhatStep cs p q) : BruhatLE cs p q :=
        Relation.ReflTransGen.single h
      let A : Interval cs u b := ⟨a,bruhat_trans cs x.property.1 (leOf hxa),
        bruhat_trans cs (leOf hac) (bruhat_trans cs (leOf hcy) y.property.2)⟩
      let B : Interval cs u b := ⟨bm,bruhat_trans cs x.property.1 (leOf hxb),
        bruhat_trans cs (leOf hbc) (bruhat_trans cs (leOf hcy) y.property.2)⟩
      let C : Interval cs u b := ⟨c,
        bruhat_trans cs x.property.1 (bruhat_trans cs (leOf hxa) (leOf hac)),
        bruhat_trans cs (leOf hcy) y.property.2⟩
      let D : Interval cs u b := ⟨d,
        bruhat_trans cs x.property.1 (bruhat_trans cs (leOf hxa) (leOf had)),
        bruhat_trans cs (leOf hdy) y.property.2⟩
      have hsmall {p q : Interval cs u b} (hpq : BruhatStep cs p.val q.val)
          (hp : cs.length x.val ≤ cs.length p.val)
          (hq : cs.length q.val ≤ cs.length y.val)
          (hs : cs.length x.val < cs.length p.val ∨ cs.length q.val < cs.length y.val) :
          DiamondEdges p q := by
        exact ih _ (by omega) p q rfl hpq
      have h₁ := hxa.1
      have h₂ := hxb.1
      have h₃ := hac.1
      have h₄ := had.1
      have h₅ := hbc.1
      have h₆ := hbd.1
      have h₇ := hcy.1
      have h₈ := hdy.1
      refine DiamondEdges.diamond
        (hsmall (p := x) (q := A) hxa ?_ ?_ ?_)
        (hsmall (p := x) (q := B) hxb ?_ ?_ ?_)
        (hsmall (p := A) (q := C) hac ?_ ?_ ?_)
        (hsmall (p := A) (q := D) had ?_ ?_ ?_)
        (hsmall (p := B) (q := C) hbc ?_ ?_ ?_)
        (hsmall (p := B) (q := D) hbd ?_ ?_ ?_)
        (hsmall (p := C) (q := y) hcy ?_ ?_ ?_)
        (hsmall (p := D) (q := y) hdy ?_ ?_ ?_)
        (fun h => hab (congrArg Subtype.val h))
        (fun h => hcd (congrArg Subtype.val h))
      all_goals first | omega | (dsimp only [A,B,C,D]; omega)

/-- An abstract interval order isomorphism determines its actual directed
reflection edges. No root labels, generators or geometric data are supplied to
that isomorphism. This proves the finite-rank graph input of the source main. -/
theorem intervalIso_bruhatStep_iff {I' W' : Type*} [Fintype I'] [Group W']
    {M' : CoxeterMatrix I'} (cs : CoxeterSystem M W) (cs' : CoxeterSystem M' W')
    {u b : W} {u' b' : W'} (e : Interval cs u b ≃o Interval cs' u' b')
    (x y : Interval cs u b) :
    BruhatStep cs' (e x).val (e y).val ↔ BruhatStep cs x.val y.val := by
  constructor
  · intro h
    exact diamondEdges_bruhatStep cs ((DiamondEdges.map_iff e).mp
      (diamondEdges_of_bruhatStep cs' h))
  · intro h
    exact diamondEdges_bruhatStep cs' ((diamondEdges_of_bruhatStep cs h).map e)

end KLInvariance
end


section
namespace KLInvariance
universe u v u' v'
variable {I : Type u} {W : Type v} [Group W] {M : CoxeterMatrix I}

/-- The graph reconstruction input in its source scope: the Coxeter system
can have infinitely many generators. The interval determines every reflection
edge without being supplied the reflection labels. -/
theorem diamondEdges_of_bruhatStep_general (cs : CoxeterSystem M W)
    {u b : W} {x y : Interval cs u b} (hxy : BruhatStep cs x.val y.val) :
    DiamondEdges x y := by
  classical
  obtain ⟨J, hJ, hwords⟩ := lower_ideal_finite_generator_support cs b
  let : Fintype J := hJ.fintype
  obtain ⟨ω, hω, hprod⟩ := hwords b (bruhat_refl cs b)
  obtain ⟨ν, rfl⟩ := StandardParabolic.lift_word J hω
  let bb := (StandardParabolic.system (M := M) J).wordProd ν
  have hb : StandardParabolic.inclusion cs J bb = b :=
    (StandardParabolic.inclusion_word cs J ν).trans hprod
  have hub : BruhatLE cs u b := (bruhat_trans cs x.property.1 x.property.2)
  obtain ⟨ub, hu⟩ := StandardParabolic.lower_range cs J bb (hb ▸ hub)
  subst u
  clear hprod
  subst b
  let e := StandardParabolic.intervalIso cs J ub bb
  let xx := e.symm x
  let yy := e.symm y
  have hx : StandardParabolic.inclusion cs J xx.val = x.val :=
    congrArg Subtype.val (e.apply_symm_apply x)
  have hy : StandardParabolic.inclusion cs J yy.val = y.val :=
    congrArg Subtype.val (e.apply_symm_apply y)
  have hh : BruhatStep (StandardParabolic.system (M := M) J) xx.val yy.val := by
    apply (StandardParabolic.bruhatStep_inclusion_iff cs J _ _).mp
    rwa [hx, hy]
  have hg := (diamondEdges_of_bruhatStep (StandardParabolic.system (M := M) J) hh).map e
  simpa only [xx, yy, e.apply_symm_apply] using hg

theorem diamondEdges_bruhatStep_general (cs : CoxeterSystem M W)
    {u b : W} {x y : Interval cs u b} (hxy : DiamondEdges x y) :
    BruhatStep cs x.val y.val := by
  classical
  obtain ⟨J, hJ, hwords⟩ := lower_ideal_finite_generator_support cs b
  let : Fintype J := hJ.fintype
  obtain ⟨ω, hω, hprod⟩ := hwords b (bruhat_refl cs b)
  obtain ⟨ν, rfl⟩ := StandardParabolic.lift_word J hω
  let bb := (StandardParabolic.system (M := M) J).wordProd ν
  have hb : StandardParabolic.inclusion cs J bb = b :=
    (StandardParabolic.inclusion_word cs J ν).trans hprod
  have hub : BruhatLE cs u b := (bruhat_trans cs x.property.1 x.property.2)
  obtain ⟨ub, hu⟩ := StandardParabolic.lower_range cs J bb (hb ▸ hub)
  subst u
  clear hprod
  subst b
  let e := StandardParabolic.intervalIso cs J ub bb
  let xx := e.symm x
  let yy := e.symm y
  have hx : StandardParabolic.inclusion cs J xx.val = x.val :=
    congrArg Subtype.val (e.apply_symm_apply x)
  have hy : StandardParabolic.inclusion cs J yy.val = y.val :=
    congrArg Subtype.val (e.apply_symm_apply y)
  have hh : DiamondEdges xx yy := hxy.map e.symm
  have hg := diamondEdges_bruhatStep (StandardParabolic.system (M := M) J) hh
  have hs := (StandardParabolic.bruhatStep_inclusion_iff cs J xx.val yy.val).mpr hg
  rwa [hx, hy] at hs

/-- Exact unlabelled directed graph invariance, also for arbitrary infinite
Coxeter systems. This is not yet KL polynomial invariance. -/
theorem intervalIso_bruhatStep_iff_general
    {I' : Type u'} {W' : Type v'} [Group W'] {M' : CoxeterMatrix I'}
    (cs : CoxeterSystem M W) (cs' : CoxeterSystem M' W')
    {u b : W} {u' b' : W'} (e : Interval cs u b ≃o Interval cs' u' b')
    (x y : Interval cs u b) :
    BruhatStep cs' (e x).val (e y).val ↔ BruhatStep cs x.val y.val := by
  constructor
  · intro h
    exact diamondEdges_bruhatStep_general cs ((DiamondEdges.map_iff e).mp
      (diamondEdges_of_bruhatStep_general cs' h))
  · intro h
    exact diamondEdges_bruhatStep_general cs' ((diamondEdges_of_bruhatStep_general cs h).map e)

end KLInvariance
end


section
namespace KLInvariance
universe u v u' v'
variable {I : Type u} {W : Type v} [Group W] {M : CoxeterMatrix I}
  {I' : Type u'} {W' : Type v'} [Group W'] {M' : CoxeterMatrix I'}
  {cs : CoxeterSystem M W} {cs' : CoxeterSystem M' W'}
  {u b : W} {u' b' : W'}

/-- An interval graph isomorphism preserves the exact two-edge intermediate
set, including ambient intermediates not specified as interval data. -/
theorem intervalIso_twoStep_iff
    (e : Interval cs u b ≃o Interval cs' u' b') (x y a c : Interval cs u b)
    (hpaths : ∀ z : W, (BruhatStep cs x.val z ∧ BruhatStep cs z y.val) ↔
      z=a.val ∨ z=c.val) (z : W') :
    (BruhatStep cs' (e x).val z ∧ BruhatStep cs' z (e y).val) ↔
      z=(e a).val ∨ z=(e c).val := by
  constructor
  · intro hz
    let z' : Interval cs' u' b' := ⟨z,
      bruhat_trans cs' (e x).property.1 (Relation.ReflTransGen.single hz.1),
      bruhat_trans cs' (Relation.ReflTransGen.single hz.2) (e y).property.2⟩
    have hz₁ : BruhatStep cs x.val (e.symm z').val := by
      apply (intervalIso_bruhatStep_iff_general cs cs' e x (e.symm z')).mp
      simpa only [e.apply_symm_apply] using hz.1
    have hz₂ : BruhatStep cs (e.symm z').val y.val := by
      apply (intervalIso_bruhatStep_iff_general cs cs' e (e.symm z') y).mp
      simpa only [e.apply_symm_apply] using hz.2
    rcases (hpaths (e.symm z').val).mp ⟨hz₁,hz₂⟩ with ha | hc
    · have he : e.symm z'=a := Subtype.ext ha
      have he' : z'=e a := by rw [← he,e.apply_symm_apply]
      exact Or.inl (congrArg Subtype.val he')
    · have he : e.symm z'=c := Subtype.ext hc
      have he' : z'=e c := by rw [← he,e.apply_symm_apply]
      exact Or.inr (congrArg Subtype.val he')
  · rintro (rfl | rfl)
    · have h := (hpaths a.val).mpr (Or.inl rfl)
      exact ⟨(intervalIso_bruhatStep_iff_general cs cs' e x a).mpr h.1,
        (intervalIso_bruhatStep_iff_general cs cs' e a y).mpr h.2⟩
    · have h := (hpaths c.val).mpr (Or.inr rfl)
      exact ⟨(intervalIso_bruhatStep_iff_general cs cs' e x c).mpr h.1,
        (intervalIso_bruhatStep_iff_general cs cs' e c y).mpr h.2⟩

end KLInvariance
end

end OAI
