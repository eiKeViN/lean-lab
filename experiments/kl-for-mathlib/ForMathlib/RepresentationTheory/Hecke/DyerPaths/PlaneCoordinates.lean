module
public import Mathlib
public import ForMathlib.Combinatorics.DirectedPaths.Transfer
public import ForMathlib.GroupTheory.Coxeter.Roots.PlaneTransport
public import ForMathlib.RepresentationTheory.Hecke.DyerPaths.Adapted

public section

/-! Semantic home: ForMathlib.RepresentationTheory.Hecke.DyerPaths.PlaneCoordinates. Source spans: ReflectionOrders:3.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.TitsSpace.PlaneBasis
open Module SchedulePaths
open AdaptedDyer
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)
noncomputable section
@[expose] local instance _root_.OAI.KLInvariance.TitsSpace.PlaneBasis.instDecidable_2 (p : Prop) : Decidable p := Classical.propDecidable p

/-- All edges of a plane-labelled path lie in the full induced relative
interval between its endpoints, with the original ambient labels. -/
theorem path_coordinates {a₀ : W}
    (hmin : ∀ z ∈ planeSubgroup M cs P, cs.length a₀ ≤ cs.length (z*a₀))
    (g : planeSubgroup M cs P) {y : W} {p : List (AdaptedDyer.Edge cs)}
    (hp : IsPath (source cs) (target cs) ((g:W)*a₀) y p)
    (hP : ∀ e ∈ p, (rootLabel cs e).val ∈ P) :
    ∃ k : planeSubgroup M cs P, y=(k:W)*a₀ ∧ BruhatLE B.system g k ∧
      ∀ e ∈ p, ∃ l r : planeSubgroup M cs P,
        source cs e=(l:W)*a₀ ∧ target cs e=(r:W)*a₀ ∧
        BruhatLE B.system g l ∧ BruhatStep B.system l r ∧ BruhatLE B.system r k := by
  induction p generalizing g with
  | nil => exact ⟨g,hp.symm,.refl,by simp⟩
  | cons e p ih =>
    have hg : source cs e*a₀⁻¹ ∈ planeSubgroup M cs P := by
      rw [hp.1]
      simpa only [mul_assoc,mul_inv_cancel,mul_one] using g.property
    have hh := mem_coset_of_graphRoot e.property hg (hP e List.mem_cons_self)
    let h : planeSubgroup M cs P := ⟨target cs e*a₀⁻¹,hh⟩
    have heqh : target cs e=(h:W)*a₀ := by dsimp [h]; group
    have he : BruhatStep B.system g h := by
      apply (B.coset_step_iff hmin g h).mp
      rw [← hp.1,← heqh]
      exact e.property
    obtain ⟨k,hky,hk,hbody⟩ := ih h (heqh ▸ hp.2)
      (fun f hf => hP f (List.mem_cons_of_mem _ hf))
    refine ⟨k,hky,(show BruhatLE B.system g h from .single he).trans hk,?_⟩
    intro f hf
    rcases List.mem_cons.mp hf with rfl | hf
    · exact ⟨g,h,hp.1,heqh,.refl,he,hk⟩
    · obtain ⟨l,r,hl,hr,hhl,hlr,hrk⟩ := hbody f hf
      exact ⟨l,r,hl,hr,(show BruhatLE B.system g h from .single he).trans hhl,hlr,hrk⟩

@[expose] def intervalToAmbient {a₀ : W} {g k : planeSubgroup M cs P}
    (z : Interval B.system g k) : W := (z.val:W)*a₀

theorem intervalToAmbient_injective {a₀ : W} {g k : planeSubgroup M cs P} :
    Function.Injective (B.intervalToAmbient (a₀ := a₀) (g := g) (k := k)) := by
  intro x y h
  exact Subtype.ext (Subtype.ext (mul_right_cancel h))

@[expose] def edgeToAmbient {a₀ : W}
    (hmin : ∀ z ∈ planeSubgroup M cs P, cs.length a₀ ≤ cs.length (z*a₀))
    {g k : planeSubgroup M cs P} (e : BruhatGraph.Edge B.system g k) : AdaptedDyer.Edge cs :=
  ⟨(B.intervalToAmbient e.val.1, B.intervalToAmbient e.val.2),
    (B.coset_step_iff hmin e.val.1.val e.val.2.val).mpr e.property⟩

@[simp] theorem edgeToAmbient_source {a₀ : W}
    (hmin : ∀ z ∈ planeSubgroup M cs P, cs.length a₀ ≤ cs.length (z*a₀))
    {g k : planeSubgroup M cs P} (e : BruhatGraph.Edge B.system g k) :
    source cs (B.edgeToAmbient hmin e) = B.intervalToAmbient (a₀ := a₀) (BruhatGraph.source B.system g k e) := rfl

@[simp] theorem edgeToAmbient_target {a₀ : W}
    (hmin : ∀ z ∈ planeSubgroup M cs P, cs.length a₀ ≤ cs.length (z*a₀))
    {g k : planeSubgroup M cs P} (e : BruhatGraph.Edge B.system g k) :
    target cs (B.edgeToAmbient hmin e) = B.intervalToAmbient (a₀ := a₀) (BruhatGraph.target B.system g k e) := rfl

theorem edgeToAmbient_injective {a₀ : W}
    (hmin : ∀ z ∈ planeSubgroup M cs P, cs.length a₀ ≤ cs.length (z*a₀))
    {g k : planeSubgroup M cs P} :
    Function.Injective (B.edgeToAmbient hmin (g := g) (k := k)) := by
  intro e f h
  have hh := congrArg Subtype.val h
  apply Subtype.ext
  exact Prod.ext (B.intervalToAmbient_injective (congrArg Prod.fst hh))
    (B.intervalToAmbient_injective (congrArg Prod.snd hh))

@[simp] theorem edgeToAmbient_root {a₀ : W}
    (hmin : ∀ z ∈ planeSubgroup M cs P, cs.length a₀ ≤ cs.length (z*a₀))
    {g k : planeSubgroup M cs P} (e : BruhatGraph.Edge B.system g k) :
    rootLabel cs (B.edgeToAmbient hmin e) = B.edgeRoot e.property := by
  apply (positiveRootEquiv M cs).symm.injective
  apply Subtype.ext
  change rootRef (rootLabel cs (B.edgeToAmbient hmin e)) = rootRef (B.edgeRoot e.property)
  rw [rootRef_rootLabel]
  have hr : rootRef (B.edgeRoot e.property) = (e.val.2.val:W)*(e.val.1.val:W)⁻¹ :=
    (rootReflection_represents M cs _).reflection_unique
      (graphRoot_represents ((B.bruhatStep_iff _ _).mpr e.property))
  rw [hr]
  change ((e.val.2.val:W)*a₀)*((e.val.1.val:W)*a₀)⁻¹ = _
  group

/-- Edge-by-edge lifting of every plane path into the full relative interval.
It is obtained from actual path connectivity, not from ambient comparability
alone (which would not suffice). -/
theorem path_edges_lift {a₀ : W}
    (hmin : ∀ z ∈ planeSubgroup M cs P, cs.length a₀ ≤ cs.length (z*a₀))
    {g k : planeSubgroup M cs P} {p : List (AdaptedDyer.Edge cs)}
    (hp : IsPath (source cs) (target cs) ((g:W)*a₀) ((k:W)*a₀) p)
    (hP : ∀ e ∈ p, (rootLabel cs e).val ∈ P) :
    ∀ e ∈ p, ∃ e' : BruhatGraph.Edge B.system g k, B.edgeToAmbient hmin e'=e := by
  obtain ⟨k',he,_,hbody⟩ := B.path_coordinates hmin g hp hP
  have hk : k'=k := Subtype.ext (mul_right_cancel he.symm)
  subst k'
  intro e he
  obtain ⟨l,r,hl,hr,hgl,hlr,hrk⟩ := hbody e he
  let vl : Interval B.system g k := ⟨l,hgl,(show BruhatLE B.system l r from .single hlr).trans hrk⟩
  let vr : Interval B.system g k := ⟨r,hgl.trans (.single hlr),hrk⟩
  refine ⟨⟨(vl,vr),hlr⟩,?_⟩
  apply Subtype.ext
  exact Prod.ext hl.symm hr.symm


include B in
/-- Reversal of a complete angular block of genuine ambient edges preserves
all its endpoint entries. Fullness is with respect to the actual root plane,
not to a rank-two subgroup chosen merely to contain two arbitrary reflections. -/
theorem dispatch_plane_reverse {R : Type*} [Semiring R] (T : R) (b : W)
    (p : List (AdaptedDyer.Edge cs)) (hnd : p.Nodup)
    (hfull : ∀ e, e ∈ p ↔ (rootLabel cs e).val ∈ P ∧ BruhatLE cs (target cs e) b)
    (hs : p.Pairwise (fun e f => geometricSlope (rootLabel cs f) ≤ geometricSlope (rootLabel cs e)))
    (x y : W) (hy : BruhatLE cs y b) :
    dispatch (source cs) (target cs) T (fun z => if z=y then 1 else 0) p x =
      dispatch (source cs) (target cs) T (fun z => if z=y then 1 else 0) p.reverse x := by
  obtain ⟨a₀,g,hg,hx,hmin⟩ := planeCoset_exists_minimal M cs P x
  let g' : planeSubgroup M cs P := ⟨g,hg⟩
  have hx' : x=(g':W)*a₀ := hx
  let L : AdaptedDyer.Edge cs → ℝ := fun e => geometricSlope (rootLabel cs e)
  have hties : ∀ e f, L e=L f → target cs e ≠ source cs f := by
    intro e f he
    exact fun hj => rootLabel_ne_of_join cs e f hj (geometricSlope_injective he)
  by_cases hex : ∃ r : List (AdaptedDyer.Edge cs),
      IsPath (source cs) (target cs) x y r ∧ ∀ e ∈ r, (rootLabel cs e).val ∈ P
  · obtain ⟨r,hr,hrP⟩ := hex
    obtain ⟨k,hyk,hgk,_⟩ := B.path_coordinates hmin g' (hx' ▸ hr) hrP
    let lo : Interval B.system g' k := ⟨g',.refl,hgk⟩
    let hi : Interval B.system g' k := ⟨k,hgk,.refl⟩
    let j := B.intervalToAmbient (a₀ := a₀) (g := g') (k := k)
    let J := B.edgeToAmbient hmin (g := g') (k := k)
    have hjlo : j lo=x := hx'.symm
    have hjhi : j hi=y := hyk.symm
    let : Fintype (BruhatGraph.Edge B.system g' k) := Fintype.ofFinite _
    let q : List (BruhatGraph.Edge B.system g' k) :=
      Finset.univ.toList.mergeSort (fun e f => B.intervalEdgeSlope g' k f ≤ B.intervalEdgeSlope g' k e)
    have hqnd : q.Nodup := (List.mergeSort_perm _ _).nodup_iff.mpr (Finset.nodup_toList _)
    have hqfull : ∀ e, e ∈ q := by intro e; simp [q]
    have hqs : q.Pairwise (fun e f => B.intervalEdgeSlope g' k f ≤ B.intervalEdgeSlope g' k e) :=
      List.pairwise_mergeSort' _ _
    have hJroot (e : BruhatGraph.Edge B.system g' k) : L (J e)=B.intervalEdgeSlope g' k e := by
      dsimp [L,J,intervalEdgeSlope]
      rw [B.edgeToAmbient_root]
    have hJmem (e : BruhatGraph.Edge B.system g' k) : J e ∈ p := by
      apply (hfull _).mpr
      constructor
      · dsimp [J]
        rw [B.edgeToAmbient_root]
        exact B.edgeRoot_plane e.property
      · have ht : BruhatLE cs ((e.val.2.val:W)*a₀) ((k:W)*a₀) :=
          B.coset_bruhat hmin e.val.2.property.2
        exact ht.trans (hyk ▸ hy)
    have hlift (s : List (AdaptedDyer.Edge cs))
        (hst : ∀ e ∈ s, e ∈ p)
        (hp : IsPath (source cs) (target cs) (j lo) (j hi) s) :
        ∀ e ∈ s, ∃ e' : BruhatGraph.Edge B.system g' k, J e'=e :=
      B.path_edges_lift hmin hp (fun e he => ((hfull e).mp (hst e he)).1)
    have hleft := dispatch_entry_graph_embedding (source cs) (target cs)
      (BruhatGraph.source B.system g' k) (BruhatGraph.target B.system g' k)
      T L hties j (B.intervalToAmbient_injective) J (B.edgeToAmbient_injective hmin)
      (B.edgeToAmbient_source hmin) (B.edgeToAmbient_target hmin)
      p q hnd hqnd hs (by simpa only [hJroot] using hqs) hqfull hJmem lo hi (by
        intro s hsp
        obtain ⟨hsub,hpath⟩ := (mem_subpaths _ _ _ _ _ _).mp hsp
        exact hlift s (fun e he => hsub.subset he) hpath)
    have hright := dispatch_entry_graph_embedding (source cs) (target cs)
      (BruhatGraph.source B.system g' k) (BruhatGraph.target B.system g' k)
      T (fun e => -L e) (fun e f he => hties e f (neg_injective he))
      j (B.intervalToAmbient_injective) J (B.edgeToAmbient_injective hmin)
      (B.edgeToAmbient_source hmin) (B.edgeToAmbient_target hmin)
      p.reverse q.reverse (List.nodup_reverse.mpr hnd) (List.nodup_reverse.mpr hqnd)
      (by rw [List.pairwise_reverse]; exact hs.imp (fun he => neg_le_neg he))
      (by rw [List.pairwise_reverse]; exact hqs.imp (fun he => by simpa only [hJroot] using neg_le_neg he))
      (fun e => List.mem_reverse.mpr (hqfull e))
      (fun e => List.mem_reverse.mpr (hJmem e)) lo hi (by
        intro s hsp
        obtain ⟨hsub,hpath⟩ := (mem_subpaths _ _ _ _ _ _).mp hsp
        exact hlift s (fun e he => List.mem_reverse.mp (hsub.subset he)) hpath)
    rw [hjlo,hjhi] at hleft hright
    rw [hleft,hright]
    exact B.dispatch_reverse_endpoints hgk q hqnd hqfull hqs T
  · have hzero (q : List (AdaptedDyer.Edge cs))
        (hqp : ∀ e ∈ q, e ∈ p) : subpaths (source cs) (target cs) q x y = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro r hr
      obtain ⟨hsub,hpath⟩ := (mem_subpaths _ _ _ _ _ _).mp hr
      exact hex ⟨r,hpath,fun e he => ((hfull e).mp (hqp e (hsub.subset he))).1⟩
    rw [dispatch_eq_subpaths_sum _ _ _ _ hnd,
      dispatch_eq_subpaths_sum _ _ _ _ (List.nodup_reverse.mpr hnd),
      hzero p (fun _ he => he),hzero p.reverse (fun _ he => List.mem_reverse.mp he)]

end
end KLInvariance.TitsSpace.PlaneBasis
end

end OAI
