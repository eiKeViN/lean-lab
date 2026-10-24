module
public import Mathlib
public import ForMathlib.GroupTheory.Coxeter.Roots.DihedralOrder
public import ForMathlib.GroupTheory.Coxeter.Roots.PlaneTransport

public section

/-! Semantic home: ForMathlib.GroupTheory.Coxeter.Roots.LaterCount. Source spans: DihedralIntervals:20, DihedralIntervals:21, DihedralIntervals:22, DihedralIntervals:23.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.TitsSpace.PlaneBasis
open KLInvariance.Dihedral
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)
noncomputable section
local instance _root_.OAI.KLInvariance.TitsSpace.PlaneBasis.instDecidable_3 (p : Prop) : Decidable p := Classical.propDecidable p

 theorem edgeRoot_same_table {i j z : ℤ}
    (hxy : BruhatStep B.system (indexWord B.system i) (indexWord B.system j))
    (hxz : BruhatStep B.system (indexWord B.system i) (indexWord B.system z))
    (hi : B.system.length (indexWord B.system i)=i.natAbs)
    (hj : B.system.length (indexWord B.system j)=j.natAbs)
    (hz : B.system.length (indexWord B.system z)=z.natAbs)
    (gj : GoodIndex B.system j) (gz : GoodIndex B.system z) :
    geometricSlope (B.edgeRoot hxy) < geometricSlope (B.edgeRoot hxz) ↔
      SignedDihedral.Before (i+j) (i+z) := by
  have hij := (index_step_iff B.system hi hj).mp hxy
  have hiz := (index_step_iff B.system hi hz).mp hxz
  have hlabel := indexWord_label B.system hij.2
  have hlabel' := indexWord_label B.system hiz.2
  rcases maximal_or_unbounded B.system with ⟨w,hw⟩ | hu
  · rw [B.edgeRoot_finite_order w hw hxy hxz hij.2 hiz.2 hlabel hlabel']
    exact SignedDihedral.finite_before_same (by exact_mod_cast max_length_positive B.system hw)
      hij.1 hiz.1 (gj w hw) (gz w hw)
  · exact B.edgeRoot_infinite_order hu hxy hxz hij.2 hiz.2 hlabel hlabel'

 theorem edgeRoot_next_table {i j z : ℤ}
    (hxy : BruhatStep B.system (indexWord B.system i) (indexWord B.system j))
    (hyz : BruhatStep B.system (indexWord B.system j) (indexWord B.system z))
    (hi : B.system.length (indexWord B.system i)=i.natAbs)
    (hj : B.system.length (indexWord B.system j)=j.natAbs)
    (hz : B.system.length (indexWord B.system z)=z.natAbs)
    (gz : GoodIndex B.system z) :
    geometricSlope (B.edgeRoot hxy) < geometricSlope (B.edgeRoot hyz) ↔
      SignedDihedral.Before (i+j) (j+z) := by
  have hij := (index_step_iff B.system hi hj).mp hxy
  have hjz := (index_step_iff B.system hj hz).mp hyz
  have hlabel := indexWord_label B.system hij.2
  have hlabel' := indexWord_label B.system hjz.2
  rcases maximal_or_unbounded B.system with ⟨w,hw⟩ | hu
  · rw [B.edgeRoot_finite_order w hw hxy hyz hij.2 hjz.2 hlabel hlabel']
    exact SignedDihedral.finite_before_next (by exact_mod_cast max_length_positive B.system hw)
      hij.1 hjz.1 (gz w hw)
  · exact B.edgeRoot_infinite_order hu hxy hyz hij.2 hjz.2 hlabel hlabel'

 @[expose] def afterIndicator (x : planeSubgroup M cs P) (α : PositiveRoot M cs)
    (z : planeSubgroup M cs P) : ℕ :=
  if h : BruhatStep B.system x z then
    if geometricSlope α < geometricSlope (B.edgeRoot h) then 1 else 0
  else 0

 theorem afterIndicator_one (x : planeSubgroup M cs P) (α : PositiveRoot M cs) :
    B.afterIndicator x α 1=0 := by
  have hn : ¬BruhatStep B.system x 1 := by
    intro h
    have := h.1
    rw [B.system.length_one] at this
    omega
  simp only [afterIndicator,dite_eq_right hn]

 theorem afterIndicator_same {i j z : ℤ}
    (hxy : BruhatStep B.system (indexWord B.system i) (indexWord B.system j))
    (hi : B.system.length (indexWord B.system i)=i.natAbs)
    (hj : B.system.length (indexWord B.system j)=j.natAbs)
    (hz : B.system.length (indexWord B.system z)=z.natAbs)
    (gj : GoodIndex B.system j) (gz : GoodIndex B.system z) :
    B.afterIndicator (indexWord B.system i) (B.edgeRoot hxy) (indexWord B.system z) =
      SignedDihedral.arrowAfter i (i+j) z := by
  by_cases hstep : BruhatStep B.system (indexWord B.system i) (indexWord B.system z)
  · have hs := (index_step_iff B.system hi hz).mp hstep
    simp only [afterIndicator,dite_eq_left hstep,B.edgeRoot_same_table hxy hstep hi hj hz gj gz,
      SignedDihedral.arrowAfter,hs.1,hs.2,true_and]
  · have hs := (index_step_iff B.system hi hz).not.mp hstep
    rw [afterIndicator,dite_eq_right hstep,SignedDihedral.arrowAfter]
    split_ifs with h
    · exact (hs ⟨h.1,h.2.1⟩).elim
    · rfl

 theorem afterIndicator_next {i j z : ℤ}
    (hxy : BruhatStep B.system (indexWord B.system i) (indexWord B.system j))
    (hi : B.system.length (indexWord B.system i)=i.natAbs)
    (hj : B.system.length (indexWord B.system j)=j.natAbs)
    (hz : B.system.length (indexWord B.system z)=z.natAbs)
    (gz : GoodIndex B.system z) :
    B.afterIndicator (indexWord B.system j) (B.edgeRoot hxy) (indexWord B.system z) =
      SignedDihedral.arrowAfter j (i+j) z := by
  by_cases hstep : BruhatStep B.system (indexWord B.system j) (indexWord B.system z)
  · have hs := (index_step_iff B.system hj hz).mp hstep
    simp only [afterIndicator,dite_eq_left hstep,B.edgeRoot_next_table hxy hstep hi hj hz gz,
      SignedDihedral.arrowAfter,hs.1,hs.2,true_and]
  · have hs := (index_step_iff B.system hj hz).not.mp hstep
    rw [afterIndicator,dite_eq_right hstep,SignedDihedral.arrowAfter]
    split_ifs with h
    · exact (hs ⟨h.1,h.2.1⟩).elim
    · rfl

end
end KLInvariance.TitsSpace.PlaneBasis
end


section
namespace KLInvariance.TitsSpace.PlaneBasis
open KLInvariance.Dihedral
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)
noncomputable section

 @[expose] def laterCount (x : planeSubgroup M cs P) (α : PositiveRoot M cs)
    (c : planeSubgroup M cs P) : ℕ :=
  ∑ z ∈ lowerFinset B.system c, B.afterIndicator x α z

 theorem laterCount_same {i j k : ℤ}
    (hxy : BruhatStep B.system (indexWord B.system i) (indexWord B.system j))
    (hi : B.system.length (indexWord B.system i)=i.natAbs)
    (hj : B.system.length (indexWord B.system j)=j.natAbs)
    (hk : B.system.length (indexWord B.system k)=k.natAbs)
    (gj : GoodIndex B.system j) (gk : GoodIndex B.system k) :
    B.laterCount (indexWord B.system i) (B.edgeRoot hxy) (indexWord B.system k) =
      SignedDihedral.countAfter i (i+j) k := by
  rw [laterCount,sum_lower_signed B.system _ _ (B.afterIndicator_one _ _),hk,
    B.afterIndicator_same hxy hi hj hk gj gk,SignedDihedral.countAfter]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  have hnc : n<B.system.length (indexWord B.system k) := by
    rw [hk]
    exact Finset.mem_range.mp hn
  have hp := length_indexWord_nat B.system hnc.le
  have hm := length_indexWord_neg_nat B.system hnc.le
  have hp' : B.system.length (indexWord B.system (n:ℤ))=(n:ℤ).natAbs := by
    simpa only [Int.natAbs_natCast] using hp
  have hm' : B.system.length (indexWord B.system (-(n:ℤ)))=(-(n:ℤ)).natAbs := by
    simpa only [Int.natAbs_neg,Int.natAbs_natCast] using hm
  rw [B.afterIndicator_same hxy hi hj hp' gj (goodIndex_nat B.system hnc.le),
    B.afterIndicator_same hxy hi hj hm' gj (goodIndex_neg_nat B.system hnc)]

 theorem laterCount_next {i j k : ℤ}
    (hxy : BruhatStep B.system (indexWord B.system i) (indexWord B.system j))
    (hi : B.system.length (indexWord B.system i)=i.natAbs)
    (hj : B.system.length (indexWord B.system j)=j.natAbs)
    (hk : B.system.length (indexWord B.system k)=k.natAbs)
    (gk : GoodIndex B.system k) :
    B.laterCount (indexWord B.system j) (B.edgeRoot hxy) (indexWord B.system k) =
      SignedDihedral.countAfter j (i+j) k := by
  rw [laterCount,sum_lower_signed B.system _ _ (B.afterIndicator_one _ _),hk,
    B.afterIndicator_next hxy hi hj hk gk,SignedDihedral.countAfter]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  have hnc : n<B.system.length (indexWord B.system k) := by
    rw [hk]
    exact Finset.mem_range.mp hn
  have hp := length_indexWord_nat B.system hnc.le
  have hm := length_indexWord_neg_nat B.system hnc.le
  have hp' : B.system.length (indexWord B.system (n:ℤ))=(n:ℤ).natAbs := by
    simpa only [Int.natAbs_natCast] using hp
  have hm' : B.system.length (indexWord B.system (-(n:ℤ)))=(-(n:ℤ)).natAbs := by
    simpa only [Int.natAbs_neg,Int.natAbs_natCast] using hm
  rw [B.afterIndicator_next hxy hi hj hp' (goodIndex_nat B.system hnc.le),
    B.afterIndicator_next hxy hi hj hm' (goodIndex_neg_nat B.system hnc)]


 theorem laterCount_difference {x y c : planeSubgroup M cs P}
    (hxy : BruhatStep B.system x y) (hyc : BruhatLE B.system y c) :
    B.laterCount x (B.edgeRoot hxy) c = B.laterCount y (B.edgeRoot hxy) c +
      (B.system.length y-B.system.length x-1)/2 := by
  obtain ⟨i,_,hi,he⟩ := exists_good_index B.system x
  obtain ⟨j,gj,hj,hf⟩ := exists_good_index B.system y
  have hi' : i.natAbs=B.system.length x := by
    exact_mod_cast (show (i.natAbs:ℤ)=(B.system.length x:ℤ) by rw [Int.natCast_natAbs,hi])
  have hj' : j.natAbs=B.system.length y := by
    exact_mod_cast (show (j.natAbs:ℤ)=(B.system.length y:ℤ) by rw [Int.natCast_natAbs,hj])
  obtain ⟨k,gk,hk,hg,hcomp⟩ : ∃ k : ℤ, GoodIndex B.system k ∧
      k.natAbs=B.system.length c ∧ indexWord B.system k=c ∧
      (k=j ∨ |j| < |k|) := by
    by_cases h : c=y
    · subst c
      exact ⟨j,gj,hj',hf,Or.inl rfl⟩
    · obtain ⟨k,gk,hk,hg⟩ := exists_good_index B.system c
      have hlen := length_lt_of_bruhat_ne B.system hyc (Ne.symm h)
      refine ⟨k,gk,?_,hg,Or.inr ?_⟩
      · exact_mod_cast (show (k.natAbs:ℤ)=(B.system.length c:ℤ) by rw [Int.natCast_natAbs,hk])
      · rw [hj,hk]
        exact_mod_cast hlen
  have ilen : B.system.length (indexWord B.system i)=i.natAbs := by rw [he,hi']
  have jlen : B.system.length (indexWord B.system j)=j.natAbs := by rw [hf,hj']
  have klen : B.system.length (indexWord B.system k)=k.natAbs := by rw [hg,hk]
  subst x y c
  rw [B.laterCount_same hxy ilen jlen klen gj gk,
    B.laterCount_next hxy ilen jlen klen gk,ilen,jlen]
  have hs := (index_step_iff B.system ilen jlen).mp hxy
  exact SignedDihedral.countAfter_difference hs.1
    ((SignedDihedral.odd_add_abs i j).mp hs.2) hcomp

end
end KLInvariance.TitsSpace.PlaneBasis
end


section
namespace KLInvariance.TitsSpace.PlaneBasis
open KLInvariance.Dihedral
universe u v u' v'
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)
noncomputable section

 theorem afterIndicator_eq_zero {x z : planeSubgroup M cs P}
    (α : PositiveRoot M cs) (h : ¬BruhatLE B.system x z) :
    B.afterIndicator x α z = 0 := by
  have hn : ¬BruhatStep B.system x z := fun hz => h (Relation.ReflTransGen.single hz)
  simp only [afterIndicator,dite_eq_right hn]

/-- Counting only the relative interval above a lower bound does not alter
an outgoing count based at a vertex above that bound. -/
 theorem interval_laterCount {a x c : planeSubgroup M cs P}
    (hax : BruhatLE B.system a x) (α : PositiveRoot M cs) :
    (∑ᶠ z : Interval B.system a c, B.afterIndicator x α z.val) =
      B.laterCount x α c := by
  classical
  let := interval_finite B.system a c
  let : Fintype (Interval B.system a c) := Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype,laterCount]
  have hs := Finset.sum_subtype (F := (inferInstance : Fintype (Interval B.system a c)))
    ((lowerFinset B.system c).filter (fun z => BruhatLE B.system a z))
    (fun z => by simp only [Finset.mem_filter,mem_lowerFinset]; exact and_comm)
    (fun z => B.afterIndicator x α z)
  refine hs.symm.trans (Finset.sum_subset (Finset.filter_subset _ _) ?_)
  intro z hz hn
  apply B.afterIndicator_eq_zero
  intro hxz
  exact hn (Finset.mem_filter.mpr ⟨hz,bruhat_trans B.system hax hxz⟩)

 theorem edgeRoot_coset {a₀ : W}
    (hmin : ∀ z ∈ planeSubgroup M cs P, cs.length a₀ ≤ cs.length (z*a₀))
    {x y : planeSubgroup M cs P} (hxy : BruhatStep B.system x y) :
    B.edgeRoot hxy = graphRoot ((B.coset_step_iff hmin x y).mpr hxy) := by
  unfold edgeRoot graphRoot
  apply congrArg (positiveRoot M cs)
  apply Subtype.ext
  change (y:W)*(x:W)⁻¹=((y:W)*a₀)*((x:W)*a₀)⁻¹
  group

variable {I' : Type u'} [Fintype I'] {M' : CoxeterMatrix I'}
  {W' : Type v'} [Group W'] {cs' : CoxeterSystem M' W'}
  {P' : Submodule ℝ (I' → ℝ)} (B' : PlaneBasis (M := M') (cs := cs') P')

/-- A full relative interval transport carries the actual angular later-edge
count. An arbitrary graph embedding would not suffice here. -/
 theorem interval_map_count {a c : planeSubgroup M cs P}
    (hac : BruhatLE B.system a c)
    (F : Interval B.system a c → planeSubgroup M' cs' P')
    (hinj : Function.Injective F)
    (hrange : Set.range F = {z | BruhatLE B'.system (F ⟨a,bruhat_refl B.system a,hac⟩) z ∧
      BruhatLE B'.system z (F ⟨c,hac,bruhat_refl B.system c⟩)})
    (x : Interval B.system a c) (α : PositiveRoot M' cs') :
    (∑ᶠ z : Interval B.system a c, B'.afterIndicator (F x) α (F z)) =
      B'.laterCount (F x) α (F ⟨c,hac,bruhat_refl B.system c⟩) := by
  classical
  let lo : Interval B.system a c := ⟨a,bruhat_refl B.system a,hac⟩
  let hi : Interval B.system a c := ⟨c,hac,bruhat_refl B.system c⟩
  have hmem (z : Interval B.system a c) : BruhatLE B'.system (F lo) (F z) ∧
      BruhatLE B'.system (F z) (F hi) := by
    exact (Set.ext_iff.mp hrange (F z)).mp ⟨z,rfl⟩
  let f : Interval B.system a c → Interval B'.system (F lo) (F hi) :=
    fun z => ⟨F z,hmem z⟩
  have hf : Function.Bijective f := by
    constructor
    · intro z w h
      exact hinj (congrArg Subtype.val h)
    · intro z
      obtain ⟨w,hw⟩ := (Set.ext_iff.mp hrange z.val).mpr z.property
      exact ⟨w,Subtype.ext hw⟩
  let E := Equiv.ofBijective f hf
  have hs := finsum_comp_equiv E (f := fun z : Interval B'.system (F lo) (F hi) =>
    B'.afterIndicator (F x) α z.val)
  exact hs.trans (B'.interval_laterCount (hmem x).1 α)

end
end KLInvariance.TitsSpace.PlaneBasis
end


section
namespace KLInvariance.TitsSpace
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
noncomputable section

 @[expose] def ambientAfterIndicator (x : W) (α : PositiveRoot M cs) (z : W) : ℕ := by
  classical
  exact if h : BruhatStep cs x z then
    if geometricSlope α < geometricSlope (graphRoot h) then 1 else 0
  else 0

 theorem ambientAfterIndicator_of_le {x z : W} (α : PositiveRoot M cs)
    (hz : BruhatLE cs z x) : ambientAfterIndicator x α z=0 := by
  classical
  have hn : ¬BruhatStep cs x z := fun h =>
    (not_lt_of_ge (length_le_of_bruhat cs hz)) h.1
  simp only [ambientAfterIndicator,dite_eq_right hn]

 theorem ambientAfterIndicator_edge_self {x y : W} (hxy : BruhatStep cs x y) :
    ambientAfterIndicator x (graphRoot hxy) y=0 := by
  classical
  simp only [ambientAfterIndicator,dite_eq_left hxy,lt_self_iff_false,ite_false]

namespace PlaneBasis
variable {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)

 theorem ambientAfterIndicator_coset {a₀ : W}
    (hmin : ∀ z ∈ planeSubgroup M cs P, cs.length a₀ ≤ cs.length (z*a₀))
    (x z : planeSubgroup M cs P) (α : PositiveRoot M cs) :
    ambientAfterIndicator ((x:W)*a₀) α ((z:W)*a₀) = B.afterIndicator x α z := by
  classical
  by_cases h : BruhatStep B.system x z
  · have h' := (B.coset_step_iff hmin x z).mpr h
    simp only [ambientAfterIndicator,afterIndicator,dite_eq_left h,dite_eq_left h',B.edgeRoot_coset hmin h]
  · have h' : ¬BruhatStep cs ((x:W)*a₀) ((z:W)*a₀) :=
      fun hz => h ((B.coset_step_iff hmin x z).mp hz)
    simp only [ambientAfterIndicator,afterIndicator,dite_eq_right h,dite_eq_right h']

universe u' v'
variable {I' : Type u'} [Fintype I'] {M' : CoxeterMatrix I'}
  {W' : Type v'} [Group W'] {cs' : CoxeterSystem M' W'}


 theorem transported_count_difference {a₀ u b : W} {u' b' : W'}
    (hmin : ∀ z ∈ planeSubgroup M cs P, cs.length a₀ ≤ cs.length (z*a₀))
    {a c : planeSubgroup M cs P} (hac : BruhatLE B.system a c)
    (hrank : B.system.length a+2 ≤ B.system.length c)
    (hlo : BruhatLE cs u ((a:W)*a₀)) (hhi : BruhatLE cs ((c:W)*a₀) b)
    (e : Interval cs u b ≃o Interval cs' u' b')
    (y : Interval B.system a c) (hxy : BruhatStep B.system a y.val) :
    let inc := B.cosetIntervalMap hmin hlo hhi
    let lo : Interval B.system a c := ⟨a,bruhat_refl B.system a,hac⟩
    let α := graphRoot ((intervalIso_bruhatStep_iff_general cs cs' e (inc lo) (inc y)).mpr
      ((B.coset_step_iff hmin a y.val).mpr hxy))
    (∑ᶠ z : Interval B.system a c,
      ambientAfterIndicator (e (inc lo)).val α (e (inc z)).val) =
    (∑ᶠ z : Interval B.system a c,
      ambientAfterIndicator (e (inc y)).val α (e (inc z)).val) +
      (B.system.length y.val-B.system.length a-1)/2 := by
  classical
  dsimp only
  let inc := B.cosetIntervalMap hmin hlo hhi
  let lo : Interval B.system a c := ⟨a,bruhat_refl B.system a,hac⟩
  let hi : Interval B.system a c := ⟨c,hac,bruhat_refl B.system c⟩
  have hedge := (intervalIso_bruhatStep_iff_general cs cs' e (inc lo) (inc y)).mpr
    ((B.coset_step_iff hmin a y.val).mpr hxy)
  change (∑ᶠ z : Interval B.system a c,
      ambientAfterIndicator (e (inc lo)).val (graphRoot hedge) (e (inc z)).val) =
    (∑ᶠ z : Interval B.system a c,
      ambientAfterIndicator (e (inc y)).val (graphRoot hedge) (e (inc z)).val) + _
  obtain ⟨P',B',a',F,hmin',hinj,hcoord,horder,hstep,hlen,hrange⟩ :=
    B.transport_interval hmin hac hrank hlo hhi e
  have hFxy : BruhatStep B'.system (F lo) (F y) := (hstep lo y).mpr hxy
  have hFyc : BruhatLE B'.system (F y) (F hi) := (horder y hi).mpr y.property.2
  have hroot : B'.edgeRoot hFxy=graphRoot hedge := by
    rw [B'.edgeRoot_coset hmin' hFxy]
    unfold graphRoot
    apply congrArg (positiveRoot M' cs')
    apply Subtype.ext
    change ((F y:W')*a')*((F lo:W')*a')⁻¹=(e (inc y)).val*(e (inc lo)).val⁻¹
    rw [hcoord y,hcoord lo]
  have hsum (x : Interval B.system a c) :
      (∑ᶠ z : Interval B.system a c,
        ambientAfterIndicator (e (inc x)).val (graphRoot hedge) (e (inc z)).val) =
      B'.laterCount (F x) (B'.edgeRoot hFxy) (F hi) := by
    rw [← B.interval_map_count B' hac F hinj hrange x (B'.edgeRoot hFxy)]
    apply finsum_congr
    intro z
    rw [← hcoord x,← hcoord z,← hroot]
    exact B'.ambientAfterIndicator_coset hmin' (F x) (F z) _
  rw [hsum lo,hsum y,B'.laterCount_difference hFxy hFyc]
  congr 1
  have hy := hlen y
  change B'.system.length (F y)+B.system.length a =
    B'.system.length (F lo)+B.system.length y.val at hy
  omega

/-- The same scheduled count with no restriction on the relative rank. -/
 theorem transported_count_difference_all {a₀ u b : W} {u' b' : W'}
    (hmin : ∀ z ∈ planeSubgroup M cs P, cs.length a₀ ≤ cs.length (z*a₀))
    {a c : planeSubgroup M cs P} (hac : BruhatLE B.system a c)
    (hlo : BruhatLE cs u ((a:W)*a₀)) (hhi : BruhatLE cs ((c:W)*a₀) b)
    (e : Interval cs u b ≃o Interval cs' u' b')
    (y : Interval B.system a c) (hxy : BruhatStep B.system a y.val) :
    let inc := B.cosetIntervalMap hmin hlo hhi
    let lo : Interval B.system a c := ⟨a,bruhat_refl B.system a,hac⟩
    let α := graphRoot ((intervalIso_bruhatStep_iff_general cs cs' e (inc lo) (inc y)).mpr
      ((B.coset_step_iff hmin a y.val).mpr hxy))
    (∑ᶠ z : Interval B.system a c,
      ambientAfterIndicator (e (inc lo)).val α (e (inc z)).val) =
    (∑ᶠ z : Interval B.system a c,
      ambientAfterIndicator (e (inc y)).val α (e (inc z)).val) +
      (B.system.length y.val-B.system.length a-1)/2 := by
  classical
  by_cases hrank : B.system.length a+2 ≤ B.system.length c
  · exact B.transported_count_difference hmin hac hrank hlo hhi e y hxy
  let inc := B.cosetIntervalMap hmin hlo hhi
  let lo : Interval B.system a c := ⟨a,bruhat_refl B.system a,hac⟩
  have hedge := (intervalIso_bruhatStep_iff_general cs cs' e (inc lo) (inc y)).mpr
    ((B.coset_step_iff hmin a y.val).mpr hxy)
  change (∑ᶠ z : Interval B.system a c,
      ambientAfterIndicator (e (inc lo)).val (graphRoot hedge) (e (inc z)).val) =
    (∑ᶠ z : Interval B.system a c,
      ambientAfterIndicator (e (inc y)).val (graphRoot hedge) (e (inc z)).val) + _
  have hylen := hxy.1
  have hyc := length_le_of_bruhat B.system y.property.2
  have hlen : B.system.length y.val=B.system.length a+1 := by omega
  have heyc : y.val=c := by
    by_contra hn
    have hlt := length_lt_of_bruhat_ne B.system y.property.2 hn
    omega
  have hverts (z : Interval B.system a c) : z=lo ∨ z=y := by
    by_cases hz : z.val=a
    · exact Or.inl (Subtype.ext hz)
    · right
      apply Subtype.ext
      rw [heyc]
      by_contra hzc
      have hzlo := length_lt_of_bruhat_ne B.system z.property.1 (Ne.symm hz)
      have hzhi := length_lt_of_bruhat_ne B.system z.property.2 hzc
      omega
  have hzero₁ : (∑ᶠ z : Interval B.system a c,
      ambientAfterIndicator (e (inc lo)).val (graphRoot hedge) (e (inc z)).val)=0 := by
    apply finsum_eq_zero_of_forall_eq_zero
    intro z
    rcases hverts z with rfl | rfl
    · exact ambientAfterIndicator_of_le _ (bruhat_refl cs' _)
    · exact ambientAfterIndicator_edge_self hedge
  have hzero₂ : (∑ᶠ z : Interval B.system a c,
      ambientAfterIndicator (e (inc y)).val (graphRoot hedge) (e (inc z)).val)=0 := by
    apply finsum_eq_zero_of_forall_eq_zero
    intro z
    rcases hverts z with rfl | rfl
    · exact ambientAfterIndicator_of_le _ (Relation.ReflTransGen.single hedge)
    · exact ambientAfterIndicator_of_le _ (bruhat_refl cs' _)
  rw [hzero₁,hzero₂,hlen]
  omega

end PlaneBasis
end
end KLInvariance.TitsSpace
end

end OAI
