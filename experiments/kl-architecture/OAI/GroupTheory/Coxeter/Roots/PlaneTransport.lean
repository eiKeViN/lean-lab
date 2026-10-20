import Mathlib
import OAI.GroupTheory.Coxeter.Bruhat.Diamonds
import OAI.GroupTheory.Coxeter.Dihedral.IntervalTransport

/-! Semantic home: OAI.GroupTheory.Coxeter.Roots.PlaneTransport. Source spans: DyerPaths:5, DyerPaths:7, DyerPaths:10, DyerPaths:11.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.TitsSpace
open Module
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
noncomputable section

namespace PlaneBasis
variable {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)

theorem graphRoot_mem {a₀ : W} {g h : planeSubgroup M cs P}
    (he : BruhatStep cs ((g : W) * a₀) ((h : W) * a₀)) :
    (graphRoot he).val ∈ P := by
  exact reflection_between_coset_mem M cs (a := a₀) g.property h.property (by group)
    (graphRoot_represents he)

include B

/-- The two labels on a composable coset path span the whole actual plane. -/
theorem graphRoot_path_plane {a₀ : W} {g h k : planeSubgroup M cs P}
    (he : BruhatStep cs ((g : W) * a₀) ((h : W) * a₀))
    (hf : BruhatStep cs ((h : W) * a₀) ((k : W) * a₀)) :
    rootPlane (graphRoot he) (graphRoot hf) = P := by
  exact (rootPlane_eq_of_mem B.left B.right (graphRoot he) (graphRoot hf)
    B.distinct (B.plane_eq.ge (graphRoot_mem he)) (B.plane_eq.ge (graphRoot_mem hf))
    (graphRoot_ne_of_path he hf)).trans B.plane_eq


theorem twoStep_mem_coset {a₀ : W} {g h k : planeSubgroup M cs P}
    (he : BruhatStep cs ((g : W) * a₀) ((h : W) * a₀))
    (hf : BruhatStep cs ((h : W) * a₀) ((k : W) * a₀))
    {z : W} (hez : BruhatStep cs ((g : W) * a₀) z)
    (hzf : BruhatStep cs z ((k : W) * a₀)) :
    z * a₀⁻¹ ∈ planeSubgroup M cs P := by
  by_cases hz : (h : W) * a₀ = z
  · rw [← hz, mul_inv_cancel_right]
    exact h.property
  have hplane := graphRoot_square_plane he hez hf hzf hz
  have hroot : (graphRoot hez).val ∈ P := by
    apply (hplane.symm.trans (B.graphRoot_path_plane he hf)).le
    exact Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have href : z * ((g : W) * a₀)⁻¹ ∈ planeSubgroup M cs P :=
    (Represents.planeSubgroup_mem_iff M cs (graphRoot_represents hez)).mpr hroot
  convert (planeSubgroup M cs P).mul_mem href g.property using 1; group

/-- A relative rank-two interval has exactly its two ambient two-edge paths,
with no assumption that the two ambient and relative orders coincide. -/
theorem ambient_two_step_rank_two {a₀ : W}
    (hmin : ∀ z ∈ planeSubgroup M cs P, cs.length a₀ ≤ cs.length (z * a₀))
    {g k : planeSubgroup M cs P} (hlen : B.system.length k = B.system.length g + 2) :
    ∃ a b : W, a ≠ b ∧ ∀ z : W,
      (BruhatStep cs ((g : W) * a₀) z ∧ BruhatStep cs z ((k : W) * a₀)) ↔
        z = a ∨ z = b := by
  obtain ⟨a,b,hab,hpaths⟩ := Dihedral.two_step_rank_two B.system hlen
  have ha := (hpaths a).mpr (Or.inl rfl)
  have he := (B.coset_step_iff hmin g a).mpr ha.1
  have hf := (B.coset_step_iff hmin a k).mpr ha.2
  refine ⟨(a : W)*a₀,(b : W)*a₀,?_,fun z => ?_⟩
  · intro heq
    exact hab (Subtype.ext (mul_right_cancel heq))
  constructor
  · intro hz
    let z' : planeSubgroup M cs P := ⟨z*a₀⁻¹,B.twoStep_mem_coset he hf hz.1 hz.2⟩
    have hz' : (z' : W)*a₀=z := by dsimp [z']; group
    have hp : BruhatStep B.system g z' ∧ BruhatStep B.system z' k := by
      constructor
      · exact (B.coset_step_iff hmin g z').mp (hz' ▸ hz.1)
      · exact (B.coset_step_iff hmin z' k).mp (hz' ▸ hz.2)
    rcases (hpaths z').mp hp with hza | hzb
    · exact Or.inl (hz'.symm.trans (congrArg (fun q : planeSubgroup M cs P => (q:W)*a₀) hza))
    · exact Or.inr (hz'.symm.trans (congrArg (fun q : planeSubgroup M cs P => (q:W)*a₀) hzb))
  · rintro (rfl | rfl)
    · exact ⟨he,hf⟩
    · have hb := (hpaths b).mpr (Or.inr rfl)
      exact ⟨(B.coset_step_iff hmin g b).mpr hb.1,
        (B.coset_step_iff hmin b k).mpr hb.2⟩

end PlaneBasis
end
end KLInvariance.TitsSpace
end


section
namespace KLInvariance.TitsSpace
open Module
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
noncomputable section

theorem graphRoot_mem_of_coset {P : Submodule ℝ (I → ℝ)} {a₀ x y : W}
    (h : BruhatStep cs x y) (hx : x*a₀⁻¹ ∈ planeSubgroup M cs P)
    (hy : y*a₀⁻¹ ∈ planeSubgroup M cs P) : (graphRoot h).val ∈ P := by
  apply (Represents.planeSubgroup_mem_iff M cs (graphRoot_represents h)).mp
  convert (planeSubgroup M cs P).mul_mem hy ((planeSubgroup M cs P).inv_mem hx) using 1
  group

theorem mem_coset_of_graphRoot {P : Submodule ℝ (I → ℝ)} {a₀ x y : W}
    (h : BruhatStep cs x y) (hx : x*a₀⁻¹ ∈ planeSubgroup M cs P)
    (hy : (graphRoot h).val ∈ P) : y*a₀⁻¹ ∈ planeSubgroup M cs P := by
  have hm := (Represents.planeSubgroup_mem_iff M cs (graphRoot_represents h)).mpr hy
  convert (planeSubgroup M cs P).mul_mem hm hx using 1
  group

variable {D : Type*} [Group D] {N : CoxeterMatrix Bool} (ds : CoxeterSystem N D)
  {l r : D}

/-- The image of a full relative dihedral interval lies in one maximal plane
coset. This is derived just from the directed graph and distinct vertices. -/
theorem dihedral_image_in_plane
    (f : Interval ds l r → W) (hinj : Function.Injective f)
    (hgraph : ∀ a b : Interval ds l r,
      BruhatStep ds a.val b.val → BruhatStep cs (f a) (f b))
    (hlr : BruhatLE ds l r) (hrank : ds.length l + 2 ≤ ds.length r) :
    ∃ a b : PositiveRoot M cs, a ≠ b ∧
      ∀ z : Interval ds l r,
        f z * (f ⟨l,bruhat_refl ds l,hlr⟩)⁻¹ ∈ planeSubgroup M cs (rootPlane a b) := by
  let lo : Interval ds l r := ⟨l,bruhat_refl ds l,hlr⟩
  let hi : Interval ds l r := ⟨r,hlr,bruhat_refl ds r⟩
  obtain ⟨a,b,hab,ha,hb⟩ := Dihedral.two_interval_elements_length ds lo hi
    (n := ds.length l+1) (by dsimp [lo]; omega) (by dsimp [hi]; omega)
  have cover : ∀ p q : Interval ds l r, ds.length q.val = ds.length p.val+1 →
      BruhatStep cs (f p) (f q) := by
    intro p q hlen
    apply hgraph
    rw [Dihedral.step_iff_odd,Nat.odd_iff]
    omega
  have hla := cover lo a ha
  have hlb := cover lo b hb
  have hrootne := graphRoot_ne_of_same_source hla hlb (fun h => hab (hinj h))
  let P := rootPlane (graphRoot hla) (graphRoot hlb)
  refine ⟨graphRoot hla,graphRoot hlb,hrootne,?_⟩
  change ∀ z : Interval ds l r, f z * (f lo)⁻¹ ∈ planeSubgroup M cs P
  have hlo : f lo * (f lo)⁻¹ ∈ planeSubgroup M cs P := by simp
  have hat : f a * (f lo)⁻¹ ∈ planeSubgroup M cs P := by
    exact mem_coset_of_graphRoot hla hlo (Submodule.subset_span (Set.mem_insert _ _))
  have hbt : f b * (f lo)⁻¹ ∈ planeSubgroup M cs P := by
    exact mem_coset_of_graphRoot hlb hlo
      (Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
  intro z
  suffices ∀ n, ∀ z : Interval ds l r, ds.length z.val = n →
      f z * (f lo)⁻¹ ∈ planeSubgroup M cs P from this _ z rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro z hz
    have hzmin := length_le_of_bruhat ds z.property.1
    by_cases hzlo : z = lo
    · simpa only [hzlo] using hlo
    have hzgt : ds.length l < ds.length z.val :=
      length_lt_of_bruhat_ne ds z.property.1 (fun h => hzlo (Subtype.ext h.symm))
    by_cases hzone : ds.length z.val = ds.length l+1
    · obtain ⟨p,q,hpq,hlev⟩ := Dihedral.two_elements_length ds
        (by omega : 0 < ds.length l+1) (w := r) (by omega)
      have ap := (hlev a.val).mp ha
      have bp := (hlev b.val).mp hb
      have zp := (hlev z.val).mp hzone
      have habval : a.val ≠ b.val := fun h => hab (Subtype.ext h)
      have hza : z = a ∨ z = b := by
        apply (show z.val = a.val ∨ z.val = b.val → z = a ∨ z = b from
          fun h => h.elim (fun h => Or.inl (Subtype.ext h)) (fun h => Or.inr (Subtype.ext h)))
        grind
      rcases hza with rfl | rfl <;> assumption
    have htwo : ds.length l+2 ≤ ds.length z.val := by omega
    have hexp : ∃ p : Interval ds l r, ds.length p.val+2=ds.length z.val := by
      by_cases he : ds.length z.val = ds.length l+2
      · exact ⟨lo,he.symm⟩
      · obtain ⟨p,q,_,hp,_⟩ := Dihedral.two_interval_elements_length ds lo z
          (n := ds.length z.val-2) (by dsimp [lo]; omega) (by omega)
        exact ⟨p,by omega⟩
    obtain ⟨p,hp⟩ := hexp
    obtain ⟨q,s,hqs,hq,hs⟩ := Dihedral.two_interval_elements_length ds lo z
      (n := ds.length z.val-1) (by dsimp [lo]; omega) (by omega)
    have hp' := ih (ds.length p.val) (by omega) p rfl
    have hq' := ih (ds.length q.val) (by omega) q rfl
    have hs' := ih (ds.length s.val) (by omega) s rfl
    have hpq := cover p q (by omega)
    have hps := cover p s (by omega)
    have hqz := cover q z (by omega)
    have hsz := cover s z (by omega)
    have hplane : rootPlane (graphRoot hpq) (graphRoot hps) = P :=
      rootPlane_eq_of_mem _ _ _ _ hrootne (graphRoot_mem_of_coset hpq hp' hq')
        (graphRoot_mem_of_coset hps hp' hs')
        (graphRoot_ne_of_same_source hpq hps (fun h => hqs (hinj h)))
    have hsquare := graphRoot_square_plane hpq hps hqz hsz (fun h => hqs (hinj h))
    apply mem_coset_of_graphRoot hqz hq'
    apply (hsquare.trans hplane).le
    exact Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))

end
end KLInvariance.TitsSpace
end


section
namespace KLInvariance.TitsSpace.PlaneBasis
open Module
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)
noncomputable section

def cosetIntervalMap {a₀ u b : W}
    (hmin : ∀ z ∈ planeSubgroup M cs P, cs.length a₀ ≤ cs.length (z*a₀))
    {g k : planeSubgroup M cs P}
    (hlo : BruhatLE cs u ((g : W)*a₀)) (hhi : BruhatLE cs ((k : W)*a₀) b) :
    Interval B.system g k ↪ Interval cs u b where
  toFun z := ⟨(z.val : W)*a₀,bruhat_trans cs hlo (B.coset_bruhat hmin z.property.1),
    bruhat_trans cs (B.coset_bruhat hmin z.property.2) hhi⟩
  inj' := by
    intro x y he
    exact Subtype.ext (Subtype.ext (mul_right_cancel (congrArg Subtype.val he)))

theorem twoStep_interval_iff {a₀ : W}
    (hmin : ∀ z ∈ planeSubgroup M cs P, cs.length a₀ ≤ cs.length (z*a₀))
    {g k : planeSubgroup M cs P} (x y : Interval B.system g k)
    (hlen : B.system.length y.val=B.system.length x.val+2) :
    ∃ a b : Interval B.system g k, a ≠ b ∧ ∀ z : W,
      (BruhatStep cs ((x.val : W)*a₀) z ∧ BruhatStep cs z ((y.val : W)*a₀)) ↔
        z=(a.val : W)*a₀ ∨ z=(b.val : W)*a₀ := by
  obtain ⟨a,b,hab,hpaths⟩ := Dihedral.two_step_rank_two B.system hlen
  have ha := (hpaths a).mpr (Or.inl rfl)
  have hb := (hpaths b).mpr (Or.inr rfl)
  let ai : Interval B.system g k := ⟨a,
    bruhat_trans B.system x.property.1 (Relation.ReflTransGen.single ha.1),
    bruhat_trans B.system (Relation.ReflTransGen.single ha.2) y.property.2⟩
  let bi : Interval B.system g k := ⟨b,
    bruhat_trans B.system x.property.1 (Relation.ReflTransGen.single hb.1),
    bruhat_trans B.system (Relation.ReflTransGen.single hb.2) y.property.2⟩
  have he := (B.coset_step_iff hmin x.val a).mpr ha.1
  have hf := (B.coset_step_iff hmin a y.val).mpr ha.2
  refine ⟨ai,bi,fun h => hab (congrArg Subtype.val h),fun z => ?_⟩
  constructor
  · intro hz
    let z' : planeSubgroup M cs P := ⟨z*a₀⁻¹,B.twoStep_mem_coset he hf hz.1 hz.2⟩
    have hz' : (z' : W)*a₀=z := by dsimp [z']; group
    have hp : BruhatStep B.system x.val z' ∧ BruhatStep B.system z' y.val := by
      constructor
      · exact (B.coset_step_iff hmin x.val z').mp (hz' ▸ hz.1)
      · exact (B.coset_step_iff hmin z' y.val).mp (hz' ▸ hz.2)
    rcases (hpaths z').mp hp with hza | hzb
    · exact Or.inl (hz'.symm.trans (congrArg (fun q : planeSubgroup M cs P => (q:W)*a₀) hza))
    · exact Or.inr (hz'.symm.trans (congrArg (fun q : planeSubgroup M cs P => (q:W)*a₀) hzb))
  · rintro (rfl | rfl)
    · exact ⟨he,hf⟩
    · exact ⟨(B.coset_step_iff hmin x.val b).mpr hb.1,
        (B.coset_step_iff hmin b y.val).mpr hb.2⟩

end
end KLInvariance.TitsSpace.PlaneBasis
end


section
namespace KLInvariance.TitsSpace.PlaneBasis
open Module
universe u v u' v'
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {I' : Type u'} [Fintype I'] {M' : CoxeterMatrix I'}
  {W' : Type v'} [Group W'] {cs' : CoxeterSystem M' W'}
  {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)
noncomputable section


theorem transport_interval {a₀ u b : W} {u' b' : W'}
    (hmin : ∀ z ∈ planeSubgroup M cs P, cs.length a₀ ≤ cs.length (z*a₀))
    {g k : planeSubgroup M cs P} (hgk : BruhatLE B.system g k)
    (hrank : B.system.length g+2 ≤ B.system.length k)
    (hlo : BruhatLE cs u ((g : W)*a₀)) (hhi : BruhatLE cs ((k : W)*a₀) b)
    (e : Interval cs u b ≃o Interval cs' u' b') :
    ∃ (P' : Submodule ℝ (I' → ℝ)) (B' : PlaneBasis (M := M') (cs := cs') P')
      (a' : W') (F : Interval B.system g k → planeSubgroup M' cs' P'),
      (∀ z ∈ planeSubgroup M' cs' P', cs'.length a' ≤ cs'.length (z*a')) ∧
      Function.Injective F ∧
      (∀ z, (F z : W')*a' = (e (B.cosetIntervalMap hmin hlo hhi z)).val) ∧
      (∀ x y, BruhatLE B'.system (F x) (F y) ↔ x ≤ y) ∧
      (∀ x y, BruhatStep B'.system (F x) (F y) ↔ BruhatStep B.system x.val y.val) ∧
      (∀ z, B'.system.length (F z)+B.system.length g =
        B'.system.length (F ⟨g,bruhat_refl B.system g,hgk⟩)+B.system.length z.val) ∧
      Set.range F = {z | BruhatLE B'.system (F ⟨g,bruhat_refl B.system g,hgk⟩) z ∧
        BruhatLE B'.system z (F ⟨k,hgk,bruhat_refl B.system k⟩)} := by
  let inc := B.cosetIntervalMap hmin hlo hhi
  let f : Interval B.system g k → W' := fun z => (e (inc z)).val
  let lo : Interval B.system g k := ⟨g,bruhat_refl B.system g,hgk⟩
  have hinj : Function.Injective f := by
    intro x y h
    exact inc.injective (e.injective (Subtype.ext h))
  have hgraph (x y : Interval B.system g k) (h : BruhatStep B.system x.val y.val) :
      BruhatStep cs' (f x) (f y) := by
    exact (intervalIso_bruhatStep_iff_general cs cs' e (inc x) (inc y)).mpr
      ((B.coset_step_iff hmin x.val y.val).mpr h)
  obtain ⟨α,β,hαβ,hplane⟩ := dihedral_image_in_plane B.system f hinj hgraph hgk hrank
  let P' := rootPlane α β
  obtain ⟨B'⟩ := nonempty_planeBasis α β hαβ
  obtain ⟨a',g₀,hg₀,hg₀a,hmin'⟩ := planeCoset_exists_minimal M' cs' P' (f lo)
  have hmem (z : Interval B.system g k) : f z*a'⁻¹ ∈ planeSubgroup M' cs' P' := by
    convert (planeSubgroup M' cs' P').mul_mem (hplane z) hg₀ using 1
    change f z*a'⁻¹=f z*(f lo)⁻¹*g₀
    rw [hg₀a]
    group
  let F : Interval B.system g k → planeSubgroup M' cs' P' := fun z => ⟨f z*a'⁻¹,hmem z⟩
  have hF (z : Interval B.system g k) : (F z : W')*a'=f z := by
    dsimp [F]; group
  have hFinj : Function.Injective F := by
    intro x y h
    apply hinj
    rw [← hF x,← hF y,h]
  have hFgraph (x y : Interval B.system g k) (h : BruhatStep B.system x.val y.val) :
      BruhatStep B'.system (F x) (F y) := by
    apply (B'.coset_step_iff hmin' (F x) (F y)).mp
    rw [hF x,hF y]
    exact hgraph x y h
  have htwo (x y : Interval B.system g k)
      (hlen : B.system.length y.val=B.system.length x.val+2) :
      B'.system.length (F y)=B'.system.length (F x)+2 := by
    obtain ⟨a,c,hac,hpaths⟩ := B.twoStep_interval_iff hmin x y hlen
    have hpaths' (z : W') : (BruhatStep cs' (f x) z ∧ BruhatStep cs' z (f y)) ↔
        z=f a ∨ z=f c := intervalIso_twoStep_iff e (inc x) (inc y) (inc a) (inc c) hpaths z
    have hpa := (hpaths' (f a)).mpr (Or.inl rfl)
    have hxa : BruhatStep B'.system (F x) (F a) := by
      apply (B'.coset_step_iff hmin' (F x) (F a)).mp
      simpa only [hF] using hpa.1
    have hay : BruhatStep B'.system (F a) (F y) := by
      apply (B'.coset_step_iff hmin' (F a) (F y)).mp
      simpa only [hF] using hpa.2
    apply Dihedral.rank_two_of_two_step_bound B'.system hxa hay (b := F c)
    intro z hxz hzy
    have hp₁ := (B'.coset_step_iff hmin' (F x) z).mpr hxz
    have hp₂ := (B'.coset_step_iff hmin' z (F y)).mpr hzy
    rw [hF x] at hp₁
    rw [hF y] at hp₂
    rcases (hpaths' ((z : W')*a')).mp ⟨hp₁,hp₂⟩ with he | he
    · exact Or.inl (Subtype.ext (mul_right_cancel (he.trans (hF a).symm)))
    · exact Or.inr (Subtype.ext (mul_right_cancel (he.trans (hF c).symm)))
  have hlen := Dihedral.map_length_affine B.system B'.system F hFgraph htwo hgk hrank
  have horder (x y : Interval B.system g k) : BruhatLE B'.system (F x) (F y) ↔ x ≤ y := by
    change BruhatLE B'.system (F x) (F y) ↔ BruhatLE B.system x.val y.val
    rw [Dihedral.bruhat_iff_length_lt_or_eq,Dihedral.bruhat_iff_length_lt_or_eq]
    have hx := hlen x
    have hy := hlen y
    constructor
    · rintro (h | h)
      · left; omega
      · exact Or.inr (congrArg Subtype.val (hFinj h))
    · rintro (h | h)
      · left; omega
      · exact Or.inr (congrArg F (Subtype.ext h))
  refine ⟨P',B',a',F,hmin',hFinj,hF,horder,?_,hlen,?_⟩
  · intro x y
    rw [Dihedral.step_iff_odd,Dihedral.step_iff_odd,Nat.odd_iff,Nat.odd_iff]
    have hx := hlen x
    have hy := hlen y
    omega
  · exact Dihedral.range_eq_interval_of_rank_two B.system B'.system F hFinj
      hFgraph htwo hgk hrank

end
end KLInvariance.TitsSpace.PlaneBasis
end

end OAI
