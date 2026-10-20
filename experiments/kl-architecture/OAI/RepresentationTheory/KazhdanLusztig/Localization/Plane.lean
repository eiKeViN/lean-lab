import Mathlib
import OAI.Combinatorics.MomentGraph.Sheaf.Localization
import OAI.RepresentationTheory.KazhdanLusztig.Localization.Embed
import OAI.RepresentationTheory.KazhdanLusztig.Localization.PlaneModel
import OAI.RingTheory.Localization.RelativePrime

/-! Semantic home: OAI.RepresentationTheory.KazhdanLusztig.Localization.Plane. Source spans: PlaneLocalization:9, PlaneLocalization:6, PlaneLocalization:11, PlaneLocalization:8, PlaneLocalization:17, PlaneLocalization:13, PlaneLocalization:19, PlaneLocalization:28, PlaneLocalization:18, PlaneLocalization:20, PlaneLocalization:22, PlaneLocalization:30.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.TitsSpace.PlaneBasis
open Module BruhatGraph MomentGraph
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)
  (a₀ b : W)
noncomputable section

 def CosetVertex := {d : planeSubgroup M cs P // BruhatLE B.system 1 d ∧
    BruhatLE cs ((d:W)*a₀) b}

 instance cosetOrder : PartialOrder (B.CosetVertex a₀ b) where
  le x y := BruhatLE B.system x.val y.val
  le_refl x := bruhat_refl B.system x.val
  le_trans _ _ _ := bruhat_trans B.system
  le_antisymm x y hxy hyx := Subtype.ext (bruhat_antisymm B.system hxy hyx)

 def cosetAmbient (x : B.CosetVertex a₀ b) : Interval cs 1 b :=
  ⟨(x.val:W)*a₀,one_bruhat cs _,x.property.2⟩

 theorem cosetAmbient_injective : Function.Injective (B.cosetAmbient a₀ b) := by
  intro x y h
  apply Subtype.ext
  apply Subtype.ext
  exact mul_right_cancel (congrArg Subtype.val h)

 instance cosetFinite : Finite (B.CosetVertex a₀ b) := by
  let := interval_finite cs 1 b
  exact Finite.of_injective _ (B.cosetAmbient_injective a₀ b)

 def CosetEdge := {p : B.CosetVertex a₀ b × B.CosetVertex a₀ b //
    BruhatStep B.system p.1.val p.2.val}

 def cosetGraph : OrderedGraph (B.CosetVertex a₀ b) (B.CosetEdge a₀ b) where
  source e := e.val.1
  target e := e.val.2
  increasing e := ⟨.single e.property,fun h => not_lt_of_ge
    (length_le_of_bruhat B.system h) e.property.1⟩

variable (hmin : ∀ z ∈ planeSubgroup M cs P, cs.length a₀ ≤ cs.length (z*a₀))

 def cosetEdgeAmbient (e : B.CosetEdge a₀ b) : Edge cs 1 b :=
  ⟨(B.cosetAmbient a₀ b e.val.1,B.cosetAmbient a₀ b e.val.2),
    (B.coset_step_iff hmin _ _).mpr e.property⟩

 def cosetGraphMap : GraphMap (B.cosetGraph a₀ b) (graph cs 1 b) where
  vertex := B.cosetAmbient a₀ b
  edge := B.cosetEdgeAmbient a₀ b hmin
  source _ := rfl
  target _ := rfl

 include hmin in
 theorem coset_lower {d : planeSubgroup M cs P} {x : B.CosetVertex a₀ b}
    (hx : BruhatLE B.system d x.val) : BruhatLE cs ((d:W)*a₀) b :=
  bruhat_trans cs (B.coset_bruhat hmin hx) x.property.2

 include hmin in
 theorem coset_outgoing_below (x c : B.CosetVertex a₀ b) (hxc : x<c) :
    ∃ e : B.CosetEdge a₀ b, (B.cosetGraph a₀ b).source e=x ∧
      (B.cosetGraph a₀ b).target e ≤ c := by
  rcases Relation.ReflTransGen.cases_head hxc.le with heq | ⟨z,hxz,hzc⟩
  · exact (hxc.ne (Subtype.ext heq)).elim
  · let y : B.CosetVertex a₀ b := ⟨z,one_bruhat B.system z,
      B.coset_lower a₀ b hmin hzc⟩
    exact ⟨⟨(x,y),hxz⟩,rfl,hzc⟩

 theorem coset_lift_live (e : Edge cs 1 b)
    (he : label cs 1 b e ∈ planeSubgroup M cs P)
    (x : B.CosetVertex a₀ b) (hx : B.cosetAmbient a₀ b x=source cs 1 b e) :
    ∃ a : B.CosetEdge a₀ b, B.cosetEdgeAmbient a₀ b hmin a=e ∧
      (B.cosetGraph a₀ b).source a=x := by
  let t : planeSubgroup M cs P := ⟨label cs 1 b e,he⟩
  have hy : ((t*x.val : planeSubgroup M cs P):W)*a₀ = (target cs 1 b e).val := by
    change (label cs 1 b e*(x.val:W))*a₀ = _
    rw [mul_assoc,show (x.val:W)*a₀=(source cs 1 b e).val from congrArg Subtype.val hx]
    exact label_mul_source cs 1 b e
  let y : B.CosetVertex a₀ b := ⟨t*x.val,one_bruhat B.system _,hy.symm ▸ (target cs 1 b e).property.2⟩
  have hye : B.cosetAmbient a₀ b y=target cs 1 b e := Subtype.ext hy
  have hs : BruhatStep B.system x.val y.val := by
    apply (B.coset_step_iff hmin _ _).mp
    change BruhatStep cs (B.cosetAmbient a₀ b x).val (B.cosetAmbient a₀ b y).val
    rw [hx,hye]
    exact e.property
  refine ⟨⟨(x,y),hs⟩,?_,rfl⟩
  apply Subtype.ext
  exact Prod.ext hx hye

end
end KLInvariance.TitsSpace.PlaneBasis
end


section
namespace KLInvariance.TitsSpace.PlaneBasis
open Module BruhatGraph MomentGraph MomentGraph.Sheaf
universe u v us ur
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)
  {σ : Type us} (basis : Basis σ ℝ (Extended M))
  (R : Type ur) [CommRing R] [Algebra (MvPolynomial σ ℝ) R]
  [Module.Flat (MvPolynomial σ ℝ) R] [IsLocalRing R]
noncomputable section

 def localModels (b : planeSubgroup M cs P)
    (hα : ∀ e, algebraMap (MvPolynomial σ ℝ) R (B.modelLabel basis b e) ∈
      IsLocalRing.maximalIdeal R) :
    LocalModels (G := graph B.system 1 b)
      (fun e => algebraMap (MvPolynomial σ ℝ) R (B.modelLabel basis b e)) := by
  classical
  let := interval_finite B.system 1 b
  let := Fintype.ofFinite (Edge B.system 1 b)
  exact structureLocalModels _ _ hα (exists_outgoing_below B.system 1 b)
    (fun c => structureSheaf_flat_flabby R _ _ c (B.model_flabby basis b c))

end
end KLInvariance.TitsSpace.PlaneBasis
end


section
namespace KLInvariance.TitsSpace.PlaneBasis
open Module BruhatGraph MomentGraph MomentGraph.Sheaf
universe u v us um
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  (a₀ b : W) (hmin : ∀ z ∈ planeSubgroup M cs P, cs.length a₀ ≤ cs.length (z*a₀))
noncomputable section

 def cosetLabel (e : B.CosetEdge a₀ b) : PlaneRing basis P :=
  algebraMap (MvPolynomial σ ℝ) (PlaneRing basis P)
    (polynomialLabel cs 1 b basis (B.cosetEdgeAmbient a₀ b hmin e))

 def localizedCoset (C : Sheaf.{us,v,v,um} (R := MvPolynomial σ ℝ) (graph cs 1 b)) :
    Sheaf (R := PlaneRing basis P) (B.cosetGraph a₀ b) :=
  (C.baseChange (PlaneRing basis P)).pullback (B.cosetGraphMap a₀ b hmin)

 omit [Fintype σ] in
 theorem polynomialLabel_unit_iff (e : Edge cs 1 b) :
    IsUnit (algebraMap (MvPolynomial σ ℝ) (PlaneRing basis P)
      (polynomialLabel cs 1 b basis e)) ↔ label cs 1 b e ∉ planeSubgroup M cs P := by
  change IsUnit (algebraMap (MvPolynomial σ ℝ) (PlaneRing basis P)
    (linearPolynomial basis (embed M (BruhatGraph.root cs 1 b e).val))) ↔ _
  rw [linear_isUnit_iff]
  have hr := positiveRoot_represents M cs ⟨label cs 1 b e,label_isReflection cs 1 b e⟩
  exact not_congr (Represents.planeSubgroup_mem_iff M cs hr).symm

 omit [Fintype σ] in
 theorem localizedCoset_quotient (C : Sheaf.{us,v,v,um} (R := MvPolynomial σ ℝ) (graph cs 1 b))
    (hq : C.UpperQuotient (polynomialLabel cs 1 b basis)) :
    (B.localizedCoset basis a₀ b hmin C).UpperQuotient (B.cosetLabel basis a₀ b hmin) :=
  (C.baseChange (PlaneRing basis P)).pullback_quotient (B.cosetGraphMap a₀ b hmin)
    (fun e => algebraMap (MvPolynomial σ ℝ) (PlaneRing basis P) (polynomialLabel cs 1 b basis e))
    (C.baseChange_upperQuotient (PlaneRing basis P) (polynomialLabel cs 1 b basis) hq)

 omit [Fintype σ] in
 theorem localizedCoset_generated (C : Sheaf.{us,v,v,um} (R := MvPolynomial σ ℝ) (graph cs 1 b))
    (hg : C.Generated) : (B.localizedCoset basis a₀ b hmin C).Generated :=
  (C.baseChange (PlaneRing basis P)).pullback_generated _
    (C.baseChange_generated (PlaneRing basis P) hg)

 omit [Fintype σ] in
 theorem localizedCoset_flabby (C : Sheaf.{us,v,v,um} (R := MvPolynomial σ ℝ) (graph cs 1 b))
    (hq : C.UpperQuotient (polynomialLabel cs 1 b basis)) (hf : C.Flabby) :
    (B.localizedCoset basis a₀ b hmin C).Flabby := by
  let := interval_finite cs 1 b
  apply (C.baseChange (PlaneRing basis P)).pullback_flabby_live _
    (C.baseChange_flabby (PlaneRing basis P) hf) (B.cosetAmbient_injective a₀ b)
    {e | label cs 1 b e ∈ planeSubgroup M cs P}
  · intro e he
    exact (C.baseChange (PlaneRing basis P)).edge_subsingleton_of_unit _
      (C.baseChange_upperQuotient (PlaneRing basis P) _ hq) e
      ((polynomialLabel_unit_iff (P := P) basis b e).mpr he)
  · exact B.coset_lift_live a₀ b hmin

end
end KLInvariance.TitsSpace.PlaneBasis
end


section
namespace KLInvariance.TitsSpace.PlaneBasis
open Module BruhatGraph MomentGraph MomentGraph.Sheaf
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)
  {σ : Type us} (basis : Basis σ ℝ (Extended M))
noncomputable section

 theorem modelLabel_mem_maximal (b : planeSubgroup M cs P) (e : Edge B.system 1 b) :
    algebraMap (MvPolynomial σ ℝ) (PlaneRing basis P) (B.modelLabel basis b e) ∈
      IsLocalRing.maximalIdeal (PlaneRing basis P) := by
  apply (linear_mem_maximal_iff basis P _).mpr
  apply (Represents.planeSubgroup_mem_iff M cs (positiveRoot_represents M cs _)).mp
  exact (label B.system 1 b e).property

 def localizedModels (b : planeSubgroup M cs P) :
    LocalModels (G := graph B.system 1 b)
      (fun e => algebraMap (MvPolynomial σ ℝ) (PlaneRing basis P) (B.modelLabel basis b e)) :=
  B.localModels basis (PlaneRing basis P) b (B.modelLabel_mem_maximal basis b)

end
end KLInvariance.TitsSpace.PlaneBasis
end


section
namespace KLInvariance.TitsSpace.PlaneBasis
open Module BruhatGraph MomentGraph MomentGraph.Sheaf
open scoped Pointwise
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)
  {σ : Type us} (basis : Basis σ ℝ (Extended M))
  (a₀ b : W) (hmin : ∀ z ∈ planeSubgroup M cs P, cs.length a₀ ≤ cs.length (z*a₀))
noncomputable section

 theorem cosetEdgeAmbient_injective : Function.Injective (B.cosetEdgeAmbient a₀ b hmin) := by
  intro e f h
  apply Subtype.ext
  apply Prod.ext
  · exact B.cosetAmbient_injective a₀ b (congrArg (fun z : Edge cs 1 b => z.val.1) h)
  · exact B.cosetAmbient_injective a₀ b (congrArg (fun z : Edge cs 1 b => z.val.2) h)

 theorem cosetLabel_relPrime {e f : B.CosetEdge a₀ b} (hef : e ≠ f)
    (hs : (B.cosetGraph a₀ b).source e = (B.cosetGraph a₀ b).source f) :
    IsRelPrime (B.cosetLabel basis a₀ b hmin e) (B.cosetLabel basis a₀ b hmin f) := by
  apply LocalizationRelativePrime.map_relPrime (planePrime basis P)
    (polynomialLabel_prime cs 1 b basis _)
  intro hd
  apply hef
  apply B.cosetEdgeAmbient_injective a₀ b hmin
  apply eq_of_label_source_eq cs 1 b (label_eq_of_polynomialLabel_dvd cs 1 b basis hd)
  exact congrArg (B.cosetAmbient a₀ b) hs

 theorem coset_supported_pairwise [Fintype (B.CosetEdge a₀ b)]
    (c x : B.CosetVertex a₀ b)
    (F : Set (Outgoing (G := B.cosetGraph a₀ b) x)) :
    (supportedOutgoing (B.cosetGraph a₀ b) c x F :
      Set (Outgoing (G := B.cosetGraph a₀ b) x)).Pairwise
      (Function.onFun IsRelPrime (fun e => B.cosetLabel basis a₀ b hmin e.val)) := by
  intro e _ f _ hef
  exact B.cosetLabel_relPrime basis a₀ b hmin
    (fun h => hef (Subtype.ext h)) (e.property.trans f.property.symm)

 theorem coset_kernel_product [Fintype (B.CosetEdge a₀ b)]
    (c x : B.CosetVertex a₀ b) (F : Set (Outgoing (G := B.cosetGraph a₀ b) x)) :
    (structureSheaf (B.cosetGraph a₀ b) (B.cosetLabel basis a₀ b hmin) c).upwardKernel x F =
      kernelProduct (B.cosetGraph a₀ b) (B.cosetLabel basis a₀ b hmin) c x F •
        (⊤ : Submodule (PlaneRing basis P)
          ((structureSheaf (B.cosetGraph a₀ b) (B.cosetLabel basis a₀ b hmin) c).vertex x)) :=
  structure_kernel_product _ _ _ _ _ (B.coset_supported_pairwise basis a₀ b hmin c x F)

end
end KLInvariance.TitsSpace.PlaneBasis
end


section
namespace KLInvariance.TitsSpace.PlaneBasis
open Module BruhatGraph MomentGraph MomentGraph.Sheaf
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)
  {σ : Type us} (basis : Basis σ ℝ (Extended M))
  (a₀ b : W) (hmin : ∀ z ∈ planeSubgroup M cs P, cs.length a₀ ≤ cs.length (z*a₀))
noncomputable section

 def cosetInto (d : planeSubgroup M cs P) (hd : ∀ x : B.CosetVertex a₀ b, BruhatLE B.system x.val d) :
    B.CosetVertex a₀ b → Interval B.system 1 d := fun x => ⟨x.val,x.property.1,hd x⟩

 def cosetIntoEdge (d : planeSubgroup M cs P)
    (hd : ∀ x : B.CosetVertex a₀ b, BruhatLE B.system x.val d) (e : B.CosetEdge a₀ b) :
    Edge B.system 1 d := ⟨(B.cosetInto a₀ b d hd e.val.1,B.cosetInto a₀ b d hd e.val.2),e.property⟩

 def cosetIntoGraph (d : planeSubgroup M cs P)
    (hd : ∀ x : B.CosetVertex a₀ b, BruhatLE B.system x.val d) :
    GraphMap (B.cosetGraph a₀ b) (graph B.system 1 d) where
  vertex := B.cosetInto a₀ b d hd
  edge := B.cosetIntoEdge a₀ b d hd
  source _ := rfl
  target _ := rfl

 theorem cosetInto_injective (d : planeSubgroup M cs P)
    (hd : ∀ x : B.CosetVertex a₀ b, BruhatLE B.system x.val d) :
    Function.Injective (B.cosetInto a₀ b d hd) := by
  intro x y h
  apply Subtype.ext
  exact congrArg (fun z : Interval B.system 1 d => z.val) h

 theorem coset_label_eq (e : B.CosetEdge a₀ b) :
    label cs 1 b (B.cosetEdgeAmbient a₀ b hmin e) = (e.val.2.val : W)*(e.val.1.val:W)⁻¹ := by
  change ((e.val.2.val:W)*a₀)*((e.val.1.val:W)*a₀)⁻¹ = _
  group

 theorem coset_modelLabel_eq (d : planeSubgroup M cs P)
    (hd : ∀ x : B.CosetVertex a₀ b, BruhatLE B.system x.val d) (e : B.CosetEdge a₀ b) :
    B.modelLabel basis d (B.cosetIntoEdge a₀ b d hd e) =
      polynomialLabel cs 1 b basis (B.cosetEdgeAmbient a₀ b hmin e) := by
  have ht : (⟨(label B.system 1 d (B.cosetIntoEdge a₀ b d hd e)).val,
      (B.reflection_iff _).mp (label_isReflection B.system 1 d _)⟩ : {t : W // cs.IsReflection t}) =
      ⟨label cs 1 b (B.cosetEdgeAmbient a₀ b hmin e),label_isReflection cs 1 b _⟩ := by
    apply Subtype.ext
    change (label B.system 1 d (B.cosetIntoEdge a₀ b d hd e)).val =
      label cs 1 b (B.cosetEdgeAmbient a₀ b hmin e)
    rw [B.coset_label_eq a₀ b hmin e]
    rfl
  exact congrArg (fun t : {t : W // cs.IsReflection t} =>
    linearPolynomial basis (embed M (positiveRoot M cs t).val)) ht

 include hmin in
 theorem coset_model_flabby (c : B.CosetVertex a₀ b) :
    (structureSheaf (B.cosetGraph a₀ b) (B.cosetLabel basis a₀ b hmin) c).Flabby := by
  classical
  let := Fintype.ofFinite (B.CosetVertex a₀ b)
  obtain ⟨d,hd⟩ := Dihedral.exists_common_upper B.system
    (Finset.univ.image (fun x : B.CosetVertex a₀ b => x.val))
  have hbnd (x : B.CosetVertex a₀ b) : BruhatLE B.system x.val d :=
    hd _ (Finset.mem_image.mpr ⟨x,Finset.mem_univ _,rfl⟩)
  let f := B.cosetIntoGraph a₀ b d hbnd
  let α : Edge B.system 1 d → PlaneRing basis P := fun e =>
    algebraMap (MvPolynomial σ ℝ) (PlaneRing basis P) (B.modelLabel basis d e)
  let C := structureSheaf (graph B.system 1 d) α (f.vertex c)
  have hfl : C.Flabby := (B.localizedModels basis d).flabby (f.vertex c)
  let := interval_finite B.system 1 d
  have hpull : (C.pullback f).Flabby := by
    apply C.pullback_flabby_live f hfl (B.cosetInto_injective a₀ b d hbnd)
      {e | target B.system 1 d e ≤ f.vertex c}
    · intro e he
      exact structureSheaf_edge_subsingleton _ α (f.vertex c) e he
    · intro e he x hx
      have hlow : BruhatLE B.system (target B.system 1 d e).val c.val := he
      let y : B.CosetVertex a₀ b := ⟨(target B.system 1 d e).val,
        (target B.system 1 d e).property.1,B.coset_lower a₀ b hmin hlow⟩
      have hye : f.vertex y=target B.system 1 d e := rfl
      have hs : BruhatStep B.system x.val y.val := by
        change BruhatStep B.system (f.vertex x).val (f.vertex y).val
        rw [hx,hye]
        exact e.property
      refine ⟨⟨(x,y),hs⟩,?_,rfl⟩
      exact Subtype.ext (Prod.ext hx hye)
  have hh := (structurePullbackIso f α c (fun _ _ => Iff.rfl)).flabby hpull
  have hα : (fun e => α (f.edge e)) = B.cosetLabel basis a₀ b hmin := by
    funext e
    exact congrArg (algebraMap (MvPolynomial σ ℝ) (PlaneRing basis P))
      (B.coset_modelLabel_eq basis a₀ b hmin d hbnd e)
  rwa [hα] at hh

 def cosetModels : LocalModels (G := B.cosetGraph a₀ b) (B.cosetLabel basis a₀ b hmin) :=
  structureLocalModels _ _
    (fun e => (linear_mem_maximal_iff basis P _).mpr (by
      apply (Represents.planeSubgroup_mem_iff M cs
        (positiveRoot_represents M cs ⟨label cs 1 b (B.cosetEdgeAmbient a₀ b hmin e),
          label_isReflection cs 1 b _⟩)).mp
      change label cs 1 b (B.cosetEdgeAmbient a₀ b hmin e) ∈ planeSubgroup M cs P
      rw [B.coset_label_eq a₀ b hmin e]
      exact (planeSubgroup M cs P).mul_mem e.val.2.val.property
        ((planeSubgroup M cs P).inv_mem e.val.1.val.property)))
    (B.coset_outgoing_below a₀ b hmin) (B.coset_model_flabby basis a₀ b hmin)

end
end KLInvariance.TitsSpace.PlaneBasis
end


section
namespace KLInvariance.TitsSpace.PlaneBasis
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)
noncomputable section

/-- The combinatorial factor already constructed from ambient inversion
pairs is exactly the intrinsic relative dihedral edge degree. -/
 theorem planeWeight_coset_edge {a₀ : W}
    (hmin : ∀ z ∈ planeSubgroup M cs P, cs.length a₀ ≤ cs.length (z*a₀))
    {x y : planeSubgroup M cs P} (hxy : BruhatStep B.system x y) :
    (planeWeight ((x:W)*a₀) (B.edgeRoot hxy) P).toNat =
      (B.system.length y-B.system.length x-1)/2 := by
  classical
  let α := B.edgeRoot hxy
  obtain ⟨β,hαβ,hβ⟩ : ∃ β : PositiveRoot M cs, α ≠ β ∧ β.val ∈ P := by
    by_cases h : α=B.left
    · exact ⟨B.right,h ▸ B.distinct,B.right_mem⟩
    · exact ⟨B.left,h,B.left_mem⟩
  have hplane : rootPlane α β=P :=
    (rootPlane_eq_of_mem B.left B.right α β B.distinct
      (B.plane_eq.ge (B.edgeRoot_plane hxy)) (B.plane_eq.ge hβ) hαβ).trans B.plane_eq
  have ha : ¬rootInverted ((x:W)*a₀) α := by
    rw [show α=graphRoot ((B.coset_step_iff hmin x y).mpr hxy) from B.edgeRoot_coset hmin hxy]
    exact graphRoot_not_inverted_source _
  have href : rootRef α=(y:W)*(x:W)⁻¹ :=
    (rootReflection_represents M cs α).reflection_unique
      (graphRoot_represents ((B.bruhatStep_iff x y).mpr hxy))
  have hends : rootRef α*((x:W)*a₀)=(y:W)*a₀ := by rw [href]; group
  have h := planeWeight_relative_degree ((x:W)*a₀) α β hαβ ha
  rw [hplane,hends,B.coset_length_eq hmin x,B.coset_length_eq hmin y] at h
  have hn := planeWeight_nonneg ((x:W)*a₀) α P
  have hlen := hxy.1
  have hc : ((planeWeight ((x:W)*a₀) α P).toNat:ℤ)=planeWeight ((x:W)*a₀) α P :=
    Int.toNat_of_nonneg hn
  change (planeWeight ((x:W)*a₀) α P).toNat = _
  omega

end
end KLInvariance.TitsSpace.PlaneBasis
end


section
namespace KLInvariance.TitsSpace.PlaneBasis
open Module BruhatGraph MomentGraph MomentGraph.Sheaf
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)
  {σ : Type us} (basis : Basis σ ℝ (Extended M))
  (a₀ b : W) (hmin : ∀ z ∈ planeSubgroup M cs P, cs.length a₀ ≤ cs.length (z*a₀))
noncomputable section

 theorem cosetRoot_eq (e : B.CosetEdge a₀ b) :
    BruhatGraph.root cs 1 b (B.cosetEdgeAmbient a₀ b hmin e)=B.edgeRoot e.property := by
  rw [B.edgeRoot_coset hmin e.property]
  rfl

 theorem cosetLabel_eq_root (e : B.CosetEdge a₀ b) :
    B.cosetLabel basis a₀ b hmin e=localizedLinear basis P (B.edgeRoot e.property).val := by
  change algebraMap (MvPolynomial σ ℝ) (PlaneRing basis P)
    (polynomialRoot cs basis (BruhatGraph.root cs 1 b (B.cosetEdgeAmbient a₀ b hmin e)))=_
  rw [B.cosetRoot_eq a₀ b hmin e]
  rfl

 def reducedCosetRoot (e : B.CosetEdge a₀ b) (β : PositiveRoot M cs) :
    PlaneRing basis P ⧸ Ideal.span {B.cosetLabel basis a₀ b hmin e} :=
  algebraMap (PlaneRing basis P) _ (localizedLinear basis P β.val)

 theorem cosetLabel_reduction_associated (e f : B.CosetEdge a₀ b)
    (β : PositiveRoot M cs) (hplane : rootPlane (B.edgeRoot e.property) β=P)
    (hne : B.edgeRoot f.property ≠ B.edgeRoot e.property) :
    Associated
      (algebraMap (PlaneRing basis P) (PlaneRing basis P ⧸ Ideal.span {B.cosetLabel basis a₀ b hmin e})
        (B.cosetLabel basis a₀ b hmin f))
      (B.reducedCosetRoot basis a₀ b hmin e β) := by
  unfold reducedCosetRoot
  rw [B.cosetLabel_eq_root basis a₀ b hmin e,B.cosetLabel_eq_root basis a₀ b hmin f]
  exact localizedReduction_associated basis P (B.edgeRoot e.property) β (B.edgeRoot f.property)
    (hplane.symm ▸ B.edgeRoot_plane f.property) hne

 theorem cosetFactor_reduction_associated (e : B.CosetEdge a₀ b)
    (β : PositiveRoot M cs) (hab : B.edgeRoot e.property ≠ β)
    (hplane : rootPlane (B.edgeRoot e.property) β=P) :
    Associated
      (algebraMap (PlaneRing basis P) (PlaneRing basis P ⧸ Ideal.span {B.cosetLabel basis a₀ b hmin e})
        (algebraMap (MvPolynomial σ ℝ) (PlaneRing basis P)
          (edgeFactorLift cs basis ((e.val.1.val:W)*a₀) (B.edgeRoot e.property))))
      ((B.reducedCosetRoot basis a₀ b hmin e β)^((planeWeight ((e.val.1.val:W)*a₀) (B.edgeRoot e.property) P).toNat)) := by
  unfold reducedCosetRoot
  rw [B.cosetLabel_eq_root basis a₀ b hmin e]
  have h := edgeFactor_local_associated basis ((e.val.1.val:W)*a₀) (B.edgeRoot e.property) β hab
  rw [hplane] at h
  exact h

end
end KLInvariance.TitsSpace.PlaneBasis
end


section
namespace KLInvariance.TitsSpace.PlaneBasis
open Module BruhatGraph MomentGraph MomentGraph.Sheaf
universe u v u' v'
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)
  {I' : Type u'} [Fintype I'] {M' : CoxeterMatrix I'}
  {W' : Type v'} [Group W'] {cs' : CoxeterSystem M' W'}
  {a₀ u b : W} {u' b' : W'}
  (hmin : ∀ z ∈ planeSubgroup M cs P, cs.length a₀ ≤ cs.length (z*a₀))
noncomputable section

 def cosetUpperVertex (x : B.CosetVertex a₀ b) (hx : BruhatLE cs u ((x.val:W)*a₀)) :
    Interval cs u b := ⟨(x.val:W)*a₀,hx,x.property.2⟩

 theorem outgoing_step (x : B.CosetVertex a₀ b)
    (f : Outgoing (G := B.cosetGraph a₀ b) x) :
    BruhatStep B.system x.val f.val.val.2.val := by
  rcases f with ⟨f,hf⟩
  change f.val.1=x at hf
  subst x
  exact f.property

 include hmin in
 theorem outgoing_upper (x : B.CosetVertex a₀ b) (hx : BruhatLE cs u ((x.val:W)*a₀))
    (f : Outgoing (G := B.cosetGraph a₀ b) x) :
    BruhatLE cs u ((f.val.val.2.val:W)*a₀) :=
  bruhat_trans cs hx (.single ((B.coset_step_iff hmin _ _).mpr (B.outgoing_step x f)))

 def scheduledOutgoing (φ : Interval cs u b ≃o Interval cs' u' b')
    (α : PositiveRoot M' cs') (x : B.CosetVertex a₀ b)
    (hx : BruhatLE cs u ((x.val:W)*a₀)) : Set (Outgoing (G := B.cosetGraph a₀ b) x) :=
  {f | ambientAfterIndicator (φ (B.cosetUpperVertex x hx)).val α
    (φ (B.cosetUpperVertex f.val.val.2 (B.outgoing_upper hmin x hx f))).val = 1}

 theorem outgoing_target_injective (x : B.CosetVertex a₀ b) :
    Function.Injective (fun f : Outgoing (G := B.cosetGraph a₀ b) x => f.val.val.2) := by
  intro f g h
  apply Subtype.ext
  apply Subtype.ext
  exact Prod.ext (f.property.trans g.property.symm) h

 theorem supported_card_count [Fintype (B.CosetEdge a₀ b)]
    (φ : Interval cs u b ≃o Interval cs' u' b') (α : PositiveRoot M' cs')
    (a x c : B.CosetVertex a₀ b) (hax : a ≤ x)
    (ha : BruhatLE cs u ((a.val:W)*a₀)) :
    let hx := bruhat_trans cs ha (B.coset_bruhat hmin hax)
    let inc := B.cosetIntervalMap hmin ha c.property.2
    (supportedOutgoing (B.cosetGraph a₀ b) c x (B.scheduledOutgoing hmin φ α x hx)).card =
      ∑ᶠ z : Interval B.system a.val c.val,
        ambientAfterIndicator (φ (B.cosetUpperVertex x hx)).val α (φ (inc z)).val := by
  classical
  let := interval_finite B.system a.val c.val
  let := Fintype.ofFinite (Interval B.system a.val c.val)
  let hx := bruhat_trans cs ha (B.coset_bruhat hmin hax)
  let inc := B.cosetIntervalMap hmin ha c.property.2
  let F := B.scheduledOutgoing hmin φ α x hx
  let s := supportedOutgoing (B.cosetGraph a₀ b) c x F
  change s.card = ∑ᶠ z : Interval B.system a.val c.val,
    ambientAfterIndicator (φ (B.cosetUpperVertex x hx)).val α (φ (inc z)).val
  rw [finsum_eq_sum_of_fintype]
  rw [show s.card=(∑ _ ∈ s,(1:ℕ)) by simp]
  let idx (f : Outgoing (G := B.cosetGraph a₀ b) x) (hf : f ∈ s) :
      Interval B.system a.val c.val :=
    ⟨f.val.val.2.val,bruhat_trans B.system hax (.single (B.outgoing_step x f)),
      (Finset.mem_filter.mp hf).2.2⟩
  apply Finset.sum_bij_ne_zero (fun f hf _ => idx f hf)
  · intro _ _ _
    exact Finset.mem_univ _
  · intro f hf _ g hg _ h
    have hz : f.val.val.2.val=g.val.val.2.val := congrArg (fun z : Interval B.system a.val c.val => z.val) h
    exact B.outgoing_target_injective x (Subtype.ext hz)
  · intro z _ hz
    have hsz : BruhatStep cs' (φ (B.cosetUpperVertex x hx)).val (φ (inc z)).val := by
      by_contra hn
      exact hz (by simp only [ambientAfterIndicator,dite_eq_right hn])
    have hcz := (intervalIso_bruhatStep_iff_general cs cs' φ _ _).mp hsz
    have hs : BruhatStep B.system x.val z.val := (B.coset_step_iff hmin _ _).mp hcz
    let y : B.CosetVertex a₀ b := ⟨z.val,one_bruhat B.system z.val,
      bruhat_trans cs (B.coset_bruhat hmin z.property.2) c.property.2⟩
    let f : Outgoing (G := B.cosetGraph a₀ b) x := ⟨⟨(x,y),hs⟩,rfl⟩
    have hfF : f ∈ F := by
      change ambientAfterIndicator (φ (B.cosetUpperVertex x hx)).val α (φ (inc z)).val=1
      unfold ambientAfterIndicator at hz ⊢
      split_ifs at hz ⊢ <;> omega
    have hfs : f ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hfF,z.property.2⟩
    exact ⟨f,hfs,by omega,rfl⟩
  · intro f hf _
    exact ((Finset.mem_filter.mp hf).2.1).symm

end
end KLInvariance.TitsSpace.PlaneBasis
end


section
namespace KLInvariance.TitsSpace.PlaneBasis
open Module BruhatGraph MomentGraph MomentGraph.Sheaf
universe u v u' v'
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)
  {I' : Type u'} [Fintype I'] {M' : CoxeterMatrix I'}
  {W' : Type v'} [Group W'] {cs' : CoxeterSystem M' W'}
  {a₀ u b : W} {u' b' : W'}
  (hmin : ∀ z ∈ planeSubgroup M cs P, cs.length a₀ ≤ cs.length (z*a₀))
  (φ : Interval cs u b ≃o Interval cs' u' b')
noncomputable section

 include hmin in
 theorem cosetEdge_target_upper (e : B.CosetEdge a₀ b)
    (hx : BruhatLE cs u ((e.val.1.val:W)*a₀)) : BruhatLE cs u ((e.val.2.val:W)*a₀) :=
  bruhat_trans cs hx (.single ((B.coset_step_iff hmin _ _).mpr e.property))

 def mappedCosetRoot (e : B.CosetEdge a₀ b) (hx : BruhatLE cs u ((e.val.1.val:W)*a₀)) :
    PositiveRoot M' cs' :=
  graphRoot ((intervalIso_bruhatStep_iff_general cs cs' φ
    (B.cosetUpperVertex e.val.1 hx)
    (B.cosetUpperVertex e.val.2 (B.cosetEdge_target_upper hmin e hx))).mpr
    ((B.coset_step_iff hmin _ _).mpr e.property))

 def scheduledLower (e : B.CosetEdge a₀ b) (hx : BruhatLE cs u ((e.val.1.val:W)*a₀)) :
    Set (Outgoing (G := B.cosetGraph a₀ b) e.val.1) :=
  B.scheduledOutgoing hmin φ (B.mappedCosetRoot hmin φ e hx) e.val.1 hx

 def scheduledUpper (e : B.CosetEdge a₀ b) (hx : BruhatLE cs u ((e.val.1.val:W)*a₀)) :
    Set (Outgoing (G := B.cosetGraph a₀ b) e.val.2) :=
  B.scheduledOutgoing hmin φ (B.mappedCosetRoot hmin φ e hx) e.val.2
    (B.cosetEdge_target_upper hmin e hx)

 theorem scheduledLower_self (e : B.CosetEdge a₀ b)
    (hx : BruhatLE cs u ((e.val.1.val:W)*a₀)) :
    (⟨e,rfl⟩ : Outgoing (G := B.cosetGraph a₀ b) e.val.1) ∉ B.scheduledLower hmin φ e hx := by
  change ambientAfterIndicator _ (graphRoot _) _ ≠ 1
  rw [ambientAfterIndicator_edge_self]
  omega

 theorem supported_count_difference [Fintype (B.CosetEdge a₀ b)]
    (e : B.CosetEdge a₀ b) (hx : BruhatLE cs u ((e.val.1.val:W)*a₀))
    (c : B.CosetVertex a₀ b) (hyc : e.val.2 ≤ c) :
    (supportedOutgoing (B.cosetGraph a₀ b) c e.val.1 (B.scheduledLower hmin φ e hx)).card =
      (supportedOutgoing (B.cosetGraph a₀ b) c e.val.2 (B.scheduledUpper hmin φ e hx)).card+
        (planeWeight ((e.val.1.val:W)*a₀) (B.edgeRoot e.property) P).toNat := by
  let x := e.val.1
  let y := e.val.2
  let α := B.mappedCosetRoot hmin φ e hx
  have hxy : BruhatLE B.system x.val y.val := .single e.property
  have hxc : BruhatLE B.system x.val c.val := bruhat_trans B.system hxy hyc
  let yy : Interval B.system x.val c.val := ⟨y.val,hxy,hyc⟩
  have h := B.transported_count_difference_all hmin hxc hx c.property.2 φ yy e.property
  rw [B.planeWeight_coset_edge hmin e.property]
  change (supportedOutgoing (B.cosetGraph a₀ b) c x (B.scheduledOutgoing hmin φ α x hx)).card =
    (supportedOutgoing (B.cosetGraph a₀ b) c y
      (B.scheduledOutgoing hmin φ α y (B.cosetEdge_target_upper hmin e hx))).card+_
  rw [B.supported_card_count hmin φ α x x c (bruhat_refl B.system x.val) hx,
    B.supported_card_count hmin φ α x y c hxy hx]
  exact h

end
end KLInvariance.TitsSpace.PlaneBasis
end


section
namespace KLInvariance.TitsSpace.PlaneBasis
open Module BruhatGraph MomentGraph MomentGraph.Sheaf
universe u v u' v'
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)
  {I' : Type u'} [Fintype I'] {M' : CoxeterMatrix I'}
  {W' : Type v'} [Group W'] {cs' : CoxeterSystem M' W'}
  {a₀ u b : W} {u' b' : W'}
  (hmin : ∀ z ∈ planeSubgroup M cs P, cs.length a₀ ≤ cs.length (z*a₀))
  (φ : Interval cs u b ≃o Interval cs' u' b')
noncomputable section

 theorem scheduledOutgoing_eq (α : PositiveRoot M' cs')
    (x : B.CosetVertex a₀ b) (hx : BruhatLE cs u ((x.val:W)*a₀)) :
    B.scheduledOutgoing hmin φ α x hx =
      {f | B.cosetEdgeAmbient a₀ b hmin f.val ∈ ambientLater φ α} := by
  ext f
  rcases f with ⟨⟨⟨s,t⟩,hst⟩,hs⟩
  change s=x at hs
  subst s
  change (_=1) ↔ ∃ hh : BruhatLE cs u ((x.val:W)*a₀), _=1
  constructor
  · intro h
    exact ⟨hx,h⟩
  · rintro ⟨_,h⟩
    exact h

end
end KLInvariance.TitsSpace.PlaneBasis
end


section
namespace KLInvariance.TitsSpace.PlaneBasis
open Module BruhatGraph MomentGraph MomentGraph.Sheaf
universe u v u' v'
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)
noncomputable section

 theorem exists_coset_edge {b : W} (e : Edge cs 1 b)
    (he : (BruhatGraph.root cs 1 b e).val ∈ P) :
    ∃ a₀, ∃ hmin : ∀ z ∈ planeSubgroup M cs P, cs.length a₀ ≤ cs.length (z*a₀),
      ∃ d : B.CosetEdge a₀ b, B.cosetEdgeAmbient a₀ b hmin d=e := by
  obtain ⟨a₀,g,hg,hx,hmin⟩ := planeCoset_exists_minimal M cs P (source cs 1 b e).val
  have ht : label cs 1 b e ∈ planeSubgroup M cs P :=
    (Represents.planeSubgroup_mem_iff M cs (positiveRoot_represents M cs
      ⟨label cs 1 b e,label_isReflection cs 1 b e⟩)).mpr he
  let gg : planeSubgroup M cs P := ⟨g,hg⟩
  let hh : planeSubgroup M cs P := ⟨label cs 1 b e*g,(planeSubgroup M cs P).mul_mem ht hg⟩
  have hy : (hh:W)*a₀=(target cs 1 b e).val := by
    change (label cs 1 b e*g)*a₀=_
    rw [mul_assoc,← hx,label_mul_source]
  let x : B.CosetVertex a₀ b := ⟨gg,one_bruhat B.system gg,hx ▸ (source cs 1 b e).property.2⟩
  let y : B.CosetVertex a₀ b := ⟨hh,one_bruhat B.system hh,hy.symm ▸ (target cs 1 b e).property.2⟩
  have hs : BruhatStep B.system gg hh := by
    apply (B.coset_step_iff hmin gg hh).mp
    rw [show (gg:W)*a₀=(source cs 1 b e).val from hx.symm,hy]
    exact e.property
  refine ⟨a₀,hmin,⟨(x,y),hs⟩,?_⟩
  apply Subtype.ext
  exact Prod.ext (Subtype.ext hx.symm) (Subtype.ext hy)

variable {I' : Type u'} [Fintype I'] {M' : CoxeterMatrix I'}
  {W' : Type v'} [Group W'] {cs' : CoxeterSystem M' W'}
  {a₀ u b : W} {u' b' : W'}
  (hmin : ∀ z ∈ planeSubgroup M cs P, cs.length a₀ ≤ cs.length (z*a₀))
  (φ : Interval cs u b ≃o Interval cs' u' b')

 theorem mappedCosetRoot_eq (e : B.CosetEdge a₀ b)
    (hx : BruhatLE cs u ((e.val.1.val:W)*a₀)) :
    B.mappedCosetRoot hmin φ e hx = mappedEdgeRoot φ (B.cosetEdgeAmbient a₀ b hmin e) hx := rfl

end
end KLInvariance.TitsSpace.PlaneBasis
end

end OAI
