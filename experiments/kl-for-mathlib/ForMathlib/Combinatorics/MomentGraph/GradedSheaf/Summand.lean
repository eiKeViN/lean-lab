module
public import Mathlib
public import ForMathlib.Algebra.Module.Graded.ModuleData.Range
public import ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Hom

public section

/-! Semantic home: ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Summand. Source spans: BalancedPairings:26, BalancedPairings:28, BalancedPairings:7, BalancedPairings:14, BalancedPairings:15, BalancedPairings:22, BalancedPairings:31, BalancedPairings:32.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.MomentGraph.GradedSheaf
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} {V E : Type um} [PartialOrder V] {G : OrderedGraph V E}
  {B C : GradedSheaf (𝓐 := 𝓐) G}

 theorem Hom.eq_of_maps (f g : Hom B C)
    (hv : ∀ x v, (f.vertex x).map v=(g.vertex x).map v)
    (he : ∀ e v, (f.edge e).map v=(g.edge e).map v) : f=g := by
  have hv' : f.vertex=g.vertex := funext (fun x =>
    ModuleData.Hom.eq_of_map_eq _ _ (LinearMap.ext (hv x)))
  have he' : f.edge=g.edge := funext (fun e =>
    ModuleData.Hom.eq_of_map_eq _ _ (LinearMap.ext (he e)))
  cases f
  cases g
  cases hv'
  cases he'
  rfl

 theorem Hom.eq_of_vertex (f g : Hom B C)
    (hs : ∀ e, Function.Surjective (B.lower e).map)
    (hv : ∀ x v, (f.vertex x).map v=(g.vertex x).map v) : f=g := by
  apply f.eq_of_maps g hv
  intro e v
  obtain ⟨w,rfl⟩ := hs e v
  rw [f.lower,g.lower,hv]

end KLInvariance.MomentGraph.GradedSheaf
end


section
namespace KLInvariance.MomentGraph.GradedSheaf
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} {V E : Type um} [PartialOrder V] {G : OrderedGraph V E}
  {B C : GradedSheaf (𝓐 := 𝓐) G}

 @[expose] def Hom.zero : Hom B C where
  vertex x := ⟨0,fun n _ _ => (C.vertex x).piece n |>.zero_mem⟩
  edge e := ⟨0,fun n _ _ => (C.edge e).piece n |>.zero_mem⟩
  lower e v := by simp
  upper e v := by simp

 @[expose] def Hom.id (B : GradedSheaf (𝓐 := 𝓐) G) : Hom B B where
  vertex x := ModuleData.Hom.id (B.vertex x)
  edge e := ModuleData.Hom.id (B.edge e)
  lower _ _ := rfl
  upper _ _ := rfl

 @[expose] def Hom.PrimitiveProjector (p : Hom B B) : Prop :=
  p.comp p=p ∧ ∀ f : Hom B B, f.comp f=f → f.comp p=f → p.comp f=f →
    f=Hom.zero ∨ f=p

 theorem Hom.primitive_of_antiInvolution
    (a : Hom B B → Hom B B)
    (ha : Function.Involutive a)
    (hac : ∀ f g, a (f.comp g)=(a g).comp (a f))
    (haz : a Hom.zero=Hom.zero)
    (p : Hom B B) (hp : p.PrimitiveProjector) :
    (a p).PrimitiveProjector := by
  constructor
  · exact (hac p p).symm.trans (congrArg a hp.1)
  · intro f hf hfp hpf
    have hi : (a f).comp (a f)=a f := (hac f f).symm.trans (congrArg a hf)
    have hleft : (a f).comp p=a f := by
      have hh := congrArg a hpf
      rw [hac,ha] at hh
      exact hh
    have hright : p.comp (a f)=a f := by
      have hh := congrArg a hfp
      rw [hac,ha] at hh
      exact hh
    rcases hp.2 (a f) hi hleft hright with hz | he
    · left
      have hh := congrArg a hz
      rw [ha,haz] at hh
      exact hh
    · right
      exact (ha f).symm.trans (congrArg a he)

end KLInvariance.MomentGraph.GradedSheaf
end


section
namespace KLInvariance.MomentGraph.GradedSheaf
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} {V E : Type um} [PartialOrder V]
  {G : OrderedGraph V E} {B C : GradedSheaf (𝓐 := 𝓐) G}
noncomputable section

 @[expose] def Hom.assignmentMap (h : Hom B C) : B.forget.Assignment →ₗ[A] C.forget.Assignment where
  toFun f x := (h.vertex x).map (f x)
  map_add' f g := by funext x; exact map_add (h.vertex x).map (f x) (g x)
  map_smul' r f := by funext x; exact map_smul (h.vertex x).map r (f x)

 theorem Hom.assignmentMap_compatible (h : Hom B C) (Ω : Set V)
    (f : B.forget.Assignment) (hf : B.forget.CompatibleOn Ω f) :
    C.forget.CompatibleOn Ω (h.assignmentMap f) := by
  intro e hs ht
  change (C.lower e).map ((h.vertex _).map (f _)) =
    (C.upper e).map ((h.vertex _).map (f _))
  exact (h.lower e (f (G.source e))).symm.trans
    ((congrArg (h.edge e).map (hf e hs ht)).trans (h.upper e (f (G.target e))))

 @[expose] def Hom.sectionMap (h : Hom B C) (Ω : Set V) :
    B.forget.sections Ω →ₗ[A] C.forget.sections Ω :=
  (h.assignmentMap.domRestrict (B.forget.sections Ω)).codRestrict (C.forget.sections Ω)
    (fun f => h.assignmentMap_compatible Ω f.val f.property)

 theorem Hom.sectionMap_apply (h : Hom B C) (Ω : Set V)
    (f : B.forget.sections Ω) (x : V) :
    (h.sectionMap Ω f).val x=(h.vertex x).map (f.val x) := rfl

 variable [Fintype V] [Fintype E] [IsNoetherianRing A]

 @[expose] def Hom.gradedSectionMap (h : Hom B C) (Ω : Set V) :
    ModuleData.Hom (B.sections Ω) (C.sections Ω) where
  map := h.sectionMap Ω
  graded := by
    intro n f hf x hx
    exact (h.vertex x).graded n (f.val x) (hf x hx)

omit [Fintype V] [Fintype E] [IsNoetherianRing A] in
 theorem SplitIn.sections_split (s : SplitIn B C) (Ω : Set V)
    (f : B.forget.sections Ω) :
    s.projection.sectionMap Ω (s.inclusion.sectionMap Ω f)=f := by
  apply Subtype.ext
  funext x
  exact s.vertex_split x (f.val x)

end
end KLInvariance.MomentGraph.GradedSheaf
end


section
namespace KLInvariance.MomentGraph.GradedSheaf
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} [IsNoetherianRing A]
  {V E : Type um} [PartialOrder V] {G : OrderedGraph V E}
  {B : GradedSheaf (𝓐 := 𝓐) G}
noncomputable section

 @[expose] def Hom.image (h : Hom B B) : GradedSheaf (𝓐 := 𝓐) G where
  vertex x := ModuleData.range (h.vertex x)
  edge e := ModuleData.range (h.edge e)
  lower e := ModuleData.rangeMap (h.vertex (G.source e)) (h.edge e) (B.lower e) (h.lower e)
  upper e := ModuleData.rangeMap (h.vertex (G.target e)) (h.edge e) (B.upper e) (h.upper e)

 @[expose] def Hom.imageInclusion (h : Hom B B) : Hom h.image B where
  vertex x := ModuleData.rangeInclusion (h.vertex x)
  edge e := ModuleData.rangeInclusion (h.edge e)
  lower _ _ := rfl
  upper _ _ := rfl

 @[expose] def Hom.imageProjection (h : Hom B B) : Hom B h.image where
  vertex x := ModuleData.rangeProjection (h.vertex x)
  edge e := ModuleData.rangeProjection (h.edge e)
  lower e v := Subtype.ext (h.lower e v)
  upper e v := Subtype.ext (h.upper e v)

 @[expose] def Hom.imageSplit (h : Hom B B)
    (hv : ∀ x v, (h.vertex x).map ((h.vertex x).map v)=(h.vertex x).map v)
    (he : ∀ e v, (h.edge e).map ((h.edge e).map v)=(h.edge e).map v) : SplitIn h.image B where
  inclusion := h.imageInclusion
  projection := h.imageProjection
  vertex_split x v := by
    obtain ⟨m,hm⟩ := v.property
    apply Subtype.ext
    change (h.vertex x).map v.val=v.val
    rw [← hm,hv]
  edge_split e v := by
    obtain ⟨m,hm⟩ := v.property
    apply Subtype.ext
    change (h.edge e).map v.val=v.val
    rw [← hm,he]

end
end KLInvariance.MomentGraph.GradedSheaf
end


section
namespace KLInvariance.MomentGraph.GradedSheaf
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} [IsNoetherianRing A]
  {V E : Type um} [PartialOrder V] {G : OrderedGraph V E}
  {B : GradedSheaf (𝓐 := 𝓐) G}
noncomputable section

 theorem Hom.imageSection_fixed (h : Hom B B)
    (hv : ∀ x v, (h.vertex x).map ((h.vertex x).map v)=(h.vertex x).map v)
    (Ω : Set V) (f : h.image.forget.sections Ω) :
    h.sectionMap Ω (h.imageInclusion.sectionMap Ω f)=h.imageInclusion.sectionMap Ω f := by
  apply Subtype.ext
  funext x
  obtain ⟨v,hv'⟩ := (f.val x).property
  change (h.vertex x).map (f.val x).val=(f.val x).val
  rw [← hv',hv]

 @[expose] def Hom.imageSectionMap (h : Hom B B)
    (hv : ∀ x v, (h.vertex x).map ((h.vertex x).map v)=(h.vertex x).map v)
    (Ω : Set V) : h.image.forget.sections Ω →ₗ[A] LinearMap.range (h.sectionMap Ω) :=
  (h.imageInclusion.sectionMap Ω).codRestrict _ (fun f =>
    ⟨h.imageInclusion.sectionMap Ω f,h.imageSection_fixed hv Ω f⟩)

 theorem Hom.imageSectionMap_bijective (h : Hom B B)
    (hv : ∀ x v, (h.vertex x).map ((h.vertex x).map v)=(h.vertex x).map v)
    (Ω : Set V) : Function.Bijective (h.imageSectionMap hv Ω) := by
  constructor
  · intro f g hfg
    apply Subtype.ext
    funext x
    apply Subtype.ext
    exact congrFun (congrArg Subtype.val (congrArg Subtype.val hfg)) x
  · rintro ⟨s,m,rfl⟩
    refine ⟨h.imageProjection.sectionMap Ω m,?_⟩
    apply Subtype.ext
    apply Subtype.ext
    rfl

 @[expose] def Hom.imageSectionEquiv (h : Hom B B)
    (hv : ∀ x v, (h.vertex x).map ((h.vertex x).map v)=(h.vertex x).map v)
    (Ω : Set V) : h.image.forget.sections Ω ≃ₗ[A] LinearMap.range (h.sectionMap Ω) :=
  LinearEquiv.ofBijective (h.imageSectionMap hv Ω) (h.imageSectionMap_bijective hv Ω)

end
end KLInvariance.MomentGraph.GradedSheaf
end


section
namespace KLInvariance.MomentGraph.GradedSheaf
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} [IsNoetherianRing A]
  {V E : Type um} [PartialOrder V] {G : OrderedGraph V E}
  {B C : GradedSheaf (𝓐 := 𝓐) G} (s : SplitIn B C)
noncomputable section

 @[expose] def SplitIn.projector : Hom C C := s.inclusion.comp s.projection

omit [IsNoetherianRing A] in
 theorem SplitIn.projector_vertex (x : V) (v : C.vertex x) :
    (s.projector.vertex x).map ((s.projector.vertex x).map v)=(s.projector.vertex x).map v := by
  change (s.inclusion.vertex x).map ((s.projection.vertex x).map
    ((s.inclusion.vertex x).map ((s.projection.vertex x).map v)))=_
  rw [s.vertex_split]
  rfl

omit [IsNoetherianRing A] in
 theorem SplitIn.projector_edge (e : E) (v : C.edge e) :
    (s.projector.edge e).map ((s.projector.edge e).map v)=(s.projector.edge e).map v := by
  change (s.inclusion.edge e).map ((s.projection.edge e).map
    ((s.inclusion.edge e).map ((s.projection.edge e).map v)))=_
  rw [s.edge_split]
  rfl

 @[expose] def SplitIn.imageTo : Hom s.projector.image B := s.projection.comp s.projector.imageInclusion
 @[expose] def SplitIn.toImage : Hom B s.projector.image := s.projector.imageProjection.comp s.inclusion

 theorem SplitIn.imageTo_toImage_vertex (x : V) (v : B.vertex x) :
    (s.imageTo.vertex x).map ((s.toImage.vertex x).map v)=v := by
  change (s.projection.vertex x).map ((s.inclusion.vertex x).map
    ((s.projection.vertex x).map ((s.inclusion.vertex x).map v)))=v
  rw [s.vertex_split,s.vertex_split]

 theorem SplitIn.toImage_imageTo_vertex (x : V) (v : s.projector.image.vertex x) :
    (s.toImage.vertex x).map ((s.imageTo.vertex x).map v)=v := by
  apply Subtype.ext
  obtain ⟨m,hm⟩ := v.property
  change (s.projector.vertex x).map ((s.projector.vertex x).map v.val)=v.val
  rw [s.projector_vertex,← hm,s.projector_vertex]

 theorem SplitIn.imageTo_toImage_edge (e : E) (v : B.edge e) :
    (s.imageTo.edge e).map ((s.toImage.edge e).map v)=v := by
  change (s.projection.edge e).map ((s.inclusion.edge e).map
    ((s.projection.edge e).map ((s.inclusion.edge e).map v)))=v
  rw [s.edge_split,s.edge_split]

 theorem SplitIn.toImage_imageTo_edge (e : E) (v : s.projector.image.edge e) :
    (s.toImage.edge e).map ((s.imageTo.edge e).map v)=v := by
  apply Subtype.ext
  obtain ⟨m,hm⟩ := v.property
  change (s.projector.edge e).map ((s.projector.edge e).map v.val)=v.val
  rw [s.projector_edge,← hm,s.projector_edge]

 theorem SplitIn.imageSection_bijective (Ω : Set V) :
    Function.Bijective (s.imageTo.sectionMap Ω) := by
  constructor
  · intro m n he
    apply Subtype.ext
    funext x
    have hx := congrFun (congrArg Subtype.val he) x
    have hy := congrArg (s.toImage.vertex x).map hx
    exact (s.toImage_imageTo_vertex x (m.val x)).symm.trans
      (hy.trans (s.toImage_imageTo_vertex x (n.val x)))
  · intro m
    refine ⟨s.toImage.sectionMap Ω m,?_⟩
    apply Subtype.ext
    funext x
    exact s.imageTo_toImage_vertex x (m.val x)

 @[expose] def SplitIn.imageSectionEquiv (Ω : Set V) :
    s.projector.image.forget.sections Ω ≃ₗ[A] B.forget.sections Ω :=
  LinearEquiv.ofBijective (s.imageTo.sectionMap Ω) (s.imageSection_bijective Ω)

 theorem SplitIn.imageSectionEquiv_symm_apply (Ω : Set V) (m : B.forget.sections Ω) :
    (s.imageSectionEquiv Ω).symm m=s.toImage.sectionMap Ω m := by
  apply (s.imageSectionEquiv Ω).injective
  rw [LinearEquiv.apply_symm_apply]
  apply Subtype.ext
  funext x
  exact (s.imageTo_toImage_vertex x (m.val x)).symm

 theorem SplitIn.imageSectionEquiv_symm_homogeneous (Ω : Set V) (n : ℤ)
    (m : B.forget.sections Ω) (hm : ∀ x, m.val x ∈ (B.vertex x).piece n) (x : V) :
    ((s.imageSectionEquiv Ω).symm m).val x ∈ (s.projector.image.vertex x).piece n := by
  rw [s.imageSectionEquiv_symm_apply]
  exact (s.toImage.vertex x).graded n (m.val x) (hm x)

end
end KLInvariance.MomentGraph.GradedSheaf
end


section
namespace KLInvariance.MomentGraph.GradedSheaf
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} {V E : Type um} [PartialOrder V] {G : OrderedGraph V E}
  {B C : GradedSheaf (𝓐 := 𝓐) G}
noncomputable section

 @[expose] def SplitIn.liftEnd (s : SplitIn B C) (f : Hom B B) : Hom C C :=
  s.inclusion.comp (f.comp s.projection)

 theorem SplitIn.liftEnd_injective (s : SplitIn B C) : Function.Injective s.liftEnd := by
  intro f g h
  apply Hom.eq_of_maps
  · intro x v
    have hh := congrArg (fun q : Hom C C => (s.projection.vertex x).map
      ((q.vertex x).map ((s.inclusion.vertex x).map v))) h
    change (s.projection.vertex x).map ((s.inclusion.vertex x).map
      ((f.vertex x).map ((s.projection.vertex x).map ((s.inclusion.vertex x).map v))))=
      (s.projection.vertex x).map ((s.inclusion.vertex x).map
      ((g.vertex x).map ((s.projection.vertex x).map ((s.inclusion.vertex x).map v)))) at hh
    simpa only [s.vertex_split] using hh
  · intro e v
    have hh := congrArg (fun q : Hom C C => (s.projection.edge e).map
      ((q.edge e).map ((s.inclusion.edge e).map v))) h
    change (s.projection.edge e).map ((s.inclusion.edge e).map
      ((f.edge e).map ((s.projection.edge e).map ((s.inclusion.edge e).map v))))=
      (s.projection.edge e).map ((s.inclusion.edge e).map
      ((g.edge e).map ((s.projection.edge e).map ((s.inclusion.edge e).map v)))) at hh
    simpa only [s.edge_split] using hh

 theorem SplitIn.liftEnd_comp (s : SplitIn B C) (f g : Hom B B) :
    s.liftEnd (f.comp g)=(s.liftEnd f).comp (s.liftEnd g) := by
  apply Hom.eq_of_maps
  · intro x v
    change (s.inclusion.vertex x).map ((f.vertex x).map ((g.vertex x).map
      ((s.projection.vertex x).map v)))=
      (s.inclusion.vertex x).map ((f.vertex x).map ((s.projection.vertex x).map
      ((s.inclusion.vertex x).map ((g.vertex x).map ((s.projection.vertex x).map v)))))
    rw [s.vertex_split]
  · intro e v
    change (s.inclusion.edge e).map ((f.edge e).map ((g.edge e).map
      ((s.projection.edge e).map v)))=
      (s.inclusion.edge e).map ((f.edge e).map ((s.projection.edge e).map
      ((s.inclusion.edge e).map ((g.edge e).map ((s.projection.edge e).map v)))))
    rw [s.edge_split]

 theorem SplitIn.liftEnd_zero (s : SplitIn B C) : s.liftEnd Hom.zero=Hom.zero := by
  apply Hom.eq_of_maps
  · intro x v
    change (s.inclusion.vertex x).map 0=0
    exact map_zero _
  · intro e v
    change (s.inclusion.edge e).map 0=0
    exact map_zero _

 theorem SplitIn.primitive_id_of_projector (s : SplitIn B C)
    (h : s.projector.PrimitiveProjector) : (Hom.id B).PrimitiveProjector := by
  constructor
  · apply Hom.eq_of_maps <;> intros <;> rfl
  · intro f hf _ _
    have hc : (s.liftEnd f).comp (s.liftEnd f)=s.liftEnd f :=
      (s.liftEnd_comp f f).symm.trans (congrArg s.liftEnd hf)
    have hi : s.liftEnd (Hom.id B)=s.projector := by
      apply Hom.eq_of_maps <;> intros <;> rfl
    have hleft : (s.liftEnd f).comp s.projector=s.liftEnd f := by
      rw [← hi,← s.liftEnd_comp]
      congr 1
    have hright : s.projector.comp (s.liftEnd f)=s.liftEnd f := by
      rw [← hi,← s.liftEnd_comp]
      congr 1
    rcases h.2 (s.liftEnd f) hc hleft hright with hz | he
    · exact Or.inl (s.liftEnd_injective (hz.trans s.liftEnd_zero.symm))
    · exact Or.inr (s.liftEnd_injective (he.trans hi.symm))

 theorem SplitIn.projector_eq_id_of_primitive (s : SplitIn B C)
    (h : (Hom.id C).PrimitiveProjector)
    (x : V) [Nontrivial (B.vertex x)] : s.projector=Hom.id C := by
  have hi : s.projector.comp s.projector=s.projector := by
    apply Hom.eq_of_maps
    · exact s.projector_vertex
    · exact s.projector_edge
  have hl : s.projector.comp (Hom.id C)=s.projector := by
    apply Hom.eq_of_maps <;> intros <;> rfl
  have hr : (Hom.id C).comp s.projector=s.projector := by
    apply Hom.eq_of_maps <;> intros <;> rfl
  rcases h.2 s.projector hi hl hr with hz | he
  · obtain ⟨v,hv⟩ := exists_ne (0 : B.vertex x)
    exfalso
    apply hv
    have hh := congrArg (fun q : Hom C C => (s.projection.vertex x).map
      ((q.vertex x).map ((s.inclusion.vertex x).map v))) hz
    change (s.projection.vertex x).map ((s.inclusion.vertex x).map
      ((s.projection.vertex x).map ((s.inclusion.vertex x).map v)))=
      (s.projection.vertex x).map 0 at hh
    simpa only [s.vertex_split,map_zero] using hh
  · exact he

 @[expose] def SplitIn.isoOfProjectorEqId (s : SplitIn B C) (h : s.projector=Hom.id C) : Iso B C where
  vertex x :=
    { toLinearMap := (s.inclusion.vertex x).map
      invFun := (s.projection.vertex x).map
      left_inv := s.vertex_split x
      right_inv := fun v => congrArg (fun q : Hom C C => (q.vertex x).map v) h }
  edge e :=
    { toLinearMap := (s.inclusion.edge e).map
      invFun := (s.projection.edge e).map
      left_inv := s.edge_split e
      right_inv := fun v => congrArg (fun q : Hom C C => (q.edge e).map v) h }
  lower e v := s.inclusion.lower e v
  upper e v := s.inclusion.upper e v
  vertex_graded x := (s.inclusion.vertex x).graded
  edge_graded e := (s.inclusion.edge e).graded

 @[expose] def SplitIn.isoOfPrimitive (s : SplitIn B C)
    (h : (Hom.id C).PrimitiveProjector)
    (x : V) [Nontrivial (B.vertex x)] : Iso B C :=
  s.isoOfProjectorEqId (s.projector_eq_id_of_primitive h x)

 variable [IsNoetherianRing A]

 theorem Hom.primitive_image (p : Hom B B) (hp : p.PrimitiveProjector) :
    (Hom.id p.image).PrimitiveProjector := by
  have hv : ∀ x v, (p.vertex x).map ((p.vertex x).map v)=(p.vertex x).map v := by
    intro x v
    exact congrArg (fun q : Hom B B => (q.vertex x).map v) hp.1
  have he : ∀ e v, (p.edge e).map ((p.edge e).map v)=(p.edge e).map v := by
    intro e v
    exact congrArg (fun q : Hom B B => (q.edge e).map v) hp.1
  let s := p.imageSplit hv he
  have hs : s.projector=p := by
    apply Hom.eq_of_maps <;> intros <;> rfl
  apply s.primitive_id_of_projector
  rw [hs]
  exact hp

end
end KLInvariance.MomentGraph.GradedSheaf
end


section
namespace KLInvariance.MomentGraph.GradedSheaf
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} {V E : Type um} [PartialOrder V] {G : OrderedGraph V E}
  {B C : GradedSheaf (𝓐 := 𝓐) G}
noncomputable section

 @[expose] def SplitIn.downEnd (s : SplitIn B C) (f : Hom C C) : Hom B B :=
  s.projection.comp (f.comp s.inclusion)

 theorem SplitIn.lift_down (s : SplitIn B C) (f : Hom C C)
    (hf : f.comp s.projector=f) (hf' : s.projector.comp f=f) :
    s.liftEnd (s.downEnd f)=f := by
  have heq : s.liftEnd (s.downEnd f)=s.projector.comp (f.comp s.projector) := by
    apply Hom.eq_of_maps <;> intros <;> rfl
  rw [heq,hf,hf']

 theorem SplitIn.downEnd_idempotent (s : SplitIn B C) (f : Hom C C)
    (hf : f.comp f=f) (hf' : s.projector.comp f=f) :
    (s.downEnd f).comp (s.downEnd f)=s.downEnd f := by
  have heq : (s.downEnd f).comp (s.downEnd f)=s.downEnd (f.comp (s.projector.comp f)) := by
    apply Hom.eq_of_maps <;> intros <;> rfl
  rw [heq,hf',hf]

 theorem SplitIn.primitive_projector_of_id (s : SplitIn B C)
    (h : (Hom.id B).PrimitiveProjector) : s.projector.PrimitiveProjector := by
  constructor
  · apply Hom.eq_of_maps
    · exact s.projector_vertex
    · exact s.projector_edge
  · intro f hf hfp hpf
    have hg := s.downEnd_idempotent f hf hpf
    have hl : (s.downEnd f).comp (Hom.id B)=s.downEnd f := by
      apply Hom.eq_of_maps <;> intros <;> rfl
    have hr : (Hom.id B).comp (s.downEnd f)=s.downEnd f := by
      apply Hom.eq_of_maps <;> intros <;> rfl
    rcases h.2 (s.downEnd f) hg hl hr with hz | he
    · left
      exact (s.lift_down f hfp hpf).symm.trans ((congrArg s.liftEnd hz).trans s.liftEnd_zero)
    · right
      have hi : s.liftEnd (Hom.id B)=s.projector := by
        apply Hom.eq_of_maps <;> intros <;> rfl
      exact (s.lift_down f hfp hpf).symm.trans ((congrArg s.liftEnd he).trans hi)

end
end KLInvariance.MomentGraph.GradedSheaf
end

end OAI
