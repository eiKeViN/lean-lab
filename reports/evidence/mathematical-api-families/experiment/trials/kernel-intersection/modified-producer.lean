module
public import Mathlib
public import ForMathlib.Algebra.Module.Cover.Local
public import ForMathlib.Combinatorics.MomentGraph.Sheaf.Basic
public import ForMathlib.LinearAlgebra.Quotient.Transport

public section

/-! Semantic home: ForMathlib.Combinatorics.MomentGraph.Sheaf.Iso. Source spans: GradedSheaves:7, GradedSheaves:9, GradedSheaves:14.
See migration.json and MIGRATION.md for exact provenance.
Sheaf isomorphisms on graphs and upper sets, transport of sections and images, and local extension across one stalk. -/

namespace OAI

section
namespace KLInvariance.MomentGraph.Sheaf
universe u v w z z'
variable {R : Type u} [CommRing R] {V : Type v} [PartialOrder V]
  {E : Type w} {G : OrderedGraph V E}

structure Iso (B : Sheaf.{u,v,w,z} (R := R) G) (C : Sheaf.{u,v,w,z'} (R := R) G) where
  vertex : ∀ x, B.vertex x ≃ₗ[R] C.vertex x
  edge : ∀ e, B.edge e ≃ₗ[R] C.edge e
  lower : ∀ e v, edge e (B.lower e v) = C.lower e (vertex (G.source e) v)
  upper : ∀ e v, edge e (B.upper e v) = C.upper e (vertex (G.target e) v)

namespace Iso
variable {B : Sheaf.{u,v,w,z} (R := R) G} {C : Sheaf.{u,v,w,z'} (R := R) G}
  (j : Iso B C)

@[expose] def symm : Iso C B where
  vertex x := (j.vertex x).symm
  edge e := (j.edge e).symm
  lower e v := by
    apply (j.edge e).injective
    simp only [LinearEquiv.apply_symm_apply, j.lower]
  upper e v := by
    apply (j.edge e).injective
    simp only [LinearEquiv.apply_symm_apply, j.upper]

@[expose] noncomputable def assignments : B.Assignment ≃ₗ[R] C.Assignment :=
  LinearEquiv.piCongrRight j.vertex

/-- Transport of an assignment is pointwise transport at the vertices. -/
@[simp] theorem assignments_apply (f : B.Assignment) (x : V) :
    j.assignments f x = j.vertex x (f x) := by rfl

@[simp] theorem assignments_symm_apply (f : C.Assignment) (x : V) :
    j.assignments.symm f x = (j.vertex x).symm (f x) := by rfl

theorem compatible_iff (Ω : Set V) (f : B.Assignment) :
    C.CompatibleOn Ω (j.assignments f) ↔ B.CompatibleOn Ω f := by
  constructor <;> intro h e hs ht
  · apply (j.edge e).injective
    rw [j.lower,j.upper]
    simpa only [assignments_apply] using h e hs ht
  · simp only [assignments_apply]
    rw [← j.lower,← j.upper,h e hs ht]

theorem map_sections (Ω : Set V) :
    (B.sections Ω).map j.assignments.toLinearMap = C.sections Ω := by
  ext g
  constructor
  · rintro ⟨f,hf,rfl⟩
    exact (j.compatible_iff Ω f).mpr hf
  · intro hg
    refine ⟨j.assignments.symm g,?_,j.assignments.apply_symm_apply g⟩
    apply (j.compatible_iff Ω _).mp
    change C.CompatibleOn Ω g at hg
    simpa using hg

@[expose] noncomputable def sections (Ω : Set V) : B.sections Ω ≃ₗ[R] C.sections Ω :=
  j.assignments.ofSubmodules _ _ (j.map_sections Ω)

@[simp] theorem sections_val_apply (Ω : Set V) (f : B.sections Ω) (x : V) :
    (j.sections Ω f).val x = j.vertex x (f.val x) := by
  exact j.assignments_apply f.val x

@[expose] noncomputable def boundary (x : V) : B.Boundary x ≃ₗ[R] C.Boundary x :=
  LinearEquiv.piCongrRight (fun e => j.edge e.val)

@[simp] theorem boundary_apply (x : V) (f : B.Boundary x) (e : Outgoing (G := G) x) :
    j.boundary x f e = j.edge e.val (f e) := by rfl

theorem stalkMap (x : V) (v : B.vertex x) :
    j.boundary x (B.stalkMap x v) = C.stalkMap x (j.vertex x v) := by
  funext e
  rcases e with ⟨e,he⟩
  subst x
  rw [boundary_apply]
  exact j.lower e v

theorem boundaryMap (x : V) (f : B.sections (Set.Ioi x)) :
    j.boundary x (B.boundaryMap x f) = C.boundaryMap x (j.sections _ f) := by
  funext e
  rw [boundary_apply]
  change j.edge e.val _ = C.upper e.val ((j.sections _ f).val (G.target e.val))
  rw [sections_val_apply]
  exact j.upper e.val (f.val (G.target e.val))

theorem map_boundaryRange (x : V) :
    (LinearMap.range (B.boundaryMap x)).map (j.boundary x).toLinearMap =
      LinearMap.range (C.boundaryMap x) := by
  ext v
  constructor
  · rintro ⟨w,⟨f,rfl⟩,rfl⟩
    exact ⟨j.sections _ f,(j.boundaryMap x f).symm⟩
  · rintro ⟨f,rfl⟩
    refine ⟨B.boundaryMap x ((j.sections _).symm f),⟨_,rfl⟩,?_⟩
    change j.boundary x (B.boundaryMap x ((j.sections _).symm f)) = _
    rw [j.boundaryMap,LinearEquiv.apply_symm_apply]

end Iso

variable (B : Sheaf.{u,v,w,z} (R := R) G)

@[expose] def upwardKernel (x : V) (F : Set (Outgoing (G := G) x)) : Submodule R (B.vertex x) :=
  ⨅ e : Outgoing (G := G) x, ⨅ (_ : e ∈ F),
    LinearMap.ker ((LinearMap.proj e).comp (B.stalkMap x))

/-- Local kernel constraints, independent of the submodule construction. -/
theorem mem_upwardKernel_iff (x : V) (F : Set (Outgoing (G := G) x)) (v : B.vertex x) :
    v ∈ B.upwardKernel x F ↔ ∀ e ∈ F, B.stalkMap x v e = 0 := by
  simp only [upwardKernel, Submodule.mem_iInf, LinearMap.mem_ker,
    LinearMap.comp_apply, LinearMap.proj_apply]

/-- Imposing every outgoing constraint is the kernel of the full stalk map. -/
theorem upwardKernel_univ (x : V) :
    B.upwardKernel x Set.univ = LinearMap.ker (B.stalkMap x) := by
  ext v
  rw [mem_upwardKernel_iff, LinearMap.mem_ker]
  simp only [Set.mem_univ, true_implies]
  exact ⟨fun h => funext h, fun h e => congrFun h e⟩

namespace Iso
variable {B : Sheaf.{u,v,w,z} (R := R) G} {C : Sheaf.{u,v,w,z'} (R := R) G}
  (j : Iso B C)

theorem upwardKernel_iff (x : V) (F : Set (Outgoing (G := G) x)) (v : B.vertex x) :
    j.vertex x v ∈ C.upwardKernel x F ↔ v ∈ B.upwardKernel x F := by
  simp only [mem_upwardKernel_iff]
  constructor <;> intro h e he
  · apply (j.edge e.val).injective
    rw [map_zero]
    exact (congrFun (j.stalkMap x v) e).trans (h e he)
  · have hh := congrFun (j.stalkMap x v) e
    rw [boundary_apply] at hh
    rw [h e he,map_zero] at hh
    exact hh.symm

theorem map_upwardKernel (x : V) (F : Set (Outgoing (G := G) x)) :
    (B.upwardKernel x F).map (j.vertex x).toLinearMap = C.upwardKernel x F := by
  ext v
  constructor
  · rintro ⟨w,hw,rfl⟩
    exact (j.upwardKernel_iff x F w).mpr hw
  · intro hv
    refine ⟨(j.vertex x).symm v,?_,(j.vertex x).apply_symm_apply v⟩
    apply (j.upwardKernel_iff x F _).mp
    simpa using hv

theorem map_lowerImage (e : E) (F : Set (Outgoing (G := G) (G.source e))) :
    ((B.upwardKernel (G.source e) F).map (B.lower e)).map (j.edge e).toLinearMap =
      (C.upwardKernel (G.source e) F).map (C.lower e) := by
  rw [← Submodule.map_comp]
  have h : (j.edge e).toLinearMap.comp (B.lower e) =
      (C.lower e).comp (j.vertex (G.source e)).toLinearMap := LinearMap.ext (j.lower e)
  rw [h,Submodule.map_comp,j.map_upwardKernel]

theorem map_upperImage (e : E) (F : Set (Outgoing (G := G) (G.target e))) :
    ((B.upwardKernel (G.target e) F).map (B.upper e)).map (j.edge e).toLinearMap =
      (C.upwardKernel (G.target e) F).map (C.upper e) := by
  rw [← Submodule.map_comp]
  have h : (j.edge e).toLinearMap.comp (B.upper e) =
      (C.upper e).comp (j.vertex (G.target e)).toLinearMap := LinearMap.ext (j.upper e)
  rw [h,Submodule.map_comp,j.map_upwardKernel]

end Iso
end KLInvariance.MomentGraph.Sheaf
end


section
namespace KLInvariance.MomentGraph.Sheaf
universe u v w z z'
variable {R : Type u} [CommRing R] {V : Type v} [PartialOrder V]
  {E : Type w} {G : OrderedGraph V E}
  (B : Sheaf.{u,v,w,z} (R := R) G) (C : Sheaf.{u,v,w,z'} (R := R) G) (x : V)

/-- An isomorphism already constructed strictly above `x`, including the edge
modules whose upper endpoints are above `x`. The latter are canonically supplied
by the upper quotient rule in the local decomposition. -/
structure AboveIso where
  vertex : ∀ y, x < y → B.vertex y ≃ₗ[R] C.vertex y
  edge : ∀ e, x < G.target e → B.edge e ≃ₗ[R] C.edge e
  lower : ∀ e (h : x < G.source e) v,
    edge e (h.trans (G.increasing e)) (B.lower e v) =
      C.lower e (vertex (G.source e) h v)
  upper : ∀ e (h : x < G.target e) v,
    edge e h (B.upper e v) = C.upper e (vertex (G.target e) h v)

namespace AboveIso
variable {B C x} (j : AboveIso B C x)

@[expose] def symm : AboveIso C B x where
  vertex y h := (j.vertex y h).symm
  edge e h := (j.edge e h).symm
  lower e h v := by
    apply (j.edge e (h.trans (G.increasing e))).injective
    rw [LinearEquiv.apply_symm_apply,j.lower e h,LinearEquiv.apply_symm_apply]
  upper e h v := by
    apply (j.edge e h).injective
    simp only [LinearEquiv.apply_symm_apply,j.upper]

@[expose] noncomputable def mapAssignment (f : B.Assignment) : C.Assignment :=
by
  classical
  exact fun y => if h : x < y then j.vertex y h (f y) else 0

lemma mapAssignment_at (f : B.Assignment) (y : V) (h : x < y) :
    j.mapAssignment f y = j.vertex y h (f y) := by
  classical
  simp [mapAssignment,h]

lemma compatible (f : B.Assignment) (hf : B.CompatibleOn (Set.Ioi x) f) :
    C.CompatibleOn (Set.Ioi x) (j.mapAssignment f) := by
  intro e hs ht
  change x < G.source e at hs
  change x < G.target e at ht
  rw [j.mapAssignment_at f _ hs,j.mapAssignment_at f _ ht,← j.lower e hs,← j.upper e ht]
  exact congrArg (j.edge e ht) (hf e hs ht)

@[expose] noncomputable def boundary : B.Boundary x ≃ₗ[R] C.Boundary x :=
  LinearEquiv.piCongrRight (fun e => j.edge e.val (lt_of_eq_of_lt e.property.symm (G.increasing e.val)))

lemma boundaryMap (f : B.sections (Set.Ioi x)) :
    j.boundary (B.boundaryMap x f) =
      C.boundaryMap x ⟨j.mapAssignment f.val,j.compatible f.val f.property⟩ := by
  funext e
  change j.edge e.val _ (B.upper e.val (f.val (G.target e.val))) =
    C.upper e.val (j.mapAssignment f.val (G.target e.val))
  rw [j.mapAssignment_at _ _ (lt_of_eq_of_lt e.property.symm (G.increasing e.val)),j.upper]

lemma map_boundaryImage : (B.boundaryImage x).map j.boundary.toLinearMap = C.boundaryImage x := by
  apply le_antisymm
  · rintro v ⟨w,⟨f,rfl⟩,rfl⟩
    exact ⟨⟨j.mapAssignment f.val,j.compatible f.val f.property⟩,(j.boundaryMap f).symm⟩
  · rintro v ⟨f,rfl⟩
    refine ⟨B.boundaryMap x ⟨j.symm.mapAssignment f.val,j.symm.compatible f.val f.property⟩,
      ⟨_,rfl⟩,?_⟩
    funext e
    change j.edge e.val _ (B.upper e.val (j.symm.mapAssignment f.val (G.target e.val))) =
      C.upper e.val (f.val (G.target e.val))
    rw [j.symm.mapAssignment_at _ _ (lt_of_eq_of_lt e.property.symm (G.increasing e.val)),j.upper]
    exact congrArg (C.upper e.val) ((j.vertex _ _).apply_symm_apply _)

lemma map_stalk_image (hBf : B.Flabby) (hBg : B.Generated)
    (hCf : C.Flabby) (hCg : C.Generated) :
    (LinearMap.range (B.stalkMap x)).map j.boundary.toLinearMap =
      LinearMap.range (C.stalkMap x) := by
  rw [B.range_stalkMap_eq_boundaryImage hBf hBg,C.range_stalkMap_eq_boundaryImage hCf hCg]
  exact j.map_boundaryImage

/-- One genuine descending splitting: the finite-free new top summand is
proved from the local-ring minimum cover, and all outgoing restriction maps
commute with the selected edge isomorphisms. -/
theorem extend_stalk [IsLocalRing R]
    [Module.Free R (B.vertex x)] [Module.Finite R (B.vertex x)]
    [Module.Free R (C.vertex x)] [Module.Finite R (C.vertex x)]
    (hBf : B.Flabby) (hBg : B.Generated) (hCf : C.Flabby) (hCg : C.Generated)
    (hmin : LinearMap.ker (C.stalkMap x) ≤
      IsLocalRing.maximalIdeal R • (⊤ : Submodule R (C.vertex x))) :
    ∃ (g : B.vertex x →ₗ[R] C.vertex x)
      (jv : B.vertex x ≃ₗ[R] C.vertex x × LinearMap.ker g),
      Module.Free R (LinearMap.ker g) ∧ Module.Finite R (LinearMap.ker g) ∧
      ∀ (b : B.vertex x) (e : Outgoing (G := G) x),
        j.edge e.val (lt_of_eq_of_lt e.property.symm (G.increasing e.val)) (B.stalkMap x b e) =
          C.stalkMap x (jv b).1 e := by
  let N := LinearMap.range (C.stalkMap x)
  let π : C.vertex x →ₗ[R] N := (C.stalkMap x).rangeRestrict
  have him := j.map_stalk_image hBf hBg hCf hCg
  let φ : B.vertex x →ₗ[R] N := LinearMap.codRestrict N
    (j.boundary.toLinearMap.comp (B.stalkMap x)) (by
      intro b
      change j.boundary (B.stalkMap x b) ∈ LinearMap.range (C.stalkMap x)
      rw [← him]
      exact ⟨B.stalkMap x b,⟨b,rfl⟩,rfl⟩)
  have hφ : Function.Surjective φ := by
    intro n
    have hn : n.val ∈ (LinearMap.range (B.stalkMap x)).map j.boundary.toLinearMap := by
      rw [him]
      exact n.property
    rcases hn with ⟨w,⟨b,rfl⟩,hb⟩
    exact ⟨b,Subtype.ext hb⟩
  have hπmin : LinearMap.ker π ≤ IsLocalRing.maximalIdeal R • (⊤ : Submodule R (C.vertex x)) := by
    intro c hc
    apply hmin
    exact congrArg Subtype.val (LinearMap.mem_ker.mp hc)
  obtain ⟨g,jv,_,hg,hfree,hfinite,hjv⟩ :=
    LocalCover.exists_split_minimal_cover π φ (by intro n; obtain ⟨c,hc⟩ := n.property; exact ⟨c,Subtype.ext hc⟩) hφ hπmin
  refine ⟨g,jv,hfree,hfinite,?_⟩
  intro b e
  have h := congrArg (fun n : N => n.val e) (hjv b).2
  exact h.symm

end AboveIso
end KLInvariance.MomentGraph.Sheaf
end


section
namespace KLInvariance.MomentGraph.Sheaf
universe u v w z z'
variable {R : Type u} [CommRing R] {V : Type v} [PartialOrder V]
  {E : Type w} {G : OrderedGraph V E}
  (B : Sheaf.{u,v,w,z} (R := R) G) (C : Sheaf.{u,v,w,z'} (R := R) G)

 @[expose] def UpperQuotient (α : E → R) : Prop :=
  ∀ e, Function.Surjective (B.upper e) ∧
    ∀ v, B.upper e v = 0 ↔ ∃ w, v = α e • w

@[expose] def castStalkIso {x y : V} (h : x=y) (j : B.vertex x ≃ₗ[R] C.vertex x) :
    B.vertex y ≃ₗ[R] C.vertex y := h ▸ j

structure OnIso (U : Set V) where
  vertex : ∀ x, x ∈ U → B.vertex x ≃ₗ[R] C.vertex x
  edge : ∀ e, G.target e ∈ U → B.edge e ≃ₗ[R] C.edge e
  lower : ∀ e (hs : G.source e ∈ U) (ht : G.target e ∈ U) v,
    edge e ht (B.lower e v) = C.lower e (vertex (G.source e) hs v)
  upper : ∀ e (ht : G.target e ∈ U) v,
    edge e ht (B.upper e v) = C.upper e (vertex (G.target e) ht v)

namespace OnIso
variable {B C} {U : Set V} (j : OnIso B C U)

 @[expose] def above (x : V) (hx : Set.Ioi x ⊆ U) : AboveIso B C x where
  vertex y h := j.vertex y (hx h)
  edge e h := j.edge e (hx h)
  lower e h v := j.lower e (hx h) (hx (h.trans (G.increasing e))) v
  upper e h v := j.upper e (hx h) v

 @[expose] def ofUniv (j : OnIso B C Set.univ) : Iso B C where
  vertex x := j.vertex x (Set.mem_univ x)
  edge e := j.edge e (Set.mem_univ _)
  lower e v := j.lower e (Set.mem_univ _) (Set.mem_univ _) v
  upper e v := j.upper e (Set.mem_univ _) v

/-- Given the new stalk and its outgoing commuting squares, all new incoming
edges are forced by the scalar quotient rule. -/
@[expose] noncomputable def extend (hU : IsUpperSet U) (x : V) (hx : x ∉ U)
    (hmax : Set.Ioi x ⊆ U) (α : E → R)
    (hBq : B.UpperQuotient α) (hCq : C.UpperQuotient α)
    (jv : B.vertex x ≃ₗ[R] C.vertex x)
    (hout : ∀ e (he : G.source e = x) v,
      j.edge e (hmax (lt_of_eq_of_lt he.symm (G.increasing e)))
        (B.lower e v) = C.lower e (castStalkIso B C he.symm jv v)) :
    OnIso B C (insert x U) := by
  classical
  let vj : ∀ y, y ∈ insert x U → B.vertex y ≃ₗ[R] C.vertex y := fun y hy =>
    if h : y = x then castStalkIso B C h.symm jv
    else j.vertex y ((Set.mem_insert_iff.mp hy).resolve_left h)
  have vj_old (y : V) (hy : y ∈ U) : vj y (Set.mem_insert_of_mem x hy) = j.vertex y hy := by
    simp only [vj,dite_eq_right (show y ≠ x from fun h => hx (h ▸ hy))]
  have vj_new : vj x (Set.mem_insert x U) = jv := by simp [vj,castStalkIso]
  let ej : ∀ e, G.target e ∈ insert x U → B.edge e ≃ₗ[R] C.edge e := fun e he =>
    if h : G.target e = x then
      QuotientEdge.iso (B.upper e) (C.upper e) (hBq e).1 (hCq e).1
        (vj (G.target e) he)
        (QuotientEdge.map_kernel_scalar (B.upper e) (C.upper e) (α e)
          (hBq e).2 (hCq e).2 (vj (G.target e) he))
    else j.edge e ((Set.mem_insert_iff.mp he).resolve_left h)
  have ej_old (e : E) (he : G.target e ∈ U) :
      ej e (Set.mem_insert_of_mem x he) = j.edge e he := by
    simp only [ej,dite_eq_right (show G.target e ≠ x from fun h => hx (h ▸ he))]
  refine ⟨vj,ej,?_,?_⟩
  · intro e hs ht v
    have htU : G.target e ∈ U := by
      rcases Set.mem_insert_iff.mp hs with hs | hs
      · exact hmax (lt_of_eq_of_lt hs.symm (G.increasing e))
      · exact hU (G.increasing e).le hs
    rw [ej_old e htU]
    by_cases he : G.source e = x
    · subst x
      rw [vj_new]
      exact hout e rfl v
    · have hsU : G.source e ∈ U := (Set.mem_insert_iff.mp hs).resolve_left he
      rw [vj_old _ hsU]
      exact j.lower e hsU htU v
  · intro e ht v
    by_cases he : G.target e = x
    · simp only [ej,dite_eq_left he]
      exact QuotientEdge.iso_apply _ _ _ _ _ _ v
    · have htU : G.target e ∈ U := (Set.mem_insert_iff.mp ht).resolve_left he
      rw [ej_old e htU,vj_old _ htU]
      exact j.upper e htU v

end OnIso
end KLInvariance.MomentGraph.Sheaf
end

end OAI
