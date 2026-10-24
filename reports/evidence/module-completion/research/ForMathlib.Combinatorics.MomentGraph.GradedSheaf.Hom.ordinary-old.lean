import Lean
import Mathlib
import ForMathlib.Algebra.Module.Graded.ModuleData.QuotientHom
import ForMathlib.Combinatorics.MomentGraph.GradedSheaf.StalkMaps

/-! Semantic home: ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Hom. Source spans: SheafMorphisms:16, SheafMorphisms:20, SheafMorphisms:11, SheafMorphisms:12, SheafMorphisms:23, SheafMorphisms:13, SheafMorphisms:27, SheafMorphisms:14, SheafMorphisms:28.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.MomentGraph.GradedSheaf
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} {V E : Type um} [PartialOrder V]
  {G : OrderedGraph V E}

structure Endomorphism (B : GradedSheaf (𝓐 := 𝓐) G) where
  vertex : ∀ x, ModuleData.Hom (B.vertex x) (B.vertex x)
  edge : ∀ e, ModuleData.Hom (B.edge e) (B.edge e)
  lower : ∀ e v, (edge e).map ((B.lower e).map v) =
    (B.lower e).map ((vertex (G.source e)).map v)
  upper : ∀ e v, (edge e).map ((B.upper e).map v) =
    (B.upper e).map ((vertex (G.target e)).map v)

namespace Endomorphism
variable {B : GradedSheaf (𝓐 := 𝓐) G} (f : Endomorphism B)

 def complement : Endomorphism B where
  vertex x :=
    { map := LinearMap.id - (f.vertex x).map
      graded := fun n v hv => (B.vertex x).piece n |>.sub_mem hv ((f.vertex x).graded n v hv) }
  edge e :=
    { map := LinearMap.id - (f.edge e).map
      graded := fun n v hv => (B.edge e).piece n |>.sub_mem hv ((f.edge e).graded n v hv) }
  lower e v := by
    change (B.lower e).map v - (f.edge e).map ((B.lower e).map v) =
      (B.lower e).map (v-(f.vertex (G.source e)).map v)
    rw [map_sub,f.lower]
  upper e v := by
    change (B.upper e).map v - (f.edge e).map ((B.upper e).map v) =
      (B.upper e).map (v-(f.vertex (G.target e)).map v)
    rw [map_sub,f.upper]

 theorem complement_idempotent (hi : ∀ x v, (f.vertex x).map ((f.vertex x).map v) =
      (f.vertex x).map v) (x : V) (v : B.vertex x) :
    (f.complement.vertex x).map ((f.complement.vertex x).map v) =
      (f.complement.vertex x).map v := by
  change v-(f.vertex x).map v - (f.vertex x).map (v-(f.vertex x).map v) =
    v-(f.vertex x).map v
  rw [map_sub,hi,sub_self,sub_zero]

end Endomorphism
end KLInvariance.MomentGraph.GradedSheaf
end


section
namespace KLInvariance.MomentGraph.GradedSheaf.Endomorphism
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} {V E : Type um} [PartialOrder V]
  {G : OrderedGraph V E} {B : GradedSheaf (𝓐 := 𝓐) G}
  (f : Endomorphism B)

 theorem edge_bijective_of_vertex {α : E → A}
    (hBq : B.forget.UpperQuotient α) (e : E)
    (hv : Function.Bijective (f.vertex (G.target e)).map) :
    Function.Bijective (f.edge e).map := by
  obtain ⟨j,hj⟩ := QuotientEdge.exists_scalar_iso
    (B.upper e).map (B.upper e).map (α e)
    (hBq e).1 (hBq e).1 (hBq e).2 (hBq e).2
    (LinearEquiv.ofBijective (f.vertex (G.target e)).map hv)
  have heq : (f.edge e).map = j.toLinearMap := by
    apply LinearMap.ext
    intro v
    obtain ⟨w,rfl⟩ := (hBq e).1 v
    exact (f.upper e w).trans (hj w).symm
  rw [heq]
  exact j.bijective

end KLInvariance.MomentGraph.GradedSheaf.Endomorphism
end


section
namespace KLInvariance.MomentGraph.GradedSheaf
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} {V E : Type um} [PartialOrder V]
  {G : OrderedGraph V E}

structure Hom (B C : GradedSheaf (𝓐 := 𝓐) G) where
  vertex : ∀ x, ModuleData.Hom (B.vertex x) (C.vertex x)
  edge : ∀ e, ModuleData.Hom (B.edge e) (C.edge e)
  lower : ∀ e v, (edge e).map ((B.lower e).map v) =
    (C.lower e).map ((vertex (G.source e)).map v)
  upper : ∀ e v, (edge e).map ((B.upper e).map v) =
    (C.upper e).map ((vertex (G.target e)).map v)

structure OnHom (B C : GradedSheaf (𝓐 := 𝓐) G) (U : Set V) where
  vertex : ∀ x, x ∈ U → ModuleData.Hom (B.vertex x) (C.vertex x)
  edge : ∀ e, G.target e ∈ U → ModuleData.Hom (B.edge e) (C.edge e)
  lower : ∀ e (hs : G.source e ∈ U) (ht : G.target e ∈ U) v,
    (edge e ht).map ((B.lower e).map v) =
      (C.lower e).map ((vertex (G.source e) hs).map v)
  upper : ∀ e (ht : G.target e ∈ U) v,
    (edge e ht).map ((B.upper e).map v) =
      (C.upper e).map ((vertex (G.target e) ht).map v)

namespace Hom
variable {B C D : GradedSheaf (𝓐 := 𝓐) G}

def comp (g : Hom C D) (f : Hom B C) : Hom B D where
  vertex x := (g.vertex x).comp (f.vertex x)
  edge e := (g.edge e).comp (f.edge e)
  lower e v := by
    change (g.edge e).map ((f.edge e).map ((B.lower e).map v)) = _
    rw [f.lower,g.lower]; rfl
  upper e v := by
    change (g.edge e).map ((f.edge e).map ((B.upper e).map v)) = _
    rw [f.upper,g.upper]; rfl

end Hom

namespace OnHom
variable {B C : GradedSheaf (𝓐 := 𝓐) G} {U : Set V} (j : OnHom B C U)
noncomputable section

 def ofUniv (j : OnHom B C Set.univ) : Hom B C where
  vertex x := j.vertex x (Set.mem_univ x)
  edge e := j.edge e (Set.mem_univ _)
  lower e v := j.lower e (Set.mem_univ _) (Set.mem_univ _) v
  upper e v := j.upper e (Set.mem_univ _) v

 def mapAssignment (x : V) (hx : Set.Ioi x ⊆ U)
    (f : B.forget.Assignment) : C.forget.Assignment := by
  classical
  exact fun y => if h : x < y then (j.vertex y (hx h)).map (f y) else 0

 theorem mapAssignment_at (x : V) (hx : Set.Ioi x ⊆ U)
    (f : B.forget.Assignment) (y : V) (h : x < y) :
    j.mapAssignment x hx f y = (j.vertex y (hx h)).map (f y) := by
  classical
  unfold mapAssignment
  exact dite_eq_left h

 theorem compatible (x : V) (hx : Set.Ioi x ⊆ U)
    (f : B.forget.Assignment) (hf : B.forget.CompatibleOn (Set.Ioi x) f) :
    C.forget.CompatibleOn (Set.Ioi x) (j.mapAssignment x hx f) := by
  intro e hs ht
  change x < G.source e at hs
  change x < G.target e at ht
  rw [j.mapAssignment_at x hx f _ hs,j.mapAssignment_at x hx f _ ht]
  change (C.lower e).map ((j.vertex _ (hx hs)).map (f _)) =
    (C.upper e).map ((j.vertex _ (hx ht)).map (f _))
  exact (j.lower e (hx hs) (hx ht) _).symm.trans
    ((congrArg (j.edge e (hx ht)).map (hf e hs ht)).trans (j.upper e (hx ht) _))

variable [Fintype E]

 def boundary (x : V) (hx : Set.Ioi x ⊆ U) :
    ModuleData.Hom (B.boundary x) (C.boundary x) where
  map := LinearMap.pi fun e =>
    ((j.edge e.val (hx (lt_of_eq_of_lt e.property.symm (G.increasing e.val)))).map).comp
      (LinearMap.proj e)
  graded := by
    intro n v hv e he
    exact (j.edge e.val _).graded n _ (hv e he)

 theorem boundaryMap (x : V) (hx : Set.Ioi x ⊆ U)
    (f : B.forget.sections (Set.Ioi x)) :
    (j.boundary x hx).map (B.forget.boundaryMap x f) =
      C.forget.boundaryMap x ⟨j.mapAssignment x hx f.val,j.compatible x hx f.val f.property⟩ := by
  funext e
  change (j.edge e.val _).map ((B.upper e.val).map (f.val (G.target e.val))) =
    (C.upper e.val).map (j.mapAssignment x hx f.val (G.target e.val))
  rw [j.mapAssignment_at _ _ _ _ (lt_of_eq_of_lt e.property.symm (G.increasing e.val))]
  exact j.upper e.val _ _

 theorem map_stalk_image_le (x : V) (hx : Set.Ioi x ⊆ U)
    (hBf : B.forget.Flabby) (hBg : B.forget.Generated)
    (hCf : C.forget.Flabby) (hCg : C.forget.Generated) :
    (LinearMap.range (B.forget.stalkMap x)).map (j.boundary x hx).map ≤
      LinearMap.range (C.forget.stalkMap x) := by
  rw [B.forget.range_stalkMap_eq_boundaryImage hBf hBg,
    C.forget.range_stalkMap_eq_boundaryImage hCf hCg]
  rintro v ⟨w,⟨f,rfl⟩,rfl⟩
  exact ⟨⟨j.mapAssignment x hx f.val,j.compatible x hx f.val f.property⟩,
    (j.boundaryMap x hx f).symm⟩

variable [DirectSum.Decomposition 𝓐] [SetLike.GradedMonoid 𝓐]
  [IsDomain A] [IsNoetherianRing A]
  (hneg : ∀ n < 0, 𝓐 n = ⊥)
  (hzero : ∀ a ∈ 𝓐 0, ∃ c : k, algebraMap k A c = a)

include hneg hzero in
 theorem extend_stalk (x : V) (hx : Set.Ioi x ⊆ U)
    [Module.Free A (B.vertex x)]
    (hBf : B.forget.Flabby) (hBg : B.forget.Generated)
    (hCf : C.forget.Flabby) (hCg : C.forget.Generated) :
    ∃ f : ModuleData.Hom (B.vertex x) (C.vertex x), ∀ v,
      C.forget.stalkMap x (f.map v) = (j.boundary x hx).map (B.forget.stalkMap x v) := by
  let T := ModuleData.range (C.stalkHom x)
  let f : ModuleData.Hom (B.vertex x) T :=
    { map := LinearMap.codRestrict (LinearMap.range (C.forget.stalkMap x))
        ((j.boundary x hx).map.comp (B.forget.stalkMap x)) (by
          intro v
          exact j.map_stalk_image_le x hx hBf hBg hCf hCg ⟨_,⟨v,rfl⟩,rfl⟩)
      graded := fun n v hv => (j.boundary x hx).graded n _ ((B.stalkHom x).graded n v hv) }
  let π : ModuleData.Hom (C.vertex x) T :=
    { map := (C.forget.stalkMap x).rangeRestrict
      graded := fun n v hv => (C.stalkHom x).graded n v hv }
  have hπ : Function.Surjective π.map := by
    intro v
    obtain ⟨w,hw⟩ := v.property
    exact ⟨w,Subtype.ext hw⟩
  obtain ⟨l,hl⟩ := ModuleData.exists_hom_lift hneg hzero π hπ f
  refine ⟨l,fun v => ?_⟩
  exact congrArg (fun z : T => z.val) (LinearMap.congr_fun hl v)

end
end OnHom
end KLInvariance.MomentGraph.GradedSheaf
end


section
namespace KLInvariance.MomentGraph.GradedSheaf
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} {V E : Type um} [PartialOrder V]
  {G : OrderedGraph V E} {B C : GradedSheaf (𝓐 := 𝓐) G}

 def castVertexHom {x y : V} (h : x=y)
    (f : ModuleData.Hom (B.vertex x) (C.vertex x)) :
    ModuleData.Hom (B.vertex y) (C.vertex y) := h ▸ f

namespace OnHom
variable {U : Set V} (j : OnHom B C U)
noncomputable section

 def extend (hU : IsUpperSet U) (x : V) (hx : x ∉ U)
    (hmax : Set.Ioi x ⊆ U) (α : E → A)
    (hBq : B.UpperQuotient α) (hCq : C.UpperQuotient α)
    (jv : ModuleData.Hom (B.vertex x) (C.vertex x))
    (hout : ∀ e (he : G.source e = x) v,
      (j.edge e (hmax (lt_of_eq_of_lt he.symm (G.increasing e)))).map
        ((B.lower e).map v) =
      (C.lower e).map ((castVertexHom he.symm jv).map v)) :
    OnHom B C (insert x U) := by
  classical
  let vj : ∀ y, y ∈ insert x U → ModuleData.Hom (B.vertex y) (C.vertex y) := fun y hy =>
    if h : y=x then castVertexHom h.symm jv
    else j.vertex y ((Set.mem_insert_iff.mp hy).resolve_left h)
  have vj_old (y : V) (hy : y ∈ U) : vj y (Set.mem_insert_of_mem x hy) = j.vertex y hy := by
    simp only [vj,dite_eq_right (show y ≠ x from fun h => hx (h ▸ hy))]
  have vj_new : vj x (Set.mem_insert x U) = jv := by simp [vj,castVertexHom]
  let ej : ∀ e, G.target e ∈ insert x U → ModuleData.Hom (B.edge e) (C.edge e) := fun e he =>
    if h : G.target e=x then
      ModuleData.quotientHom (B.upper e) (C.upper e) (hBq e).1 (vj (G.target e) he)
        (QuotientEdge.kernel_scalar_le (B.upper e).map (C.upper e).map (α e)
          (hBq e).2 (hCq e).2 (vj (G.target e) he).map)
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
    by_cases he : G.source e=x
    · subst x
      rw [vj_new]
      exact hout e rfl v
    · have hsU : G.source e ∈ U := (Set.mem_insert_iff.mp hs).resolve_left he
      rw [vj_old _ hsU]
      exact j.lower e hsU htU v
  · intro e ht v
    by_cases he : G.target e=x
    · simp only [ej,dite_eq_left he]
      exact ModuleData.quotientHom_apply _ _ _ _ _ v
    · have htU : G.target e ∈ U := (Set.mem_insert_iff.mp ht).resolve_left he
      rw [ej_old e htU,vj_old _ htU]
      exact j.upper e htU v

 theorem extend_vertex_old (hU : IsUpperSet U) (x : V) (hx : x ∉ U)
    (hmax : Set.Ioi x ⊆ U) (α : E → A)
    (hBq : B.UpperQuotient α) (hCq : C.UpperQuotient α)
    (jv : ModuleData.Hom (B.vertex x) (C.vertex x))
    (hout : ∀ e (he : G.source e = x) v,
      (j.edge e (hmax (lt_of_eq_of_lt he.symm (G.increasing e)))).map
        ((B.lower e).map v) =
      (C.lower e).map ((castVertexHom he.symm jv).map v))
    (y : V) (hy : y ∈ U) :
    (j.extend hU x hx hmax α hBq hCq jv hout).vertex y (Set.mem_insert_of_mem x hy) =
      j.vertex y hy := by
  classical
  simp only [extend,dite_eq_right (show y ≠ x from fun h => hx (h ▸ hy))]

 theorem extend_vertex_new (hU : IsUpperSet U) (x : V) (hx : x ∉ U)
    (hmax : Set.Ioi x ⊆ U) (α : E → A)
    (hBq : B.UpperQuotient α) (hCq : C.UpperQuotient α)
    (jv : ModuleData.Hom (B.vertex x) (C.vertex x))
    (hout : ∀ e (he : G.source e = x) v,
      (j.edge e (hmax (lt_of_eq_of_lt he.symm (G.increasing e)))).map
        ((B.lower e).map v) =
      (C.lower e).map ((castVertexHom he.symm jv).map v)) :
    (j.extend hU x hx hmax α hBq hCq jv hout).vertex x (Set.mem_insert x U) = jv := by
  classical
  dsimp only [extend]
  exact dite_eq_left rfl

end
end OnHom
end KLInvariance.MomentGraph.GradedSheaf
end


section
namespace KLInvariance.MomentGraph.GradedSheaf
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} {V E : Type um} [PartialOrder V]
  {G : OrderedGraph V E}
noncomputable section

 def Hom.toEndomorphism {B : GradedSheaf (𝓐 := 𝓐) G} (f : Hom B B) : Endomorphism B :=
  ⟨f.vertex,f.edge,f.lower,f.upper⟩

 def Hom.inverse {B C : GradedSheaf (𝓐 := 𝓐) G} (f : Hom B C)
    (hv : ∀ x, Function.Bijective (f.vertex x).map)
    (he : ∀ e, Function.Bijective (f.edge e).map) : Hom C B where
  vertex x := (f.vertex x).inverse (hv x)
  edge e := (f.edge e).inverse (he e)
  lower e v := by
    apply (he e).1
    rw [(f.edge e).map_inverse]
    rw [f.lower,(f.vertex _).map_inverse]
  upper e v := by
    apply (he e).1
    rw [(f.edge e).map_inverse]
    rw [f.upper,(f.vertex _).map_inverse]

 structure SplitIn (B C : GradedSheaf (𝓐 := 𝓐) G) where
  inclusion : Hom B C
  projection : Hom C B
  vertex_split : ∀ x v, (projection.vertex x).map ((inclusion.vertex x).map v)=v
  edge_split : ∀ e v, (projection.edge e).map ((inclusion.edge e).map v)=v

end
end KLInvariance.MomentGraph.GradedSheaf
end


section
namespace KLInvariance.MomentGraph.GradedSheaf.OnHom
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} [DirectSum.Decomposition 𝓐] [SetLike.GradedMonoid 𝓐]
  [IsDomain A] [IsNoetherianRing A]
  (hneg : ∀ n < 0, 𝓐 n = ⊥)
  (hzero : ∀ a ∈ 𝓐 0, ∃ c : k, algebraMap k A c = a)
  {V E : Type um} [PartialOrder V] [Fintype V] [Fintype E]
  {G : OrderedGraph V E} {B C : GradedSheaf (𝓐 := 𝓐) G}
  (α : E → A) (hBq : B.UpperQuotient α) (hCq : C.UpperQuotient α)
  (hBfree : ∀ x, Module.Free A (B.vertex x))
  (hBf : B.forget.Flabby) (hBg : B.forget.Generated)
  (hCf : C.forget.Flabby) (hCg : C.forget.Generated)
noncomputable section

omit [DirectSum.Decomposition 𝓐] [SetLike.GradedMonoid 𝓐]
  [IsDomain A] [IsNoetherianRing A] [Fintype V] [Fintype E] in
private theorem cast_vertex {U U' : Set V} (h : U=U') (j : OnHom B C U)
    (y : V) (hy : y ∈ U') :
    (h ▸ j).vertex y hy = j.vertex y (h.symm ▸ hy) := by
  subst U'
  rfl

include hneg hzero hBq hCq hBfree hBf hBg hCf hCg in
 theorem exists_extension {U : Set V} (hU : IsUpperSet U) (j : OnHom B C U) :
    ∃ f : Hom B C, ∀ x (hx : x ∈ U), f.vertex x = j.vertex x hx := by
  classical
  have h : ∀ s : Finset V, IsUpperSet ((s : Set V)ᶜ) →
      ∀ j : OnHom B C ((s : Set V)ᶜ),
      ∃ f : Hom B C, ∀ x (hx : x ∈ ((s : Set V)ᶜ)), f.vertex x = j.vertex x hx := by
    intro s
    induction s using Finset.strongInductionOn with
    | _ s ih =>
      intro hU j
      by_cases hs : s=∅
      · subst s
        have heq : ((∅ : Finset V) : Set V)ᶜ=Set.univ := by simp
        let jj : OnHom B C Set.univ := heq ▸ j
        refine ⟨jj.ofUniv,fun y hy => ?_⟩
        exact cast_vertex heq j y (Set.mem_univ y)
      · obtain ⟨x,hxs,hxmax⟩ := s.exists_maximal (Finset.nonempty_iff_ne_empty.mpr hs)
        have hx : x ∉ ((s : Set V)ᶜ) := by simpa using hxs
        have hmax : Set.Ioi x ⊆ ((s : Set V)ᶜ) := by
          intro y hy
          change y ∉ s
          intro hys
          exact (not_le_of_gt hy) (hxmax hys hy.le)
        let := hBfree x
        obtain ⟨l,hl⟩ := j.extend_stalk hneg hzero x hmax hBf hBg hCf hCg
        have hout : ∀ e (he : G.source e=x) v,
            (j.edge e (hmax (lt_of_eq_of_lt he.symm (G.increasing e)))).map
              ((B.lower e).map v) =
            (C.lower e).map ((castVertexHom he.symm l).map v) := by
          intro e he v
          subst x
          exact (congrFun (hl v) ⟨e,rfl⟩).symm
        let jj := j.extend hU x hx hmax α hBq hCq l hout
        have heq : insert x ((s : Set V)ᶜ) = ((s.erase x : Finset V) : Set V)ᶜ := by
          ext y
          simp only [Set.mem_insert_iff,Set.mem_compl_iff,Finset.mem_coe,Finset.mem_erase]
          tauto
        have hU' : IsUpperSet (insert x ((s : Set V)ᶜ)) := by
          intro y t hyt hy
          rcases Set.mem_insert_iff.mp hy with hy | hy
          · subst y
            by_cases htx : t=x
            · exact Set.mem_insert_iff.mpr (Or.inl htx)
            · exact Set.mem_insert_of_mem x (hmax (lt_of_le_of_ne hyt (Ne.symm htx)))
          · exact Set.mem_insert_of_mem x (hU hyt hy)
        obtain ⟨f,hf⟩ := ih (s.erase x) (Finset.erase_ssubset hxs) (heq ▸ hU') (heq ▸ jj)
        refine ⟨f,fun y hy => ?_⟩
        have hy' : y ∈ ((s.erase x : Finset V) : Set V)ᶜ :=
          heq ▸ Set.mem_insert_of_mem x hy
        exact (hf y hy').trans ((cast_vertex heq jj y hy').trans
          (j.extend_vertex_old hU x hx hmax α hBq hCq l hout y hy))
  let s := (Uᶜ).toFinset
  have heq : (s : Set V)ᶜ=U := by simp [s]
  obtain ⟨f,hf⟩ := h s (heq.symm ▸ hU) (heq.symm ▸ j)
  refine ⟨f,fun x hx => ?_⟩
  exact (hf x (heq.symm ▸ hx)).trans (cast_vertex heq.symm j x (heq.symm ▸ hx))

end
end KLInvariance.MomentGraph.GradedSheaf.OnHom
end


section
namespace KLInvariance.MomentGraph.GradedSheaf
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} [DirectSum.Decomposition 𝓐] [SetLike.GradedMonoid 𝓐]
  [IsDomain A] [IsNoetherianRing A]
  {hneg : ∀ n < 0, 𝓐 n = ⊥}
  (hzero : ∀ a ∈ 𝓐 0, ∃ c : k, algebraMap k A c = a)
  {V E : Type um} [PartialOrder V] [Fintype E] {G : OrderedGraph V E}
  {α : E → A} (O : BoundaryModels hneg (G := G) α)
  {B C : GradedSheaf (𝓐 := 𝓐) G}
noncomputable section

include hzero in
 theorem extend_modelSum {U : Set V} (hU : IsUpperSet U)
    (hC : ModelSum O.sheaf U C) (j : OnIso B C U)
    (hBq : B.UpperQuotient α) (hBf : B.forget.Flabby) (hBg : B.forget.Generated)
    (x : V) (hx : x ∉ U) (hmax : Set.Ioi x ⊆ U)
    [Module.Free A (B.vertex x)] :
    ∃ D : GradedSheaf (𝓐 := 𝓐) G,
      ModelSum O.sheaf (insert x U) D ∧ Nonempty (OnIso B D (insert x U)) := by
  classical
  obtain ⟨g,jv,hfree,hjvgrade,hjv⟩ := (j.toOnIso.above x hmax).split_stalk_graded hneg hzero
    (fun e he => j.edge_graded e (hmax he)) inferInstance (hC.free O x)
    hBf hBg (hC.flabby O) (hC.generated O) (hC.minimal O x hx)
  let := hfree
  obtain ⟨n,d,jq0,hjq0⟩ := ModuleData.exists_equiv_shiftedUnits hneg hzero (ModuleData.kernel g)
  let S : GradedSheaf (𝓐 := 𝓐) G := pi (fun i : ULift.{um} (Fin n) => (O.sheaf x).shift (d i))
  let jq1 : ModuleData.pi (fun i : ULift.{um} (Fin n) => (ModuleData.unit hneg).shift (d i))
      ≃ₗ[A] S.vertex x := LinearEquiv.piCongrRight (fun _ => (O.top x).symm)
  have hjq1 (m : ℤ) (v : ModuleData.pi (fun i : ULift.{um} (Fin n) => (ModuleData.unit hneg).shift (d i)))
      (hv : v ∈ (ModuleData.pi (fun i : ULift.{um} (Fin n) => (ModuleData.unit hneg).shift (d i))).piece m) :
      jq1 v ∈ (S.vertex x).piece m := by
    intro i _
    let t : ModuleData.Hom ((O.sheaf x).vertex x) (ModuleData.unit hneg) :=
      ⟨(O.top x).toLinearMap,O.top_graded x⟩
    apply t.mem_of_map_mem (O.top x).injective (m-(d i : ℤ))
    change O.top x ((O.top x).symm (v i)) ∈ (ModuleData.unit hneg).piece (m-(d i : ℤ))
    exact ((O.top x).apply_symm_apply (v i)).symm ▸ hv i (Set.mem_univ i)
  let jq := jq0.trans jq1
  let jv' : B.vertex x ≃ₗ[A] (prod C S).vertex x :=
    jv.trans (LinearEquiv.prodCongr (LinearEquiv.refl A (C.vertex x)) jq)
  have hjv' (m : ℤ) (v : B.vertex x) (hv : v ∈ (B.vertex x).piece m) :
      jv' v ∈ ((prod C S).vertex x).piece m :=
    ⟨(hjvgrade m v hv).1,hjq1 m _ (hjq0 m _ (hjvgrade m v hv).2)⟩
  have hSV (y : V) (hy : y ∈ U) : Subsingleton (S.vertex y) := by
    let := O.support x y (fun hyx => hx (hU hyx hy))
    exact inferInstanceAs (Subsingleton (ULift.{um} (Fin n) → (O.sheaf x).vertex y))
  have hSE (e : E) (he : G.target e ∈ U) : Subsingleton (S.edge e) := by
    let := O.support x (G.target e) (fun h => hx (hU h he))
    let : Subsingleton ((O.sheaf x).edge e) := (O.quotient x e).1.subsingleton
    exact inferInstanceAs (Subsingleton (ULift.{um} (Fin n) → (O.sheaf x).edge e))
  let jj : OnIso B (prod C S) U := j.prodZero S hSV hSE
  have hsum : ModelSum O.sheaf (insert x U) (prod C S) :=
    .add (hC.mono (Set.subset_insert x U)) x (Set.mem_insert x U) n d
  have hout : ∀ e (he : G.source e = x) v,
      jj.edge e (hmax (lt_of_eq_of_lt he.symm (G.increasing e)))
        (B.forget.lower e v) = (prod C S).forget.lower e
          (Sheaf.castStalkIso B.forget (prod C S).forget he.symm jv' v) := by
    intro e he v
    subst x
    apply Prod.ext
    · exact congrFun (hjv v) ⟨e,rfl⟩
    · let := hSE e (hmax (G.increasing e))
      exact Subsingleton.elim _ _
  exact ⟨prod C S,hsum,⟨jj.extend hU x hx hmax α hBq (hsum.quotient O) jv' hjv' hout⟩⟩

end
end KLInvariance.MomentGraph.GradedSheaf
end


section
namespace KLInvariance.MomentGraph.GradedSheaf
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} [DirectSum.Decomposition 𝓐] [SetLike.GradedMonoid 𝓐]
  [IsDomain A] [IsNoetherianRing A]
  (hneg : ∀ n < 0, 𝓐 n = ⊥)
  (hzero : ∀ a ∈ 𝓐 0, ∃ c : k, algebraMap k A c = a)
  {V E : Type um} [PartialOrder V] [Fintype V] [Fintype E]
  {G : OrderedGraph V E} {B C : GradedSheaf (𝓐 := 𝓐) G}
  (α : E → A) (hBq : B.UpperQuotient α) (hCq : C.UpperQuotient α)
  (hBfree : ∀ x, Module.Free A (B.vertex x))
  (hBf : B.forget.Flabby) (hBg : B.forget.Generated)
  (hCf : C.forget.Flabby) (hCg : C.forget.Generated)
  (b : V) (hb : ∀ x, x ≤ b)
noncomputable section

include hneg hzero hBq hCq hBfree hBf hBg hCf hCg hb in
 theorem exists_hom_top (t : ModuleData.Hom (B.vertex b) (C.vertex b)) :
    ∃ f : Hom B C, f.vertex b=t := by
  let je : OnHom B C (∅ : Set V) :=
    { vertex x hx := False.elim hx
      edge e he := False.elim he
      lower e hs := False.elim hs
      upper e ht := False.elim ht }
  have hmax : Set.Ioi b ⊆ (∅ : Set V) := by
    intro x hx
    exact False.elim ((not_lt_of_ge (hb x)) hx)
  have hout : ∀ e (he : G.source e=b) v,
      (je.edge e (hmax (lt_of_eq_of_lt he.symm (G.increasing e)))).map
        ((B.lower e).map v) =
      (C.lower e).map ((castVertexHom he.symm t).map v) := by
    intro e he
    exact False.elim ((not_lt_of_ge (hb (G.target e)))
      (lt_of_eq_of_lt he.symm (G.increasing e)))
  let jj := je.extend isUpperSet_empty b (Set.notMem_empty b) hmax α hBq hCq t hout
  have hU : IsUpperSet (insert b (∅ : Set V)) := by
    intro x y hxy hx
    have hxb : x=b := by simpa using hx
    subst x
    have hyb : y=b := le_antisymm (hb y) hxy
    simpa using hyb
  obtain ⟨f,hf⟩ := jj.exists_extension hneg hzero α hBq hCq hBfree hBf hBg hCf hCg hU
  exact ⟨f,(hf b (Set.mem_insert b _)).trans
    (je.extend_vertex_new isUpperSet_empty b (Set.notMem_empty b) hmax α hBq hCq t hout)⟩

end
end KLInvariance.MomentGraph.GradedSheaf
end


section
namespace KLInvariance.MomentGraph.GradedSheaf
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} [DirectSum.Decomposition 𝓐] [SetLike.GradedMonoid 𝓐]
  [IsDomain A] [IsNoetherianRing A]
  {hneg : ∀ n < 0, 𝓐 n = ⊥}
  (hzero : ∀ a ∈ 𝓐 0, ∃ c : k, algebraMap k A c = a)
  {V E : Type um} [PartialOrder V] [Fintype E] {G : OrderedGraph V E}
  {α : E → A} (O : BoundaryModels hneg (G := G) α)
  (B : GradedSheaf (𝓐 := 𝓐) G)

include hzero in
/-- Finite graded decomposition with actual nonnegative shifts. -/
theorem exists_modelSumIso [Finite V]
    (hBfree : ∀ x, Module.Free A (B.vertex x))
    (hBq : B.UpperQuotient α) (hBf : B.forget.Flabby) (hBg : B.forget.Generated) :
    ∃ C : GradedSheaf (𝓐 := 𝓐) G,
      ModelSum O.sheaf Set.univ C ∧ Nonempty (Iso B C) := by
  classical
  let := Fintype.ofFinite V
  have h : ∀ s : Finset V, IsUpperSet ((s : Set V)ᶜ) →
      ∀ C : GradedSheaf (𝓐 := 𝓐) G,
      ModelSum O.sheaf ((s : Set V)ᶜ) C → OnIso B C ((s : Set V)ᶜ) →
      ∃ D : GradedSheaf (𝓐 := 𝓐) G,
        ModelSum O.sheaf Set.univ D ∧ Nonempty (Iso B D) := by
    intro s
    induction s using Finset.strongInductionOn with
    | _ s ih =>
      intro hU C hC j
      by_cases hs : s = ∅
      · subst s
        have hh : ((∅ : Finset V) : Set V)ᶜ = Set.univ := by simp
        exact ⟨C,hh ▸ hC,⟨OnIso.ofUniv (hh ▸ j)⟩⟩
      · obtain ⟨x,hxs,hxmax⟩ := s.exists_maximal (Finset.nonempty_iff_ne_empty.mpr hs)
        have hx : x ∉ ((s : Set V)ᶜ) := by simpa using hxs
        have hmax : Set.Ioi x ⊆ ((s : Set V)ᶜ) := by
          intro y hy
          change y ∉ s
          intro hys
          exact (not_le_of_gt hy) (hxmax hys hy.le)
        let := hBfree x
        obtain ⟨D,hD,⟨jj⟩⟩ := extend_modelSum hzero O hU hC j hBq hBf hBg x hx hmax
        have heq : insert x ((s : Set V)ᶜ) = ((s.erase x : Finset V) : Set V)ᶜ := by
          ext y
          simp only [Set.mem_insert_iff,Set.mem_compl_iff,Finset.mem_coe,Finset.mem_erase]
          tauto
        have hU' : IsUpperSet (insert x ((s : Set V)ᶜ)) := by
          intro y t hyt hy
          rcases Set.mem_insert_iff.mp hy with hy | hy
          · subst y
            by_cases htx : t=x
            · exact Set.mem_insert_iff.mpr (Or.inl htx)
            · exact Set.mem_insert_of_mem x (hmax (lt_of_le_of_ne hyt (Ne.symm htx)))
          · exact Set.mem_insert_of_mem x (hU hyt hy)
        exact ih (s.erase x) (Finset.erase_ssubset hxs) (heq ▸ hU') D (heq ▸ hD) (heq ▸ jj)
  have hset : ((Finset.univ : Finset V) : Set V)ᶜ = ∅ := by simp
  have hj : OnIso B zero (∅ : Set V) :=
    ⟨⟨fun x hx => False.elim hx,fun e he => False.elim he,
      fun e hs => False.elim hs,fun e ht => False.elim ht⟩,
      fun x hx => False.elim hx,fun e he => False.elim he⟩
  have hinit := h Finset.univ
  rw [hset] at hinit
  exact hinit isUpperSet_empty zero .zero hj

end KLInvariance.MomentGraph.GradedSheaf
end

end OAI

open Lean
namespace BoundaryCodec
partial def nameJson : Name → Json
  | .anonymous => Json.arr #[]
  | .str p s => toJson (#[nameJson p, toJson s])
  | .num p n => toJson (#[nameJson p, toJson n, Json.null])
partial def levelJson : Level → Json
  | .zero => toJson (#[toJson "zero"])
  | .succ u => toJson (#[toJson "succ", levelJson u])
  | .max u v => toJson (#[toJson "max", levelJson u, levelJson v])
  | .imax u v => toJson (#[toJson "imax", levelJson u, levelJson v])
  | .param n => toJson (#[toJson "param", nameJson n])
  | .mvar _ => panic! "unclosed level"
structure Dump where
  ids : ExprStructMap Nat := {}
  nodes : Array Json := #[]
partial def encode (e : Expr) : StateM Dump Nat := do
  if let .mdata _ b := e then return ← encode b
  if let some i := (← get).ids[ExprStructEq.mk e]? then return i
  let node : Array Json ← match e with
    | .bvar n => pure #[toJson "bvar", toJson n]
    | .sort u => pure #[toJson "sort", levelJson u]
    | .const n us => pure #[toJson "const", nameJson n, toJson (us.map levelJson)]
    | .app f a => do pure #[toJson "app", toJson (← encode f), toJson (← encode a)]
    | .lam n t b bi | .forallE n t b bi => do
      let tag := if e.isLambda then "lam" else "forall"
      let bi := match bi with | .default => 0 | .implicit => 1 | .strictImplicit => 2 | .instImplicit => 3
      pure #[toJson tag, nameJson n, toJson (← encode t), toJson (← encode b), toJson bi]
    | .letE n t v b nondep => do pure #[toJson "let", nameJson n, toJson (← encode t), toJson (← encode v), toJson (← encode b), toJson nondep]
    | .lit (.natVal n) => pure #[toJson "nat", toJson n]
    | .lit (.strVal s) => pure #[toJson "str", toJson s]
    | .proj n i b => do pure #[toJson "proj", nameJson n, toJson i, toJson (← encode b)]
    | _ => panic! "unclosed expression"
  let s ← get
  set ({ids := s.ids.insert (ExprStructEq.mk e) s.nodes.size, nodes := s.nodes.push (toJson node)} : Dump)
  return s.nodes.size
partial def readName (j : Json) : Except String Name := do
  let a ← j.getArr?
  if a.isEmpty then return .anonymous
  if a.size == 2 then return .str (← readName a[0]!) (← a[1]!.getStr?)
  if a.size == 3 then return .num (← readName a[0]!) (← fromJson? a[1]!)
  throw "bad name"
partial def readLevel (j : Json) : Except String Level := do
  let a ← j.getArr?
  match ← a[0]!.getStr? with
  | "zero" => do pure (.zero)
  | "succ" => do pure (.succ (← readLevel a[1]!))
  | "max" => do pure (.max (← readLevel a[1]!) (← readLevel a[2]!))
  | "imax" => do pure (.imax (← readLevel a[1]!) (← readLevel a[2]!))
  | "param" => do pure (.param (← readName a[1]!))
  | _ => throw "bad level"
def decode (nodes : Array Json) : Except String (Array Expr) := do
  let mut es := #[]
  for j in nodes do
    let a ← j.getArr?
    let child := fun (i : Nat) => (show Except String Expr from do
      let n : Nat ← fromJson? a[i]!
      if n < es.size then return es[n]! else throw "non-topological DAG")
    let e : Expr ← match ← a[0]!.getStr? with
      | "bvar" => do pure (.bvar (← fromJson? a[1]!))
      | "sort" => do pure (.sort (← readLevel a[1]!))
      | "const" => do pure (.const (← readName a[1]!) (← (← a[2]!.getArr?).toList.mapM readLevel))
      | "app" => do pure (.app (← child 1) (← child 2))
      | "lam" | "forall" => do
        let bi : Nat ← fromJson? a[4]!
        let bi ← match bi with | 0 => pure BinderInfo.default | 1 => pure .implicit | 2 => pure .strictImplicit | 3 => pure .instImplicit | _ => throw "bad binder"
        if (← a[0]!.getStr?) == "lam" then pure (.lam (← readName a[1]!) (← child 2) (← child 3) bi)
        else pure (.forallE (← readName a[1]!) (← child 2) (← child 3) bi)
      | "let" => do pure (.letE (← readName a[1]!) (← child 2) (← child 3) (← child 4) (← fromJson? a[5]!))
      | "nat" => do pure (.lit (.natVal (← fromJson? a[1]!)))
      | "str" => do pure (.lit (.strVal (← fromJson? a[1]!)))
      | "proj" => do pure (.proj (← readName a[1]!) (← fromJson? a[2]!) (← child 3))
      | _ => throw "bad expression"
    es := es.push e
  return es
end BoundaryCodec

open Lean Meta Elab Command BoundaryCodec
run_elab do
  let names : Array Name := #[`OAI.KLInvariance.MomentGraph.GradedSheaf.OnHom.extend.eq_1]
  let env := (← Lean.getEnv).setExporting false
  let mut dump : BoundaryCodec.Dump := {}
  let mut records : Array Json := #[]
  let mut aux : Array Json := #[]
  let mut pending : Array Name := names
  let mut seen : Array Name := #[]
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    if seen.contains n then continue
    seen := seen.push n
    let some ci := env.find? n | throwError "old name missing {n}"
    let (ti, ds) := (BoundaryCodec.encode ci.type).run dump
    dump := ds
    if names.contains n then
      records := records.push (Json.arr #[BoundaryCodec.nameJson n, toJson (ci.levelParams.map BoundaryCodec.nameJson), toJson ti])
    let visit := fun (e : Expr) => e.foldConsts #[] fun n ns =>
      if n.toString.contains "_proof_" || n.toString.contains "match_" then ns.push n else ns
    pending := pending ++ visit ci.type
    if n.toString.contains "_proof_" || n.toString.contains "match_" then
      let some v := ci.value? (allowOpaque := true) | continue
      pending := pending ++ visit v
      let (vi, ds) := (BoundaryCodec.encode v).run dump
      dump := ds
      aux := aux.push (Json.arr #[BoundaryCodec.nameJson n, toJson (ci.levelParams.map BoundaryCodec.nameJson), toJson ti, toJson vi, toJson (match ci with | .thmInfo _ => "theorem" | _ => "def")])
  IO.FS.writeFile "/workspace/lean-lab/results/matcher-compat/ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Hom.ordinary-old.json" ((Json.mkObj [("nodes",toJson dump.nodes),("records",toJson records),("aux",toJson aux)]).compress)
  IO.println s!"Captured {records.size} actual old types and {aux.size} helper declarations."

open Lean

structure TypeDumpState where
  ids : ExprStructMap Nat := {}
  proofIds : ExprStructMap Nat := {}
  next : Nat := 0
  privateOwners : Std.HashMap Name Name := {}
  proofAliases : NameHashSet := {}
  unrenamed : NameHashSet := {}

-- Alpha equivalence ignores binder display names. Only compiler-private OAI
-- owner prefixes are erased from constant names; their user names stay exact.
-- There are no duplicate private user names in the pinned source.
private def canonicalConstant (n : Name) : Name :=
  if n.toString.startsWith "_private.OAI." then
    (privateToUserName? n).getD n
  else n

-- Keep every mathematical expression constructor, universe, binder info,
-- constant, application and de Bruijn index. Metadata and binder display names
-- have no effect on the mathematical type. A local compiler theorem auxiliary
-- is represented by its full proposition, using kernel proof irrelevance.
-- No proof body, general definition, data instance or user theorem is unfolded.
partial def dumpType (env : Environment) (out : IO.FS.Handle) (e : Expr)
    (proofContext := false) : StateT TypeDumpState IO Nat := do
  let cached : TypeDumpState ← get
  let cache := if proofContext then cached.proofIds else cached.ids
  if let some id := cache[ExprStructEq.mk e]? then return id
  if let .mdata _ body := e then return ← dumpType env out body proofContext
  let fields ← match e with
    | .bvar i => pure ["bvar", toString i]
    | .sort u => pure ["sort", reprStr u]
    | .const n us =>
      let proofName := match n with
        | .str _ s => s.startsWith "_proof_"
        | _ => false
      if n.isInternal && n.toString.startsWith "OAI." && proofName then
        if let some (.thmInfo info) := env.find? n then
          -- Kernel theorem declarations prove propositions. Their full
          -- proposition, including parameters, is retained; only its binder
          -- display/implicitness metadata is irrelevant to the proof value.
          let proposition ← dumpType env out (info.type.instantiateLevelParams info.levelParams us) true
          modify fun st => { st with proofAliases := st.proofAliases.insert n }
          pure ["proof", toString proposition]
        else pure ["const", reprStr n, reprStr us]
      else
        let canonical := canonicalConstant n
        if canonical != n then
          if env.contains canonical then
            throw <| IO.userError "Private canonical name collides with an unrenamed global constant"
          if let some previous := (← get).privateOwners[canonical]? then
            if previous != n then throw <| IO.userError "Ambiguous private type constant"
          modify fun st => { st with privateOwners := st.privateOwners.insert canonical n }
        pure ["const", reprStr canonical, reprStr us]
    | .app f a => do
      let f ← dumpType env out f proofContext; let a ← dumpType env out a proofContext
      pure ["app", toString f, toString a]
    | .lam _ t b bi | .forallE _ t b bi => do
      let t ← dumpType env out t proofContext; let b ← dumpType env out b proofContext
      pure [if e.isLambda then "lam" else "forall", "_", if proofContext then "kernel" else reprStr bi, toString t, toString b]
    | .letE _ t v b nondep => do
      let t ← dumpType env out t proofContext; let v ← dumpType env out v proofContext; let b ← dumpType env out b proofContext
      pure ["let", "_", toString t, toString v, toString b, toString nondep]
    | .lit v => pure ["lit", reprStr v]
    | .proj n i b => do
      let b ← dumpType env out b proofContext
      pure ["proj", reprStr n, toString i, toString b]
    | .fvar _ | .mvar _ => throw <| IO.userError "Non-closed declaration type"
    | .mdata _ _ => unreachable!
  match e with
  | .const n _ =>
    if fields.head! == "const" && canonicalConstant n == n then
      modify fun st => { st with unrenamed := st.unrenamed.insert n }
  | .proj n _ _ => modify fun st => { st with unrenamed := st.unrenamed.insert n }
  | _ => pure ()
  let state : TypeDumpState ← get
  if proofContext then
    set { state with proofIds := state.proofIds.insert (ExprStructEq.mk e) state.next, next := state.next+1 }
  else
    set { state with ids := state.ids.insert (ExprStructEq.mk e) state.next, next := state.next+1 }
  out.putStrLn s!"NODE\t{state.next}\t{(toJson fields).compress}"
  return state.next

private def declarationKind : ConstantInfo → String
  | .axiomInfo _ => "axiom" | .defnInfo _ => "def"
  | .thmInfo _ => "theorem" | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient" | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor" | .recInfo _ => "recursor"

-- This experiment accepts duplicate serialized theorem records only.
-- Other ConstantInfo variants fail closed; their safety/hints are not omitted
-- from a purported full-record comparison. ExprStructEq retains binder names
-- and annotations, unlike BEq Expr (Expr.eqv).
private def sameSerializedTheorem (a b : ConstantInfo) : Bool :=
  match a, b with
  | .thmInfo a, .thmInfo b =>
    a.name == b.name && a.levelParams == b.levelParams &&
      ExprStructEq.mk a.type == ExprStructEq.mk b.type &&
      ExprStructEq.mk a.value == ExprStructEq.mk b.value && a.all == b.all
  | _, _ => false


run_elab do
  let env := (← Lean.getEnv).setExporting false
  let out ← IO.FS.Handle.mk "/workspace/lean-lab/results/matcher-compat/ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Hom.ordinary-old.tsv" .write
  let action : StateT TypeDumpState IO Unit := do
    out.putStrLn "FORMAT\tkl-public-types-v3"
    for n in #[`OAI.KLInvariance.MomentGraph.GradedSheaf.OnHom.extend.eq_1] do
      let some ci := env.find? n | throw <| IO.userError "missing selected old name"
      out.putStrLn "MODULE\tForMathlib.Combinatorics.MomentGraph.GradedSheaf.Hom"
      let id ← dumpType env out ci.type
      out.putStrLn s!"TYPE\t{n}\t{(toJson (reprStr ci.levelParams)).compress}\t{id}\t{declarationKind ci}"
    let st ← get
    for n in st.proofAliases.toArray do out.putStrLn s!"PROOF_ALIAS\t{n}"
    out.putStrLn s!"PRIVATE_SUMMARY\t{st.privateOwners.size}\t{st.unrenamed.size}\t0\t0"
    out.putStrLn s!"SUMMARY\t1\t0\t{st.proofAliases.size}"
  discard <| action.run {}
  out.flush
