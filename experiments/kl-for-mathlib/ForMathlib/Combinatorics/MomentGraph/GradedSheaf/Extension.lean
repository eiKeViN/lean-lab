import Mathlib
import ForMathlib.Algebra.Module.Graded.Hilbert.Series
import ForMathlib.Algebra.Module.Graded.ModuleData.Transport
import ForMathlib.Combinatorics.MomentGraph.Boundary.Basic
import ForMathlib.Combinatorics.MomentGraph.Sheaf.Products
import ForMathlib.Combinatorics.MomentGraph.Sheaf.Pullback

/-! Semantic home: ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Extension. Source spans: MinimalExtensions:1, MinimalExtensions:2, MinimalExtensions:3, MinimalExtensions:5, MinimalExtensions:10, MinimalExtensions:23, MinimalExtensions:9, MinimalExtensions:11, MinimalExtensions:12.
See migration.json and MIGRATION.md for exact provenance.
Graded lower-extension and pullback constructions, graded stalk-isomorphism lifting and the associated boundary-model family. -/

namespace OAI

section
namespace KLInvariance.MomentGraph.GradedSheaf
open _root_.OAI.KLInvariance.Graded _root_.OAI.KLInvariance.Hilbert
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} {V E : Type um} [PartialOrder V]
  {G : OrderedGraph V E} (B : GradedSheaf (𝓐 := 𝓐) G)

/-- The actual lower restriction, with its source explicitly identified. -/
def lowerAt (x : V) (e : Sheaf.Outgoing (G := G) x) :
    ModuleData.Hom (B.vertex x) (B.edge e.val) := by
  rcases e with ⟨e,rfl⟩
  exact B.lower e

 theorem lowerAt_map (x : V) (e : Sheaf.Outgoing (G := G) x) (v : B.vertex x) :
    (B.lowerAt x e).map v = B.forget.stalkMap x v e := by
  rcases e with ⟨e,rfl⟩
  rfl

/-- The same kernel, typed in the graded stalk so base-field instances are explicit. -/
def upwardSubmodule (x : V) (F : Set (Sheaf.Outgoing (G := G) x)) :
    Submodule A (B.vertex x) := B.forget.upwardKernel x F

 theorem upwardKernel_homogeneous (x : V) (F : Set (Sheaf.Outgoing (G := G) x)) :
    ∀ n v, v ∈ B.upwardSubmodule x F →
      component (B.vertex x).piece n v ∈ B.upwardSubmodule x F := by
  intro n v hv e he
  rw [← B.lowerAt_map]
  rw [← (B.lowerAt x e).component]
  rw [B.lowerAt_map,hv e he]
  exact map_zero (component (B.edge e.val).piece n)

noncomputable def upwardKernel [IsNoetherianRing A]
    (x : V) (F : Set (Sheaf.Outgoing (G := G) x)) : ModuleData.{uk,ua,um} 𝓐 :=
  ModuleData.sub (B.vertex x) (B.upwardSubmodule x F) (B.upwardKernel_homogeneous x F)

 theorem upwardKernel_insert (x : V) (F : Set (Sheaf.Outgoing (G := G) x))
    (e : Sheaf.Outgoing (G := G) x) :
    B.upwardSubmodule x (insert e F) =
      B.upwardSubmodule x F ⊓ LinearMap.ker (B.lowerAt x e).map := by
  ext v
  change (∀ a ∈ insert e F, B.forget.stalkMap x v a = 0) ↔
    (∀ a ∈ F, B.forget.stalkMap x v a = 0) ∧ (B.lowerAt x e).map v = 0
  rw [B.lowerAt_map]
  simp only [Set.mem_insert_iff,forall_eq_or_imp]
  exact and_comm


 theorem hilbert_edge_increment
    (x : V) (F : Set (Sheaf.Outgoing (G := G) x))
    (e : Sheaf.Outgoing (G := G) x)
    [∀ n, Module.Finite k ((B.vertex x).piece n)]
    {q : ℝ} (hq : 0 < q)
    (hs : Summable (term (B.vertex x).piece
      ((B.upwardSubmodule x F).restrictScalars k) q)) :
    value (B.vertex x).piece ((B.upwardSubmodule x F).restrictScalars k) q =
      value (B.vertex x).piece
        ((B.upwardSubmodule x (insert e F)).restrictScalars k) q +
      value (B.edge e.val).piece
        (((B.upwardSubmodule x F).map (B.lowerAt x e).map).restrictScalars k) q := by
  rw [B.upwardKernel_insert]
  exact value_image_exact (B.vertex x).piece (B.edge e.val).piece
    (B.upwardSubmodule x F) (B.upwardKernel_homogeneous x F)
    (B.lowerAt x e).map (B.lowerAt x e).graded hq hs

end KLInvariance.MomentGraph.GradedSheaf
end


section
namespace KLInvariance.MomentGraph.GradedSheaf
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} {V E : Type um} [PartialOrder V]
  {G : OrderedGraph V E} [Fintype V] [Fintype E]
  (B : GradedSheaf (𝓐 := 𝓐) G)

noncomputable def stalkHom (x : V) : ModuleData.Hom (B.vertex x) (B.boundary x) where
  map := B.forget.stalkMap x
  graded := by
    intro n v hv e _
    change B.forget.stalkMap x v e ∈ (B.edge e.val).piece n
    rw [← B.lowerAt_map]
    exact (B.lowerAt x e).graded n v hv

end KLInvariance.MomentGraph.GradedSheaf
end


section
namespace KLInvariance.MomentGraph.Sheaf.AboveIso
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} [DirectSum.Decomposition 𝓐] [SetLike.GradedMonoid 𝓐]
  {V E : Type um} [PartialOrder V] {G : OrderedGraph V E}
  [Fintype E] [IsNoetherianRing A] [IsDomain A]
  (hneg : ∀ n < 0, 𝓐 n = ⊥)
  (hzero : ∀ a ∈ 𝓐 0, ∃ c : k, algebraMap k A c = a)
  {B C : GradedSheaf (𝓐 := 𝓐) G} {x : V}
  (j : AboveIso B.forget C.forget x)

include hneg hzero in
 theorem extend_stalk_graded
    (hj : ∀ e (h : x < G.target e) n v, v ∈ (B.edge e).piece n →
      j.edge e h v ∈ (C.edge e).piece n)
    (hBfree : Module.Free A (B.vertex x)) (hCfree : Module.Free A (C.vertex x))
    (hBf : B.forget.Flabby) (hBg : B.forget.Generated)
    (hCf : C.forget.Flabby) (hCg : C.forget.Generated)
    (hBmin : B.KernelMinimal x) (hCmin : C.KernelMinimal x) :
    ∃ e : B.vertex x ≃ₗ[A] C.vertex x,
      (∀ n v, v ∈ (B.vertex x).piece n → e v ∈ (C.vertex x).piece n) ∧
      ∀ v, j.boundary (B.forget.stalkMap x v) = C.forget.stalkMap x (e v) := by
  let T := ModuleData.range (C.stalkHom x)
  let f : ModuleData.Hom (B.vertex x) T :=
    { map := LinearMap.codRestrict (LinearMap.range (C.forget.stalkMap x))
        (j.boundary.toLinearMap.comp (B.forget.stalkMap x)) (by
          intro v
          rw [← j.map_stalk_image hBf hBg hCf hCg]
          exact ⟨B.forget.stalkMap x v,⟨v,rfl⟩,rfl⟩)
      graded := by
        intro n v hv e _
        exact hj e.val _ n _ ((B.stalkHom x).graded n v hv e (Set.mem_univ e)) }
  let g : ModuleData.Hom (C.vertex x) T :=
    { map := (C.forget.stalkMap x).rangeRestrict
      graded := fun n v hv => (C.stalkHom x).graded n v hv }
  have hfs : Function.Surjective f.map := by
    intro v
    have hv : v.val ∈ (LinearMap.range (B.forget.stalkMap x)).map j.boundary.toLinearMap := by
      rw [j.map_stalk_image hBf hBg hCf hCg]
      exact v.property
    obtain ⟨w,⟨z,rfl⟩,hz⟩ := hv
    exact ⟨z,Subtype.ext hz⟩
  have hgs : Function.Surjective g.map := by
    intro v
    obtain ⟨w,hw⟩ := v.property
    exact ⟨w,Subtype.ext hw⟩
  have hfm : LinearMap.ker f.map ≤ positiveIdeal 𝓐 • (⊤ : Submodule A (B.vertex x)) := by
    intro v hv
    apply (B.kernelMinimal_iff x).mp hBmin
    apply LinearMap.mem_ker.mpr
    apply j.boundary.injective
    rw [map_zero]
    have hh : f.map v = 0 := LinearMap.mem_ker.mp hv
    exact congrArg (fun z : T => z.val) hh
  have hgm : LinearMap.ker g.map ≤ positiveIdeal 𝓐 • (⊤ : Submodule A (C.vertex x)) := by
    intro v hv
    apply (C.kernelMinimal_iff x).mp hCmin
    have hh : g.map v = 0 := LinearMap.mem_ker.mp hv
    exact congrArg (fun z : T => z.val) hh
  let F : ModuleData.MinimalCover T := ⟨B.vertex x,hBfree,f,hfs,hfm⟩
  let D : ModuleData.MinimalCover T := ⟨C.vertex x,hCfree,g,hgs,hgm⟩
  obtain ⟨e,he,hef⟩ := ModuleData.MinimalCover.equiv hneg hzero F D
  refine ⟨e,he,?_⟩
  intro v
  exact (congrArg Subtype.val (LinearMap.congr_fun hef v)).symm

end KLInvariance.MomentGraph.Sheaf.AboveIso
end


section
namespace KLInvariance.MomentGraph.GradedSheaf
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} {V E : Type um} [PartialOrder V]
  {G : OrderedGraph V E}

structure Iso (B C : GradedSheaf (𝓐 := 𝓐) G) extends Sheaf.Iso B.forget C.forget where
  vertex_graded : ∀ x n v, v ∈ (B.vertex x).piece n → vertex x v ∈ (C.vertex x).piece n
  edge_graded : ∀ e n v, v ∈ (B.edge e).piece n → edge e v ∈ (C.edge e).piece n

structure OnIso (B C : GradedSheaf (𝓐 := 𝓐) G) (U : Set V)
    extends Sheaf.OnIso B.forget C.forget U where
  vertex_graded : ∀ x (hx : x ∈ U) n v,
    v ∈ (B.vertex x).piece n → vertex x hx v ∈ (C.vertex x).piece n
  edge_graded : ∀ e (he : G.target e ∈ U) n v,
    v ∈ (B.edge e).piece n → edge e he v ∈ (C.edge e).piece n

namespace OnIso
variable {B C : GradedSheaf (𝓐 := 𝓐) G} {U : Set V} (j : OnIso B C U)

 def ofUniv (j : OnIso B C Set.univ) : Iso B C where
  toIso := j.toOnIso.ofUniv
  vertex_graded x := j.vertex_graded x (Set.mem_univ x)
  edge_graded e := j.edge_graded e (Set.mem_univ _)

noncomputable def extend (hU : IsUpperSet U) (x : V) (hx : x ∉ U)
    (hmax : Set.Ioi x ⊆ U) (α : E → A)
    (hBq : B.UpperQuotient α) (hCq : C.UpperQuotient α)
    (jv : B.vertex x ≃ₗ[A] C.vertex x)
    (hjv : ∀ n v, v ∈ (B.vertex x).piece n → jv v ∈ (C.vertex x).piece n)
    (hout : ∀ e (he : G.source e = x) v,
      j.edge e (hmax (lt_of_eq_of_lt he.symm (G.increasing e)))
        (B.forget.lower e v) = C.forget.lower e (Sheaf.castStalkIso B.forget C.forget he.symm jv v)) :
    OnIso B C (insert x U) := by
  classical
  let p := j.toOnIso.extend hU x hx hmax α hBq hCq jv hout
  have hvp : ∀ y (hy : y ∈ insert x U) n v,
      v ∈ (B.vertex y).piece n → p.vertex y hy v ∈ (C.vertex y).piece n := by
    intro y hy n v hv
    dsimp only [p,Sheaf.OnIso.extend]
    split_ifs with h
    · subst y
      exact hjv n v hv
    · exact j.vertex_graded y _ n v hv
  refine ⟨p,hvp,?_⟩
  intro e he n v hv
  dsimp only [p,Sheaf.OnIso.extend]
  split_ifs with h
  · apply ModuleData.quotient_iso_graded (B.upper e) (C.upper e) (hBq e).1 (hCq e).1
    · subst x
      exact hjv
    · exact hv
  · exact j.edge_graded e _ n v hv

end OnIso
end KLInvariance.MomentGraph.GradedSheaf
end


section
namespace KLInvariance.MomentGraph
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} {V E : Type um} [PartialOrder V]
  (G : OrderedGraph V E) (K : Set V) (hK : IsLowerSet K)

 def lowerGraph : OrderedGraph K {e : E // G.target e ∈ K} where
  source e := ⟨G.source e.val,hK (G.increasing e.val).le e.property⟩
  target e := ⟨G.target e.val,e.property⟩
  increasing e := G.increasing e.val

namespace GradedSheaf
noncomputable section
attribute [local instance] Classical.propDecidable

abbrev Witness (p : Prop) := ULift.{um} (PLift p)

variable {G K hK} (B : GradedSheaf (𝓐 := 𝓐) (lowerGraph G K hK))

 def lowerExtend : GradedSheaf (𝓐 := 𝓐) G where
  vertex x := ModuleData.pi (fun h : Witness.{um} (x ∈ K) => B.vertex ⟨x,h.down.down⟩)
  edge e := ModuleData.pi (fun h : Witness.{um} (G.target e ∈ K) => B.edge ⟨e,h.down.down⟩)
  lower e :=
    { map := LinearMap.pi (fun h => (B.lower ⟨e,h.down.down⟩).map.comp
        (LinearMap.proj ⟨⟨hK (G.increasing e).le h.down.down⟩⟩))
      graded n _v hv h _ := (B.lower ⟨e,h.down.down⟩).graded n _ (hv _ (Set.mem_univ _)) }
  upper e :=
    { map := LinearMap.pi (fun h => (B.upper ⟨e,h.down.down⟩).map.comp (LinearMap.proj h))
      graded n _v hv h _ := (B.upper ⟨e,h.down.down⟩).graded n _ (hv _ (Set.mem_univ _)) }

 def lowerExtendVertex (x : K) : (B.lowerExtend.vertex x.val) ≃ₗ[A] B.vertex x where
  toFun f := f ⟨⟨x.property⟩⟩
  invFun v _ := v
  left_inv f := by
    funext h
    rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

 theorem lowerExtendVertex_graded (x : K) (n : ℤ) (v : B.lowerExtend.vertex x.val)
    (hv : v ∈ (B.lowerExtend.vertex x.val).piece n) :
    B.lowerExtendVertex x v ∈ (B.vertex x).piece n := hv _ (Set.mem_univ _)

 theorem lowerExtend_support (x : V) (hx : x ∉ K) : Subsingleton (B.lowerExtend.vertex x) :=
  ⟨fun _f _g => funext (fun h => (hx h.down.down).elim)⟩

 theorem lowerExtend_free (hb : ∀ x, Module.Free A (B.vertex x)) (x : V) :
    Module.Free A (B.lowerExtend.vertex x) := by
  let : ∀ h : Witness.{um} (x ∈ K), Module.Free A (B.vertex ⟨x,h.down.down⟩) := fun h => hb _
  change Module.Free A (∀ h : Witness.{um} (x ∈ K), B.vertex ⟨x,h.down.down⟩)
  infer_instance

 def liftLowerAssignment (f : B.forget.Assignment) : B.lowerExtend.forget.Assignment :=
  fun x h => f ⟨x,h.down.down⟩

 def projectLowerAssignment (f : B.lowerExtend.forget.Assignment) : B.forget.Assignment :=
  fun x => f x.val ⟨⟨x.property⟩⟩

 theorem projectLower_compatible {U : Set V} {f : B.lowerExtend.forget.Assignment}
    (hf : B.lowerExtend.forget.CompatibleOn U f) :
    B.forget.CompatibleOn (Subtype.val ⁻¹' U) (B.projectLowerAssignment f) := by
  intro e hs ht
  exact congrFun (hf e.val hs ht) ⟨⟨e.property⟩⟩

 theorem liftLower_compatible {U : Set V} {f : B.forget.Assignment}
    (hf : B.forget.CompatibleOn (Subtype.val ⁻¹' U) f) :
    B.lowerExtend.forget.CompatibleOn U (B.liftLowerAssignment f) := by
  intro e hs ht
  funext h
  exact hf ⟨e,h.down.down⟩ hs ht

 theorem lowerExtend_generated (hb : B.forget.Generated) : B.lowerExtend.forget.Generated := by
  intro x v
  by_cases hx : x ∈ K
  · obtain ⟨f,hf,hfx⟩ := hb ⟨x,hx⟩ (v ⟨⟨hx⟩⟩)
    refine ⟨B.liftLowerAssignment f,B.liftLower_compatible hf,?_⟩
    funext h
    exact hfx
  · let : Subsingleton (B.lowerExtend.forget.vertex x) := B.lowerExtend_support x hx
    exact ⟨0,fun _ _ _ => by simp,Subsingleton.elim _ _⟩

 theorem lowerExtend_flabby (hb : B.forget.Flabby) : B.lowerExtend.forget.Flabby := by
  intro U hU f hf
  have hu : IsUpperSet (Subtype.val ⁻¹' U : Set K) := fun _ _ hab ha => hU hab ha
  obtain ⟨g,hg,hgf⟩ := hb (Subtype.val ⁻¹' U) hu (B.projectLowerAssignment f) (B.projectLower_compatible hf)
  refine ⟨B.liftLowerAssignment g,B.liftLower_compatible hg,?_⟩
  intro x hx
  funext h
  exact hgf ⟨x,h.down.down⟩ hx

 theorem lowerExtend_quotient (α : E → A)
    (hb : B.UpperQuotient (fun e => α e.val)) : B.lowerExtend.UpperQuotient α := by
  intro e
  constructor
  · intro v
    have hh : ∀ h : Witness.{um} (G.target e ∈ K), ∃ w, (B.upper ⟨e,h.down.down⟩).map w=v h :=
      fun h => (hb ⟨e,h.down.down⟩).1 (v h)
    choose w hw using hh
    exact ⟨w,funext hw⟩
  · intro v
    constructor
    · intro hv
      have hh : ∀ h : Witness.{um} (G.target e ∈ K), ∃ w, v h=α e • w :=
        fun h => (hb ⟨e,h.down.down⟩).2 (v h) |>.mp (congrFun hv h)
      choose w hw using hh
      exact ⟨w,funext hw⟩
    · rintro ⟨w,rfl⟩
      funext h
      exact (hb ⟨e,h.down.down⟩).2 _ |>.mpr ⟨w h,rfl⟩

 theorem lowerExtend_minimal (x : V)
    (hb : ∀ hx : x ∈ K, B.KernelMinimal ⟨x,hx⟩) : B.lowerExtend.KernelMinimal x := by
  intro f hf
  apply LocalCover.pi_mem_ideal_smul
  intro h
  apply hb h.down.down (B.projectLowerAssignment f)
  intro e he
  have hes : G.source e.val=x := congrArg Subtype.val he
  exact congrFun (hf e.val hes) ⟨⟨e.property⟩⟩

end
end GradedSheaf
end KLInvariance.MomentGraph
end


section
namespace KLInvariance.MomentGraph
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A}
  {V E W F : Type um} [PartialOrder V] [PartialOrder W]
  {G : OrderedGraph V E} {H : OrderedGraph W F}
namespace GradedSheaf
variable (B : GradedSheaf (𝓐 := 𝓐) H) (f : GraphMap G H)

 theorem moduleEq_graded {x y : W} (h : x=y) (n : ℤ)
    (v : B.vertex x) (hv : v ∈ (B.vertex x).piece n) :
    Sheaf.moduleEq (congrArg B.forget.vertex h) v ∈ (B.vertex y).piece n := by
  subst y
  exact hv

 def pullback : GradedSheaf (𝓐 := 𝓐) G where
  vertex x := B.vertex (f.vertex x)
  edge e := B.edge (f.edge e)
  lower e := ⟨(B.forget.pullback f).lower e,fun n v hv =>
    (B.lower (f.edge e)).graded n _ (B.moduleEq_graded (f.source e) n v hv)⟩
  upper e := ⟨(B.forget.pullback f).upper e,fun n v hv =>
    (B.upper (f.edge e)).graded n _ (B.moduleEq_graded (f.target e) n v hv)⟩

@[simp] theorem forget_pullback : (B.pullback f).forget = B.forget.pullback f := rfl

 theorem pullback_edgeFlabby (hb : B.EdgeFlabby)
    (hi : Function.Injective f.vertex)
    (hlift : ∀ e x, f.vertex x = H.source e → ∃ a, f.edge a=e ∧ G.source a=x) :
    (B.pullback f).EdgeFlabby := by
  intro Ω hΩ s hs
  have hc : B.forget.ClosedUnder Set.univ (f.vertex '' Ω) := by
    intro e _ hsource
    obtain ⟨x,hx,hxe⟩ := hsource
    obtain ⟨a,rfl,rfl⟩ := hlift e x hxe
    exact ⟨G.target a,hΩ a (Set.mem_univ a) hx,f.target a⟩
  have hcompat : B.forget.CompatibleOn (f.vertex '' Ω) (B.forget.pushAssignment f s) := by
    intro e hsource htarget
    obtain ⟨x,hx,hxe⟩ := hsource
    obtain ⟨a,rfl,rfl⟩ := hlift e x hxe
    obtain ⟨y,hy,hye⟩ := htarget
    have hya : y=G.target a := hi (hye.trans (f.target a).symm)
    subst y
    have hh := hs a hx hy
    change (B.forget.pullback f).lower a (s (G.source a)) =
      (B.forget.pullback f).upper a (s (G.target a)) at hh
    rw [← B.forget.pull_push f hi s] at hh
    rw [Sheaf.pull_lower,Sheaf.pull_upper] at hh
    exact hh
  obtain ⟨t,ht,hts⟩ := hb (f.vertex '' Ω) hc (B.forget.pushAssignment f s) hcompat
  refine ⟨B.forget.pullAssignment f t,B.forget.pull_global f t ht,?_⟩
  intro x hx
  change t (f.vertex x) = s x
  rw [hts (f.vertex x) ⟨x,hx,rfl⟩]
  exact congrFun (B.forget.pull_push f hi s) x

 theorem pullback_kernelMinimal (hi : Function.Injective f.vertex)
    (hlift : ∀ e x, f.vertex x = H.source e → ∃ a, f.edge a=e ∧ G.source a=x)
    (x : V) (hx : B.KernelMinimal (f.vertex x)) :
    (B.pullback f).KernelMinimal x := by
  intro s hs
  have h := hx (B.forget.pushAssignment f s) (by
    intro e he
    obtain ⟨a,rfl,hax⟩ := hlift e x he.symm
    have hh := hs a hax
    change (B.forget.pullback f).lower a (s (G.source a)) = 0 at hh
    rw [← B.forget.pull_push f hi s,Sheaf.pull_lower] at hh
    exact hh)
  have he : B.forget.pushAssignment f s (f.vertex x)=s x :=
    congrFun (B.forget.pull_push f hi s) x
  rwa [he] at h

end GradedSheaf

namespace BoundarySheaf
variable [DirectSum.Decomposition 𝓐] [SetLike.GradedMonoid 𝓐]
  {hneg : ∀ n < 0, 𝓐 n = ⊥} {α : F → A} {b : W}
  (B : BoundarySheaf hneg H α b) (f : GraphMap G H)
  (hi : Function.Injective f.vertex)
  (hlift : ∀ e x, f.vertex x = H.source e → ∃ a, f.edge a=e ∧ G.source a=x)
  (c : V) (hc : f.vertex c=b)

 def pullback : BoundarySheaf hneg G (fun e => α (f.edge e)) c where
  sheaf := B.sheaf.pullback f
  free x := B.free (f.vertex x)
  quotient := B.sheaf.forget.pullback_quotient f α B.quotient
  flabby := B.sheaf.pullback_edgeFlabby f B.flabby hi hlift
  generated := B.sheaf.forget.pullback_generated f B.generated
  top := by change B.sheaf.vertex (f.vertex c)=_; rw [hc,B.top]
  minimal x hx := B.sheaf.pullback_kernelMinimal f hi hlift x
    (B.minimal (f.vertex x) (fun h => hx (hi (h.trans hc.symm))))

end BoundarySheaf
end KLInvariance.MomentGraph
end


section
namespace KLInvariance.MomentGraph.GradedSheaf
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} {V E : Type um} [PartialOrder V]
  {G : OrderedGraph V E}
noncomputable section
 def shift (B : GradedSheaf (𝓐 := 𝓐) G) (d : ℕ) : GradedSheaf (𝓐 := 𝓐) G where
  vertex x := (B.vertex x).shift d
  edge e := (B.edge e).shift d
  lower e := (B.lower e).shift d
  upper e := (B.upper e).shift d

 def zero : GradedSheaf (𝓐 := 𝓐) G where
  vertex _ := ModuleData.zero
  edge _ := ModuleData.zero
  lower _ := ModuleData.Hom.zero _ _
  upper _ := ModuleData.Hom.zero _ _

 def prod (B C : GradedSheaf (𝓐 := 𝓐) G) : GradedSheaf (𝓐 := 𝓐) G where
  vertex x := (B.vertex x).prod (C.vertex x)
  edge e := (B.edge e).prod (C.edge e)
  lower e := (B.lower e).prodMap (C.lower e)
  upper e := (B.upper e).prodMap (C.upper e)

 def pi {ι : Type um} [Fintype ι] (B : ι → GradedSheaf (𝓐 := 𝓐) G) :
    GradedSheaf (𝓐 := 𝓐) G where
  vertex x := ModuleData.pi (fun i => (B i).vertex x)
  edge e := ModuleData.pi (fun i => (B i).edge e)
  lower e := ModuleData.Hom.pi (fun i => (B i).lower e)
  upper e := ModuleData.Hom.pi (fun i => (B i).upper e)

 def OnIso.prodZero {B C : GradedSheaf (𝓐 := 𝓐) G} {U : Set V} (j : OnIso B C U)
    (D : GradedSheaf (𝓐 := 𝓐) G)
    (hV : ∀ x ∈ U, Subsingleton (D.vertex x))
    (hE : ∀ e, G.target e ∈ U → Subsingleton (D.edge e)) : OnIso B (prod C D) U where
  toOnIso := j.toOnIso.prodZero D.forget hV hE
  vertex_graded x hx n v hv := ⟨j.vertex_graded x hx n v hv,Submodule.zero_mem _⟩
  edge_graded e he n v hv := ⟨j.edge_graded e he n v hv,Submodule.zero_mem _⟩

 theorem shift_forget (B : GradedSheaf (𝓐 := 𝓐) G) (d : ℕ) :
    (B.shift d).forget=B.forget := rfl
 theorem zero_forget : (zero (𝓐 := 𝓐) (G := G)).forget=Sheaf.zero := rfl
 theorem prod_forget (B C : GradedSheaf (𝓐 := 𝓐) G) :
    (prod B C).forget=Sheaf.prod B.forget C.forget := rfl
 theorem pi_forget {ι : Type um} [Fintype ι] (B : ι → GradedSheaf (𝓐 := 𝓐) G) :
    (pi B).forget=Sheaf.pi (fun i => (B i).forget) := rfl
end
end KLInvariance.MomentGraph.GradedSheaf
end


section
namespace KLInvariance.MomentGraph.GradedSheaf
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} [DirectSum.Decomposition 𝓐] [SetLike.GradedMonoid 𝓐]
  (hneg : ∀ n < 0, 𝓐 n = ⊥)
  {V E : Type um} [PartialOrder V] {G : OrderedGraph V E}

instance zeroVertex_subsingleton (x : V) : Subsingleton ((zero (𝓐 := 𝓐) (G := G)).vertex x) :=
  inferInstanceAs (Subsingleton PUnit.{max ua um+1})
instance zeroEdge_subsingleton (e : E) : Subsingleton ((zero (𝓐 := 𝓐) (G := G)).edge e) :=
  inferInstanceAs (Subsingleton PUnit.{max ua um+1})

structure BoundaryModels (α : E → A) where
  sheaf : V → GradedSheaf (𝓐 := 𝓐) G
  free : ∀ c x, Module.Free A ((sheaf c).vertex x)
  quotient : ∀ c, (sheaf c).UpperQuotient α
  generated : ∀ c, (sheaf c).forget.Generated
  flabby : ∀ c, (sheaf c).forget.Flabby
  support : ∀ c x, ¬x ≤ c → Subsingleton ((sheaf c).vertex x)
  top : ∀ c, (sheaf c).vertex c ≃ₗ[A] ModuleData.unit.{uk,ua,um} hneg
  top_graded : ∀ c n v, v ∈ ((sheaf c).vertex c).piece n → top c v ∈ (ModuleData.unit.{uk,ua,um} hneg).piece n
  minimal : ∀ c x, x ≠ c → (sheaf c).KernelMinimal x

inductive ModelSum (O : V → GradedSheaf (𝓐 := 𝓐) G) (U : Set V) :
    GradedSheaf (𝓐 := 𝓐) G → Prop where
  | zero : ModelSum O U zero
  | add {B} : ModelSum O U B → ∀ c ∈ U, ∀ (n : ℕ) (d : ULift.{um} (Fin n) → ℕ),
      ModelSum O U (prod B (pi (fun i => (O c).shift (d i))))

namespace ModelSum
variable {hneg} {α : E → A} (O : BoundaryModels hneg (G := G) α)
  {U : Set V} {B : GradedSheaf (𝓐 := 𝓐) G}

omit [DirectSum.Decomposition 𝓐] [SetLike.GradedMonoid 𝓐] in
lemma mono {O : V → GradedSheaf (𝓐 := 𝓐) G} (h : ModelSum O U B)
    {T : Set V} (hUT : U ⊆ T) : ModelSum O T B := by
  induction h with
  | zero => exact .zero
  | add _ c hc n d ih => exact .add ih c (hUT hc) n d

lemma free (h : ModelSum O.sheaf U B) (x : V) : Module.Free A (B.vertex x) := by
  induction h with
  | zero => exact inferInstanceAs (Module.Free A PUnit.{max ua um+1})
  | @add C _ c _ n d ih =>
    let _ : Module.Free A (C.vertex x) := ih
    let _ := O.free c x
    change Module.Free A (C.vertex x × (ULift.{um} (Fin n) → (O.sheaf c).vertex x))
    infer_instance

lemma quotient (h : ModelSum O.sheaf U B) : B.UpperQuotient α := by
  induction h with
  | zero =>
    intro e
    exact ⟨fun v => ⟨0,Subsingleton.elim _ _⟩,fun v => ⟨fun _ => ⟨0,Subsingleton.elim _ _⟩,fun _ => Subsingleton.elim _ _⟩⟩
  | @add C _ c _ n d ih =>
    exact Sheaf.prod_upperQuotient C.forget (Sheaf.pi (fun _ : ULift.{um} (Fin n) => (O.sheaf c).forget)) α ih
      (Sheaf.pi_upperQuotient (fun _ : ULift.{um} (Fin n) => (O.sheaf c).forget) α (fun _ => O.quotient c))

lemma generated (h : ModelSum O.sheaf U B) : B.forget.Generated := by
  induction h with
  | zero =>
    intro x v
    let : Subsingleton ((GradedSheaf.zero (𝓐 := 𝓐) (G := G)).forget.vertex x) := zeroVertex_subsingleton (𝓐 := 𝓐) (G := G) x
    exact ⟨0,fun _ _ _ => rfl,Subsingleton.elim _ _⟩
  | add _ c _ n d ih => exact Sheaf.prod_generated _ _ ih (Sheaf.pi_generated _ (fun _ => O.generated c))

lemma flabby (h : ModelSum O.sheaf U B) : B.forget.Flabby := by
  induction h with
  | zero => exact fun U _ f _ => ⟨f,fun _ _ _ => rfl,fun _ _ => rfl⟩
  | add _ c _ n d ih => exact Sheaf.prod_flabby _ _ ih (Sheaf.pi_flabby _ (fun _ => O.flabby c))

lemma minimal (h : ModelSum O.sheaf U B) (x : V) (hx : x ∉ U) : B.KernelMinimal x := by
  induction h with
  | zero =>
    apply (GradedSheaf.zero.kernelMinimal_iff x).mpr
    intro v _
    let : Subsingleton ((GradedSheaf.zero (𝓐 := 𝓐) (G := G)).forget.vertex x) := zeroVertex_subsingleton (𝓐 := 𝓐) (G := G) x
    rw [Subsingleton.elim v 0]
    exact Submodule.zero_mem _
  | @add C _ c hc n d ih =>
    apply ((prod C (pi (fun i => (O.sheaf c).shift (d i)))).kernelMinimal_iff x).mpr
    exact Sheaf.prod_minimal C.forget (Sheaf.pi (fun _ : ULift.{um} (Fin n) => (O.sheaf c).forget)) x _ ((C.kernelMinimal_iff x).mp ih)
      (Sheaf.pi_minimal (fun _ : ULift.{um} (Fin n) => (O.sheaf c).forget) x _ (fun _ =>
        ((O.sheaf c).kernelMinimal_iff x).mp (O.minimal c x (fun he => hx (he ▸ hc)))))

end ModelSum
end KLInvariance.MomentGraph.GradedSheaf
end


section
namespace KLInvariance.MomentGraph
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} [DirectSum.Decomposition 𝓐] [SetLike.GradedMonoid 𝓐]
  [IsNoetherianRing A]
  (hneg : ∀ n < 0, 𝓐 n = ⊥)
  (hscalar : ∀ a : A, ∃ c : k, a-algebraMap k A c ∈ positiveIdeal 𝓐)
  {V E : Type um} [PartialOrder V] [Fintype V] [Fintype E]
  (G : OrderedGraph V E) (α : E → A) (hα : ∀ e, α e ∈ 𝓐 1)
noncomputable section
attribute [local instance] Classical.propDecidable

 def lowerBoundary (c : V) : BoundarySheaf hneg (lowerGraph G (Set.Iic c) (isLowerSet_Iic c))
    (fun e => α e.val) ⟨c,le_rfl⟩ :=
  (exists_boundarySheaf hneg (lowerGraph G (Set.Iic c) (isLowerSet_Iic c)) hscalar
    ⟨c,le_rfl⟩ (fun x => x.property) (fun e => α e.val) (fun e => hα e.val)).some

 def actualBoundaryModels : GradedSheaf.BoundaryModels hneg (G := G) α where
  sheaf c := (lowerBoundary hneg hscalar G α hα c).sheaf.lowerExtend
  free c := (lowerBoundary hneg hscalar G α hα c).sheaf.lowerExtend_free
    (lowerBoundary hneg hscalar G α hα c).free
  quotient c := (lowerBoundary hneg hscalar G α hα c).sheaf.lowerExtend_quotient α
    (lowerBoundary hneg hscalar G α hα c).quotient
  generated c := (lowerBoundary hneg hscalar G α hα c).sheaf.lowerExtend_generated
    (lowerBoundary hneg hscalar G α hα c).generated
  flabby c := (lowerBoundary hneg hscalar G α hα c).sheaf.lowerExtend_flabby
    (lowerBoundary hneg hscalar G α hα c).flabby.flabby
  support c x hx := (lowerBoundary hneg hscalar G α hα c).sheaf.lowerExtend_support x hx
  top c := ((lowerBoundary hneg hscalar G α hα c).sheaf.lowerExtendVertex ⟨c,le_rfl⟩).trans
    (ModuleData.equivOfEq (lowerBoundary hneg hscalar G α hα c).top)
  top_graded c n v hv := ModuleData.equivOfEq_graded
    (lowerBoundary hneg hscalar G α hα c).top n _
    ((lowerBoundary hneg hscalar G α hα c).sheaf.lowerExtendVertex_graded ⟨c,le_rfl⟩ n v hv)
  minimal c x hx := (lowerBoundary hneg hscalar G α hα c).sheaf.lowerExtend_minimal x
    (fun hxc => (lowerBoundary hneg hscalar G α hα c).minimal ⟨x,hxc⟩
      (fun hh => hx (congrArg Subtype.val hh)))

end
end KLInvariance.MomentGraph
end

end OAI
