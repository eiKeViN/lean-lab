import Mathlib
import OAI.Algebra.Module.Graded.ModuleData.Equality
import OAI.Combinatorics.MomentGraph.Sheaf.Basic

/-! Semantic home: OAI.Combinatorics.MomentGraph.GradedSheaf.Basic. Source spans: GradedSheaves:1, GradedSheaves:2, GradedSheaves:4, GradedSheaves:6.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.MomentGraph
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A}
  {V E : Type um} [PartialOrder V] (G : OrderedGraph V E)

structure GradedSheaf where
  vertex : V → ModuleData.{uk,ua,um} 𝓐
  edge : E → ModuleData.{uk,ua,um} 𝓐
  lower : ∀ e, ModuleData.Hom (vertex (G.source e)) (edge e)
  upper : ∀ e, ModuleData.Hom (vertex (G.target e)) (edge e)

namespace GradedSheaf
variable {G} (B : GradedSheaf (𝓐 := 𝓐) G)

def forget : Sheaf (R := A) G where
  vertex := fun x => (B.vertex x).obj
  edge := fun e => (B.edge e).obj
  lower := fun e => (B.lower e).map
  upper := fun e => (B.upper e).map

/-- Extension for sets closed under actual edges. It implies the source's
ordinary flabbiness, and is convenient for the descending construction. -/
def EdgeFlabby : Prop :=
  ∀ Ω : Set V, B.forget.ClosedUnder Set.univ Ω →
    ∀ f : B.forget.Assignment, B.forget.CompatibleOn Ω f →
    ∃ g : B.forget.Assignment, B.forget.IsGlobal g ∧ ∀ x ∈ Ω, g x = f x

 theorem EdgeFlabby.flabby (h : B.EdgeFlabby) : B.forget.Flabby := by
  intro Ω hΩ f hf
  exact h Ω (fun e _ he => hΩ (G.increasing e).le he) f hf

variable [Fintype V] [Fintype E]

noncomputable def assignments : ModuleData.{uk,ua,um} 𝓐 := ModuleData.pi B.vertex

noncomputable def lowerGlobal (e : E) : ModuleData.Hom B.assignments (B.edge e) :=
  (B.lower e).comp (ModuleData.projection B.vertex (G.source e))

noncomputable def upperGlobal (e : E) : ModuleData.Hom B.assignments (B.edge e) :=
  (B.upper e).comp (ModuleData.projection B.vertex (G.target e))

omit [Fintype E] in
 theorem sections_homogeneous (Ω : Set V) :
    ∀ n f, f ∈ B.forget.sections Ω → component B.assignments.piece n f ∈ B.forget.sections Ω := by
  intro n f hf e hs ht
  change (B.lowerGlobal e).map (component B.assignments.piece n f) =
    (B.upperGlobal e).map (component B.assignments.piece n f)
  rw [← (B.lowerGlobal e).component n f, ← (B.upperGlobal e).component n f]
  exact congrArg (component (B.edge e).piece n) (hf e hs ht)

noncomputable def sections [IsNoetherianRing A] (Ω : Set V) : ModuleData.{uk,ua,um} 𝓐 :=
  ModuleData.sub B.assignments (B.forget.sections Ω) (B.sections_homogeneous Ω)

noncomputable def boundary (x : V) : ModuleData.{uk,ua,um} 𝓐 :=
by
  classical
  letI : Fintype (Sheaf.Outgoing (G := G) x) := inferInstanceAs (Fintype {e : E // G.source e = x})
  exact ModuleData.pi (fun e : Sheaf.Outgoing (G := G) x => B.edge e.val)

noncomputable def boundaryHom [IsNoetherianRing A] (x : V) :
    ModuleData.Hom (B.sections (Set.Ioi x)) (B.boundary x) where
  map := B.forget.boundaryMap x
  graded := by
    intro n f hf e _
    exact (B.upper e.val).graded n (f.val (G.target e.val)) (hf (G.target e.val) (Set.mem_univ _))

noncomputable def boundaryImage [IsNoetherianRing A] (x : V) : ModuleData.{uk,ua,um} 𝓐 :=
  ModuleData.range (B.boundaryHom x)

 theorem exists_boundaryCover [IsNoetherianRing A]
    [DirectSum.Decomposition 𝓐] [SetLike.GradedMonoid 𝓐]
    (hneg : ∀ n < 0, 𝓐 n = ⊥)
    (hscalar : ∀ a : A, ∃ c : k, a-algebraMap k A c ∈ positiveIdeal 𝓐) (x : V) :
    Nonempty (ModuleData.MinimalCover (B.boundaryImage x)) :=
  ModuleData.exists_minimalCover hneg hscalar (B.boundaryImage x)

end GradedSheaf
end KLInvariance.MomentGraph
end


section
namespace KLInvariance.MomentGraph
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A}
  {V E D : Type um} [PartialOrder V] (G : OrderedGraph V E)

/-- Adjoin a vertex below the old vertices, with specified outgoing edges.
Only the edge orientations, not the extra comparabilities, enter sections. -/
def bottomGraph (τ : D → V) : OrderedGraph (WithBot V) (E ⊕ D) where
  source := Sum.elim (fun e => (G.source e : WithBot V)) (fun _ => ⊥)
  target := Sum.elim (fun e => (G.target e : WithBot V)) (fun d => (τ d : WithBot V))
  increasing := by
    intro e
    cases e with
    | inl e => exact WithBot.coe_lt_coe.mpr (G.increasing e)
    | inr d => exact WithBot.bot_lt_coe (τ d)

namespace GradedSheaf
variable {G} (B : GradedSheaf (𝓐 := 𝓐) G)
  [Fintype V] [Fintype D] [IsNoetherianRing A]
  (τ : D → V) (α : D → A) (hα : ∀ d, α d ∈ 𝓐 1)

noncomputable def attachEdges (d : D) : ModuleData.{uk,ua,um} 𝓐 :=
  (B.vertex (τ d)).scalarQuotient (α d) 1 (hα d)

noncomputable def attachQuotient (d : D) :
    ModuleData.Hom (B.vertex (τ d)) (B.attachEdges τ α hα d) :=
  ModuleData.quotientMap _ _ (scalar_range_homogeneous 𝓐 (B.vertex (τ d)).piece 1 (α d) (hα d))

noncomputable def attachBoundary : ModuleData.{uk,ua,um} 𝓐 :=
  ModuleData.pi (B.attachEdges τ α hα)

noncomputable def attachBoundaryMap :
    ModuleData.Hom (B.sections Set.univ) (B.attachBoundary τ α hα) where
  map := LinearMap.pi fun d => (B.attachQuotient τ α hα d).map.comp
    ((LinearMap.proj (τ d)).comp (B.forget.sections Set.univ).subtype)
  graded := by
    intro n f hf d _
    exact (B.attachQuotient τ α hα d).graded n _ (hf (τ d) (Set.mem_univ _))

noncomputable def attachImage : ModuleData.{uk,ua,um} 𝓐 :=
  ModuleData.range (B.attachBoundaryMap τ α hα)

variable (C : ModuleData.MinimalCover (B.attachImage τ α hα))

noncomputable def attachStalkMap : ModuleData.Hom C.source (B.attachBoundary τ α hα) :=
  (ModuleData.subtype (B.attachBoundary τ α hα) _
    (range_homogeneous _ _ (B.attachBoundaryMap τ α hα).map 0
      (by simpa using (B.attachBoundaryMap τ α hα).graded))).comp C.hom

noncomputable def extendBottom : GradedSheaf (𝓐 := 𝓐) (bottomGraph G τ) where
  vertex := WithBot.recBotCoe C.source B.vertex
  edge := Sum.elim B.edge (B.attachEdges τ α hα)
  lower := by
    intro e
    cases e with
    | inl e => exact B.lower e
    | inr d =>
      exact (ModuleData.projection (B.attachEdges τ α hα) d).comp
        (B.attachStalkMap τ α hα C)
  upper := by
    intro e
    cases e with
    | inl e => exact B.upper e
    | inr d => exact B.attachQuotient τ α hα d

 def attachAssignment (z : C.source) (f : B.forget.Assignment) :
    (B.extendBottom τ α hα C).forget.Assignment := WithBot.recBotCoe z f

 theorem attachAssignment_global (z : C.source) (f : B.forget.Assignment)
    (hf : B.forget.IsGlobal f)
    (hz : ∀ d, (B.attachStalkMap τ α hα C).map z d =
      (B.attachQuotient τ α hα d).map (f (τ d))) :
    (B.extendBottom τ α hα C).forget.IsGlobal (B.attachAssignment τ α hα C z f) := by
  intro e _ _
  cases e with
  | inl e => exact hf e (Set.mem_univ _) (Set.mem_univ _)
  | inr d => exact hz d

 theorem lift_global (f : B.forget.Assignment) (hf : B.forget.IsGlobal f) :
    ∃ z : C.source, (B.extendBottom τ α hα C).forget.IsGlobal
      (B.attachAssignment τ α hα C z f) := by
  let s : B.sections Set.univ := ⟨f,hf⟩
  let v : B.attachImage τ α hα :=
    ⟨(B.attachBoundaryMap τ α hα).map s, ⟨s,rfl⟩⟩
  obtain ⟨z,hz⟩ := C.surjective v
  refine ⟨z,B.attachAssignment_global τ α hα C z f hf ?_⟩
  intro d
  exact congrArg (fun t : B.attachImage τ α hα => t.val d) hz

 theorem extendBottom_generated (hg : B.forget.Generated) :
    (B.extendBottom τ α hα C).forget.Generated := by
  intro x
  induction x using WithBot.recBotCoe with
  | bot =>
    intro z
    obtain ⟨s,hs⟩ := (C.hom.map z).property
    refine ⟨B.attachAssignment τ α hα C z s.val,
      B.attachAssignment_global τ α hα C z s.val s.property ?_,rfl⟩
    intro d
    exact congrFun hs d |>.symm
  | coe x =>
    intro v
    obtain ⟨f,hf,hfx⟩ := hg x v
    obtain ⟨z,hz⟩ := B.lift_global τ α hα C f hf
    exact ⟨B.attachAssignment τ α hα C z f,hz,hfx⟩

 theorem extendBottom_edgeFlabby (hf : B.EdgeFlabby) :
    (B.extendBottom τ α hα C).EdgeFlabby := by
  intro Ω hΩ f hcompat
  let Ω' : Set V := {x | (x : WithBot V) ∈ Ω}
  let f' : B.forget.Assignment := fun x => f (x : WithBot V)
  have hc : B.forget.ClosedUnder Set.univ Ω' := by
    intro e _ hs
    exact hΩ (Sum.inl e) (Set.mem_univ _) hs
  have hcf : B.forget.CompatibleOn Ω' f' := by
    intro e hs ht
    exact hcompat (Sum.inl e) hs ht
  obtain ⟨g,hg,hgf⟩ := hf Ω' hc f' hcf
  classical
  by_cases hb : (⊥ : WithBot V) ∈ Ω
  · refine ⟨B.attachAssignment τ α hα C (f ⊥) g,
      B.attachAssignment_global τ α hα C (f ⊥) g hg ?_,?_⟩
    · intro d
      have hd : (τ d : WithBot V) ∈ Ω := hΩ (Sum.inr d) (Set.mem_univ _) hb
      rw [hgf (τ d) hd]
      exact hcompat (Sum.inr d) hb hd
    · intro x hx
      induction x using WithBot.recBotCoe with
      | bot => rfl
      | coe x => exact hgf x hx
  · obtain ⟨z,hz⟩ := B.lift_global τ α hα C g hg
    refine ⟨B.attachAssignment τ α hα C z g,hz,?_⟩
    intro x hx
    induction x using WithBot.recBotCoe with
    | bot => exact (hb hx).elim
    | coe x => exact hgf x hx

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

/-- An isomorphism of directed graphs, with no order-reflection requirement. -/
structure GraphEquiv (G : OrderedGraph V E) (H : OrderedGraph W F) where
  vertex : V ≃ W
  edge : E ≃ F
  source : ∀ e, vertex (G.source e) = H.source (edge e)
  target : ∀ e, vertex (G.target e) = H.target (edge e)

namespace GradedSheaf
variable (B : GradedSheaf (𝓐 := 𝓐) H) (e : GraphEquiv G H)

def reindex : GradedSheaf (𝓐 := 𝓐) G where
  vertex := fun x => B.vertex (e.vertex x)
  edge := fun a => B.edge (e.edge a)
  lower := fun a => (B.lower (e.edge a)).comp (ModuleData.Hom.ofEq (congrArg B.vertex (e.source a)))
  upper := fun a => (B.upper (e.edge a)).comp (ModuleData.Hom.ofEq (congrArg B.vertex (e.target a)))

def reindexAssignment (f : B.forget.Assignment) : (B.reindex e).forget.Assignment :=
  fun x => f (e.vertex x)

@[simp] theorem reindex_lower (a : E) (f : B.forget.Assignment) :
    (B.reindex e).forget.lower a (B.reindexAssignment e f (G.source a)) =
      B.forget.lower (e.edge a) (f (H.source (e.edge a))) := by
  change (B.lower (e.edge a)).map ((ModuleData.Hom.ofEq (congrArg B.vertex (e.source a))).map
    (f (e.vertex (G.source a)))) = _
  exact congrArg (B.lower (e.edge a)).map
    (ModuleData.Hom.ofEq_apply B.vertex (e.source a) f)

@[simp] theorem reindex_upper (a : E) (f : B.forget.Assignment) :
    (B.reindex e).forget.upper a (B.reindexAssignment e f (G.target a)) =
      B.forget.upper (e.edge a) (f (H.target (e.edge a))) := by
  change (B.upper (e.edge a)).map ((ModuleData.Hom.ofEq (congrArg B.vertex (e.target a))).map
    (f (e.vertex (G.target a)))) = _
  exact congrArg (B.upper (e.edge a)).map
    (ModuleData.Hom.ofEq_apply B.vertex (e.target a) f)

def unreindexAssignment (f : (B.reindex e).forget.Assignment) : B.forget.Assignment :=
  fun y => (ModuleData.Hom.ofEq (congrArg B.vertex (e.vertex.apply_symm_apply y))).map
    (f (e.vertex.symm y))

@[simp] theorem unreindex_reindexAssignment (f : B.forget.Assignment) :
    B.unreindexAssignment e (B.reindexAssignment e f) = f := by
  funext y
  exact ModuleData.Hom.ofEq_apply B.vertex (e.vertex.apply_symm_apply y) f

@[simp] theorem reindex_unreindexAssignment (f : (B.reindex e).forget.Assignment) :
    B.reindexAssignment e (B.unreindexAssignment e f) = f := by
  funext x
  change (ModuleData.Hom.ofEq (congrArg B.vertex (e.vertex.apply_symm_apply (e.vertex x)))).map
    (f (e.vertex.symm (e.vertex x))) = f x
  have h : e.vertex.symm (e.vertex x) = x := e.vertex.symm_apply_apply x
  have hh : (ModuleData.Hom.ofEq
      (congrArg (fun t => B.vertex (e.vertex t)) h)).map
      (f (e.vertex.symm (e.vertex x))) = f x :=
    ModuleData.Hom.ofEq_apply (fun t => B.vertex (e.vertex t)) h f
  exact hh

 theorem reindex_global (f : B.forget.Assignment) (hf : B.forget.IsGlobal f) :
    (B.reindex e).forget.IsGlobal (B.reindexAssignment e f) := by
  intro a _ _
  rw [B.reindex_lower, B.reindex_upper]
  exact hf (e.edge a) (Set.mem_univ _) (Set.mem_univ _)

 theorem reindex_generated (hg : B.forget.Generated) : (B.reindex e).forget.Generated := by
  intro x v
  obtain ⟨f,hf,hfx⟩ := hg (e.vertex x) v
  exact ⟨B.reindexAssignment e f,B.reindex_global e f hf,hfx⟩

 theorem reindex_edgeFlabby (hb : B.EdgeFlabby) : (B.reindex e).EdgeFlabby := by
  intro Ω hΩ f hf
  let Ω' := e.vertex '' Ω
  have hc : B.forget.ClosedUnder Set.univ Ω' := by
    intro a _ hs
    obtain ⟨a,rfl⟩ := e.edge.surjective a
    obtain ⟨x,hx,hxs⟩ := hs
    have hx' : x = G.source a := e.vertex.injective (hxs.trans (e.source a).symm)
    exact ⟨G.target a,hΩ a (Set.mem_univ _) (hx' ▸ hx),e.target a⟩
  have hcf : B.forget.CompatibleOn Ω' (B.unreindexAssignment e f) := by
    intro a hs ht
    obtain ⟨a,rfl⟩ := e.edge.surjective a
    have hh (x : V) (h : e.vertex x ∈ Ω') : x ∈ Ω := by
      obtain ⟨y,hy,hyx⟩ := h
      exact (e.vertex.injective hyx) ▸ hy
    have hfa := hf a (hh _ ((e.source a).symm ▸ hs)) (hh _ ((e.target a).symm ▸ ht))
    rw [← B.reindex_unreindexAssignment e f] at hfa
    exact (B.reindex_lower e a (B.unreindexAssignment e f)).symm.trans
      (hfa.trans (B.reindex_upper e a (B.unreindexAssignment e f)))
  obtain ⟨g,hg,hgf⟩ := hb Ω' hc (B.unreindexAssignment e f) hcf
  refine ⟨B.reindexAssignment e g,B.reindex_global e g hg,?_⟩
  intro x hx
  have hh := hgf (e.vertex x) ⟨x,hx,rfl⟩
  change g (e.vertex x) = f x
  rw [hh]
  exact congrFun (B.reindex_unreindexAssignment e f) x

end GradedSheaf
end KLInvariance.MomentGraph
end


section
namespace KLInvariance.MomentGraph.GradedSheaf
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A}
  {V E W F : Type um} [PartialOrder V] [PartialOrder W]
  {G : OrderedGraph V E} {H : OrderedGraph W F}

 def FreeStalks (B : GradedSheaf (𝓐 := 𝓐) G) : Prop := ∀ x, Module.Free A (B.vertex x)

/-- The genuine upper-end quotient rule, expressed without choosing a quotient
presentation of the edge object. -/
 def UpperQuotient (B : GradedSheaf (𝓐 := 𝓐) G) (α : E → A) : Prop :=
  ∀ e, Function.Surjective (B.upper e).map ∧
    ∀ v, (B.upper e).map v = 0 ↔ ∃ w, v = α e • w

/-- Minimality of the full outgoing boundary cover. The assignment formulation
avoids dependent casts and is equivalent to the usual kernel containment. -/
 def KernelMinimal (B : GradedSheaf (𝓐 := 𝓐) G) (x : V) : Prop :=
  ∀ f : B.forget.Assignment,
    (∀ e, G.source e = x → B.forget.lower e (f (G.source e)) = 0) →
    f x ∈ positiveIdeal 𝓐 • (⊤ : Submodule A (B.vertex x))

 theorem kernelMinimal_iff (B : GradedSheaf (𝓐 := 𝓐) G) (x : V) :
    B.KernelMinimal x ↔ LinearMap.ker (B.forget.stalkMap x) ≤
      positiveIdeal 𝓐 • (⊤ : Submodule A (B.vertex x)) := by
  classical
  constructor
  · intro h v hv
    let f : B.forget.Assignment := Function.update 0 x v
    have hf : f x = v := by simp [f]
    rw [← hf]
    apply h f
    intro e he
    have hh := congrFun (LinearMap.mem_ker.mp hv) (⟨e,he⟩ : Sheaf.Outgoing x)
    subst x
    simpa [Sheaf.stalkMap,f] using hh
  · intro h f hf
    apply h
    apply LinearMap.mem_ker.mpr
    funext e
    rcases e with ⟨e,he⟩
    subst x
    exact hf e rfl

 theorem reindex_freeStalks (B : GradedSheaf (𝓐 := 𝓐) H) (e : GraphEquiv G H)
    (h : B.FreeStalks) : (B.reindex e).FreeStalks := fun x => h (e.vertex x)

 theorem reindex_upperQuotient (B : GradedSheaf (𝓐 := 𝓐) H) (e : GraphEquiv G H)
    {α : F → A} (h : B.UpperQuotient α) : (B.reindex e).UpperQuotient (α ∘ e.edge) := by
  intro a
  let j := ModuleData.Hom.ofEq (congrArg B.vertex (e.target a))
  have hj := ModuleData.Hom.ofEq_bijective (congrArg B.vertex (e.target a))
  refine ⟨(h (e.edge a)).1.comp hj.2,?_⟩
  intro v
  change (B.upper (e.edge a)).map (j.map v) = 0 ↔ ∃ w, v = α (e.edge a) • w
  rw [(h (e.edge a)).2]
  constructor
  · rintro ⟨w,hw⟩
    obtain ⟨z,rfl⟩ := hj.2 w
    exact ⟨z,hj.1 (hw.trans (map_smul j.map (α (e.edge a)) z).symm)⟩
  · rintro ⟨w,rfl⟩
    exact ⟨j.map w,map_smul _ _ _⟩

 theorem reindex_kernelMinimal (B : GradedSheaf (𝓐 := 𝓐) H) (e : GraphEquiv G H)
    (x : V) (h : B.KernelMinimal (e.vertex x)) : (B.reindex e).KernelMinimal x := by
  intro f hf
  have hh : ∀ a, H.source a = e.vertex x →
      B.forget.lower a (B.unreindexAssignment e f (H.source a)) = 0 := by
    intro a ha
    obtain ⟨a,rfl⟩ := e.edge.surjective a
    have hs : G.source a = x := e.vertex.injective ((e.source a).trans ha)
    have hv := hf a hs
    rw [← B.reindex_unreindexAssignment e f] at hv
    exact (B.reindex_lower e a (B.unreindexAssignment e f)).symm.trans hv
  have hm := h (B.unreindexAssignment e f) hh
  have he := congrFun (B.reindex_unreindexAssignment e f) x
  exact he ▸ hm

variable {D : Type um} [Fintype V] [Fintype D] [IsNoetherianRing A]
  (B : GradedSheaf (𝓐 := 𝓐) G) (τ : D → V) (α : D → A)
  (hα : ∀ d, α d ∈ 𝓐 1) (C : ModuleData.MinimalCover (B.attachImage τ α hα))

 theorem extendBottom_freeStalks (hb : B.FreeStalks) :
    (B.extendBottom τ α hα C).FreeStalks := by
  intro x
  induction x using WithBot.recBotCoe with
  | bot => exact C.free
  | coe x => exact hb x

 theorem extendBottom_upperQuotient {αold : E → A} (hb : B.UpperQuotient αold) :
    (B.extendBottom τ α hα C).UpperQuotient (Sum.elim αold α) := by
  intro e
  cases e with
  | inl e => exact hb e
  | inr d =>
    let S := LinearMap.range (LinearMap.lsmul A (B.vertex (τ d)) (α d))
    refine ⟨S.mkQ_surjective,?_⟩
    intro v
    change S.mkQ v = 0 ↔ ∃ w, v = α d • w
    refine (Submodule.Quotient.mk_eq_zero S).trans ?_
    change (∃ w, α d • w = v) ↔ ∃ w, v = α d • w
    exact ⟨fun ⟨w,hw⟩ => ⟨w,hw.symm⟩,fun ⟨w,hw⟩ => ⟨w,hw.symm⟩⟩

 theorem extendBottom_kernelMinimal_bot : (B.extendBottom τ α hα C).KernelMinimal ⊥ := by
  intro f hf
  apply C.minimal
  apply LinearMap.mem_ker.mpr
  apply Subtype.ext
  funext d
  exact hf (Sum.inr d) rfl

 theorem extendBottom_kernelMinimal_coe (x : V) (h : B.KernelMinimal x) :
    (B.extendBottom τ α hα C).KernelMinimal (x : WithBot V) := by
  intro f hf
  apply h (fun y => f (y : WithBot V))
  intro a ha
  exact hf (Sum.inl a) (congrArg (fun y : V => (y : WithBot V)) ha)

end KLInvariance.MomentGraph.GradedSheaf
end

end OAI
