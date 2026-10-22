module
public import Mathlib
public import ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Defs

public section

/-! Semantic home: ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Reindex. Source spans: GradedSheaves:4.
See migration.json and MIGRATION.md for exact provenance.
The existing graph equivalence and reindexing of graded sheaves, sections and flabbiness. The graph-equivalence definition remains in its original complete source unit. -/

namespace OAI

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

@[expose] def reindex : GradedSheaf (𝓐 := 𝓐) G where
  vertex := fun x => B.vertex (e.vertex x)
  edge := fun a => B.edge (e.edge a)
  lower := fun a => (B.lower (e.edge a)).comp (ModuleData.Hom.ofEq (congrArg B.vertex (e.source a)))
  upper := fun a => (B.upper (e.edge a)).comp (ModuleData.Hom.ofEq (congrArg B.vertex (e.target a)))

@[expose] def reindexAssignment (f : B.forget.Assignment) : (B.reindex e).forget.Assignment :=
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

@[expose] def unreindexAssignment (f : (B.reindex e).forget.Assignment) : B.forget.Assignment :=
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

end OAI
