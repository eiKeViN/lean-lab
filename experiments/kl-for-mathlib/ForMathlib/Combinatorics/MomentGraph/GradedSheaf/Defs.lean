module
public import Mathlib
public import ForMathlib.Algebra.Module.Graded.ModuleData.Equality
public import ForMathlib.Combinatorics.MomentGraph.Sheaf.Basic

public section

/-! Semantic home: ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Defs. Source spans: GradedSheaves:1.
See migration.json and MIGRATION.md for exact provenance.
Graded sheaf data, its underlying sheaf, graded sections, boundary and boundary-cover existence. -/

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

@[expose] def forget : Sheaf (R := A) G where
  vertex := fun x => (B.vertex x).obj
  edge := fun e => (B.edge e).obj
  lower := fun e => (B.lower e).map
  upper := fun e => (B.upper e).map

/-- Extension for sets closed under actual edges. It implies the source's
ordinary flabbiness, and is convenient for the descending construction. -/
@[expose] def EdgeFlabby : Prop :=
  ∀ Ω : Set V, B.forget.ClosedUnder Set.univ Ω →
    ∀ f : B.forget.Assignment, B.forget.CompatibleOn Ω f →
    ∃ g : B.forget.Assignment, B.forget.IsGlobal g ∧ ∀ x ∈ Ω, g x = f x

 theorem EdgeFlabby.flabby (h : B.EdgeFlabby) : B.forget.Flabby := by
  intro Ω hΩ f hf
  exact h Ω (fun e _ he => hΩ (G.increasing e).le he) f hf

variable [Fintype V] [Fintype E]

@[expose] noncomputable def assignments : ModuleData.{uk,ua,um} 𝓐 := ModuleData.pi B.vertex

@[expose] noncomputable def lowerGlobal (e : E) : ModuleData.Hom B.assignments (B.edge e) :=
  (B.lower e).comp (ModuleData.projection B.vertex (G.source e))

@[expose] noncomputable def upperGlobal (e : E) : ModuleData.Hom B.assignments (B.edge e) :=
  (B.upper e).comp (ModuleData.projection B.vertex (G.target e))

omit [Fintype E] in
 theorem sections_homogeneous (Ω : Set V) :
    ∀ n f, f ∈ B.forget.sections Ω → component B.assignments.piece n f ∈ B.forget.sections Ω := by
  intro n f hf e hs ht
  change (B.lowerGlobal e).map (component B.assignments.piece n f) =
    (B.upperGlobal e).map (component B.assignments.piece n f)
  rw [← (B.lowerGlobal e).component n f, ← (B.upperGlobal e).component n f]
  exact congrArg (component (B.edge e).piece n) (hf e hs ht)

@[expose] noncomputable def sections [IsNoetherianRing A] (Ω : Set V) : ModuleData.{uk,ua,um} 𝓐 :=
  ModuleData.sub B.assignments (B.forget.sections Ω) (B.sections_homogeneous Ω)

@[expose] noncomputable def boundary (x : V) : ModuleData.{uk,ua,um} 𝓐 :=
by
  classical
  letI : Fintype (Sheaf.Outgoing (G := G) x) := inferInstanceAs (Fintype {e : E // G.source e = x})
  exact ModuleData.pi (fun e : Sheaf.Outgoing (G := G) x => B.edge e.val)

@[expose] noncomputable def boundaryHom [IsNoetherianRing A] (x : V) :
    ModuleData.Hom (B.sections (Set.Ioi x)) (B.boundary x) where
  map := B.forget.boundaryMap x
  graded := by
    intro n f hf e _
    exact (B.upper e.val).graded n (f.val (G.target e.val)) (hf (G.target e.val) (Set.mem_univ _))

@[expose] noncomputable def boundaryImage [IsNoetherianRing A] (x : V) : ModuleData.{uk,ua,um} 𝓐 :=
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

end OAI
