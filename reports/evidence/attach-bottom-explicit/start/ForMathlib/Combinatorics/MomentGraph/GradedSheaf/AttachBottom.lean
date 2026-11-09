import Mathlib
import ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Defs

/-! Semantic home: ForMathlib.Combinatorics.MomentGraph.GradedSheaf.AttachBottom. Source spans: GradedSheaves:2.
See migration.json and MIGRATION.md for exact provenance.
Attaching a new bottom vertex with scalar-quotient edges and extending sections across it. -/

namespace OAI

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

end OAI
