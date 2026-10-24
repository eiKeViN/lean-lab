module
public import Mathlib
public import ForMathlib.Combinatorics.MomentGraph.Sheaf.Structure
public import ForMathlib.Combinatorics.MomentGraph.Sheaf.Pullback

public section

/-! Semantic home: ForMathlib.Combinatorics.MomentGraph.Sheaf.Restriction. Source spans: MinimalExtensions:19, MinimalExtensions:20.
See migration.json and MIGRATION.md for exact provenance.
Restriction to induced subgraphs and lower ideals, including the structure-sheaf restriction isomorphism. -/

namespace OAI

section
namespace KLInvariance.MomentGraph
universe ur uv ue um
variable {V : Type uv} [PartialOrder V] {E : Type ue} (G : OrderedGraph V E)

 @[expose] def inducedGraph (K : Set V) : OrderedGraph K {e : E // G.source e ∈ K ∧ G.target e ∈ K} where
  source e := ⟨G.source e.val,e.property.1⟩
  target e := ⟨G.target e.val,e.property.2⟩
  increasing e := G.increasing e.val

namespace Sheaf
variable {G} {R : Type ur} [CommRing R] (B : Sheaf.{ur,uv,ue,um} (R := R) G)
  (K : Set V)
noncomputable section

 @[expose] def restrict : Sheaf (R := R) (inducedGraph G K) where
  vertex x := B.vertex x.val
  edge e := B.edge e.val
  lower e := B.lower e.val
  upper e := B.upper e.val

 @[expose] def restrictAssignment (f : B.Assignment) : (B.restrict K).Assignment := fun x => f x.val

 @[expose] def extendAssignment (f : (B.restrict K).Assignment) : B.Assignment := by
  classical
  exact fun x => if h : x ∈ K then f ⟨x,h⟩ else 0

@[simp] theorem extendAssignment_mem (f : (B.restrict K).Assignment) (x : K) :
    B.extendAssignment K f x.val = f x := by
  classical
  change (if h : x.val ∈ K then f ⟨x.val,h⟩ else 0) = f x
  split_ifs with h
  · rfl
  · exact (h x.property).elim

 theorem restrict_compatible {Ω : Set V} {f : B.Assignment} (hf : B.CompatibleOn Ω f) :
    (B.restrict K).CompatibleOn (Subtype.val ⁻¹' Ω) (B.restrictAssignment K f) := by
  intro e hs ht
  exact hf e.val hs ht

 theorem restrict_global (f : B.Assignment) (hf : B.IsGlobal f) :
    (B.restrict K).IsGlobal (B.restrictAssignment K f) := by
  intro e _ _
  exact hf e.val (Set.mem_univ _) (Set.mem_univ _)

 theorem restrict_generated (hg : B.Generated) : (B.restrict K).Generated := by
  intro x v
  obtain ⟨f,hf,hfx⟩ := hg x.val v
  exact ⟨B.restrictAssignment K f,B.restrict_global K f hf,hfx⟩

 theorem extend_compatible (Ω : Set K) (f : (B.restrict K).Assignment)
    (hf : (B.restrict K).CompatibleOn Ω f) :
    B.CompatibleOn (Subtype.val '' Ω) (B.extendAssignment K f) := by
  intro e hs ht
  obtain ⟨x,hx,hxe⟩ := hs
  obtain ⟨y,hy,hye⟩ := ht
  have hsk : G.source e ∈ K := hxe ▸ x.property
  have htk : G.target e ∈ K := hye ▸ y.property
  let ee : {e : E // G.source e ∈ K ∧ G.target e ∈ K} := ⟨e,hsk,htk⟩
  have hsx : (inducedGraph G K).source ee = x := Subtype.ext hxe.symm
  have hty : (inducedGraph G K).target ee = y := Subtype.ext hye.symm
  have hh := hf ee (hsx ▸ hx) (hty ▸ hy)
  change B.lower e (f ⟨G.source e,hsk⟩) = B.upper e (f ⟨G.target e,htk⟩) at hh
  simpa only [← B.extendAssignment_mem K f] using hh

/-- The induced subgraph may use upper sets which are not ambient upper
sets. All nonzero exiting edges must stay in the subgraph. -/
 theorem restrict_flabby_live [Finite V] (hb : B.Flabby) (live : Set E)
    (hdead : ∀ e, e ∉ live → Subsingleton (B.edge e))
    (hclosed : ∀ e ∈ live, G.source e ∈ K → G.target e ∈ K) :
    (B.restrict K).Flabby := by
  intro Ω hΩ f hf
  have hc : B.ClosedUnder live (Subtype.val '' Ω) := by
    intro e he hs
    obtain ⟨x,hx,hxe⟩ := hs
    have hsk : G.source e ∈ K := hxe ▸ x.property
    have htk := hclosed e he hsk
    refine ⟨⟨G.target e,htk⟩,?_,rfl⟩
    apply hΩ _ hx
    change x.val ≤ G.target e
    rw [hxe]
    exact (G.increasing e).le
  obtain ⟨g,hg,hgf⟩ := B.extend_closedUnder hb live hdead (Subtype.val '' Ω) hc
    (B.extendAssignment K f) (B.extend_compatible K Ω f hf)
  refine ⟨B.restrictAssignment K g,B.restrict_global K g hg,?_⟩
  intro x hx
  exact (hgf x.val ⟨x,hx,rfl⟩).trans (B.extendAssignment_mem K f x)

 theorem restrict_quotient (α : E → R) (hB : B.UpperQuotient α) :
    (B.restrict K).UpperQuotient (fun e => α e.val) := fun e => hB e.val

end
end Sheaf
end KLInvariance.MomentGraph
end


section
namespace KLInvariance.MomentGraph.Sheaf
universe ur uv ue
variable {R : Type ur} [CommRing R] {V : Type uv} [PartialOrder V]
  {E : Type ue} (G : OrderedGraph V E) (α : E → R) (K : Set V)
noncomputable section

 @[expose] def structureRestrictIso (c : K) :
    Iso ((structureSheaf G α c.val).restrict K)
      (structureSheaf (inducedGraph G K) (fun e => α e.val) c) where
  vertex _ := LinearEquiv.refl R _
  edge _ := LinearEquiv.refl R _
  lower _ _ := rfl
  upper _ _ := rfl

 theorem structureSheaf_edge_subsingleton (c : V) (e : E) (he : ¬ G.target e ≤ c) :
    Subsingleton ((structureSheaf G α c).edge e) :=
  ⟨fun _ _ => funext (fun h => False.elim (he h.down))⟩

 theorem structureSheaf_lowerIdeal_flabby [Finite V] (hK : IsLowerSet K) (c : K)
    (hf : (structureSheaf G α c.val).Flabby) :
    (structureSheaf (inducedGraph G K) (fun e => α e.val) c).Flabby := by
  apply (structureRestrictIso G α K c).flabby
  apply (structureSheaf G α c.val).restrict_flabby_live K hf {e | G.target e ∈ K}
  · intro e he
    exact structureSheaf_edge_subsingleton G α c.val e (fun hc => he (hK hc c.property))
  · intro e he _
    exact he

end
end KLInvariance.MomentGraph.Sheaf
end

end OAI
