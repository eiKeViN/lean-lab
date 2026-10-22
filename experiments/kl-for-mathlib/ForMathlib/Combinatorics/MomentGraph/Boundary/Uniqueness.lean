module
public import Mathlib
public import ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Uniqueness
public import ForMathlib.Combinatorics.MomentGraph.GradedSheaf.StalkMaps

public section

/-! Semantic home: ForMathlib.Combinatorics.MomentGraph.Boundary.Uniqueness. Source spans: EdgeLocalization:11, EdgeLocalization:13.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.MomentGraph.BoundarySheaf
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} [DirectSum.Decomposition 𝓐] [SetLike.GradedMonoid 𝓐]
  [IsDomain A] [IsNoetherianRing A]
  {hneg : ∀ n < 0, 𝓐 n = ⊥}
  (hzero : ∀ a ∈ 𝓐 0, ∃ c : k, algebraMap k A c = a)
  {V E : Type um} [PartialOrder V] [Fintype V] [Fintype E]
  {G : OrderedGraph V E} {α : E → A} {b : V}
  (B C : BoundarySheaf hneg G α b)
noncomputable section

 include hzero in
 theorem hom_vertex_bijective (f : GradedSheaf.Hom B.sheaf C.sheaf)
    (hb : Function.Bijective (f.vertex b).map) (x : V) :
    Function.Bijective (f.vertex x).map := by
  classical
  refine wellFounded_gt.induction (C := fun y => Function.Bijective (f.vertex y).map) x ?_
  intro x ih
  by_cases hx : x=b
  · subst x
    exact hb
  have he : ∀ e, x<G.target e → Function.Bijective (f.edge e).map :=
    fun e h => f.edge_bijective_of_vertex α B.quotient C.quotient e (ih _ h)
  let j := f.aboveIso x ih he
  apply j.stalk_hom_bijective hneg hzero
    (fun e h n v hv => (f.edge e).graded n v hv)
    (B.free x) (C.free x) B.flabby.flabby B.generated C.flabby.flabby C.generated
    (B.minimal x hx) (C.minimal x hx) (f.vertex x)
  intro v
  funext e
  change (f.edge e.val).map (B.sheaf.forget.stalkMap x v e)=
    C.sheaf.forget.stalkMap x ((f.vertex x).map v) e
  rcases e with ⟨e,he⟩
  subst x
  exact f.lower e v

 @[expose] def homIso (f : GradedSheaf.Hom B.sheaf C.sheaf)
    (hb : Function.Bijective (f.vertex b).map) : GradedSheaf.Iso B.sheaf C.sheaf :=
  f.isoOfBijective (hom_vertex_bijective hzero B C f hb)
    (fun e => f.edge_bijective_of_vertex α B.quotient C.quotient e
      (hom_vertex_bijective hzero B C f hb _))

end
end KLInvariance.MomentGraph.BoundarySheaf
end


section
namespace KLInvariance.MomentGraph.BoundarySheaf
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} [DirectSum.Decomposition 𝓐] [SetLike.GradedMonoid 𝓐]
  [IsDomain A] [IsNoetherianRing A]
  {hneg : ∀ n < 0, 𝓐 n = ⊥}
  (hzero : ∀ a ∈ 𝓐 0, ∃ c : k, algebraMap k A c = a)
  {V E : Type um} [PartialOrder V] [Fintype V] [Fintype E]
  {G : OrderedGraph V E} {α : E → A} {b : V}
  (B : BoundarySheaf hneg G α b) {C : GradedSheaf (𝓐 := 𝓐) G}
noncomputable section

 include hzero in
 theorem hom_vertex_bijective_of_iso (j : GradedSheaf.Iso B.sheaf C)
    (f : GradedSheaf.Hom B.sheaf C) (hb : Function.Bijective (f.vertex b).map)
    (x : V) : Function.Bijective (f.vertex x).map := by
  let g := j.invHom.comp f
  have hgb : Function.Bijective (g.vertex b).map := (j.vertex b).symm.bijective.comp hb
  have hg := hom_vertex_bijective hzero B B g hgb x
  constructor
  · intro v w h
    apply hg.1
    exact congrArg (j.vertex x).symm h
  · intro w
    obtain ⟨v,hv⟩ := hg.2 ((j.vertex x).symm w)
    exact ⟨v,(j.vertex x).symm.injective hv⟩

 @[expose] def homIsoOfIso (j : GradedSheaf.Iso B.sheaf C) (hq : C.UpperQuotient α)
    (f : GradedSheaf.Hom B.sheaf C) (hb : Function.Bijective (f.vertex b).map) :
    GradedSheaf.Iso B.sheaf C :=
  f.isoOfBijective (hom_vertex_bijective_of_iso hzero B j f hb)
    (fun e => f.edge_bijective_of_vertex α B.quotient hq e
      (hom_vertex_bijective_of_iso hzero B j f hb _))

end
end KLInvariance.MomentGraph.BoundarySheaf
end

end OAI
