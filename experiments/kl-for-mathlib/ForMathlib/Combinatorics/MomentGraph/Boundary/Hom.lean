module
public import Mathlib
public import ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Hom

public section

/-! Semantic home: ForMathlib.Combinatorics.MomentGraph.Boundary.Hom. Source spans: SheafMorphisms:18, SheafMorphisms:21, SheafMorphisms:24.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.MomentGraph.BoundarySheaf
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} [DirectSum.Decomposition 𝓐] [SetLike.GradedMonoid 𝓐]
  {hneg : ∀ n < 0, 𝓐 n = ⊥} {V E : Type um} [PartialOrder V]
  {G : OrderedGraph V E} {α : E → A} {b : V}
  (B : BoundarySheaf hneg G α b)

 theorem idempotent_zero_of_top_zero [Finite V]
    (f : B.sheaf.Endomorphism)
    (hi : ∀ x v, (f.vertex x).map ((f.vertex x).map v) = (f.vertex x).map v)
    (ht : (f.vertex b).map = 0) :
    (∀ x, (f.vertex x).map = 0) ∧ (∀ e, (f.edge e).map = 0) := by
  have hv : ∀ x, (f.vertex x).map = 0 := by
    intro x
    induction x using WellFoundedGT.induction with
    | ind x ih =>
      by_cases hx : x=b
      · exact hx ▸ ht
      apply ModuleData.idempotent_eq_zero (B.sheaf.vertex x) (f.vertex x) (hi x)
      intro v hv
      obtain ⟨w,rfl⟩ := hv
      apply (B.sheaf.kernelMinimal_iff x).mp (B.minimal x hx)
      change B.sheaf.forget.stalkMap x ((f.vertex x).map w) = 0
      funext e
      rcases e with ⟨e,he⟩
      subst x
      change (B.sheaf.lower e).map ((f.vertex (G.source e)).map w) = 0
      rw [← f.lower]
      have hezero : (f.edge e).map = 0 := by
        ext z
        obtain ⟨y,rfl⟩ := (B.quotient e).1 z
        rw [f.upper,ih (G.target e) (G.increasing e)]
        exact map_zero _
      rw [hezero]
      rfl
  refine ⟨hv,?_⟩
  intro e
  ext z
  obtain ⟨y,rfl⟩ := (B.quotient e).1 z
  rw [f.upper,hv]
  exact map_zero _

/-- Actual indecomposability in the idempotent formulation. A direct sum
splitting supplies such a homogeneous idempotent, hence one summand vanishes. -/
 theorem idempotent_trivial [Finite V] [IsDomain A]
    (f : B.sheaf.Endomorphism)
    (hi : ∀ x v, (f.vertex x).map ((f.vertex x).map v) = (f.vertex x).map v) :
    ((∀ x, (f.vertex x).map = 0) ∧ (∀ e, (f.edge e).map = 0)) ∨
      ((∀ x, (f.vertex x).map = LinearMap.id) ∧
        (∀ e, (f.edge e).map = LinearMap.id)) := by
  have ht : (f.vertex b).map = 0 ∨ (f.vertex b).map = LinearMap.id := by
    have h := B.top
    have general (N : ModuleData.{uk,ua,um} 𝓐) (hN : N=ModuleData.unit hneg)
        (g : ModuleData.Hom N N) (hg : ∀v, g.map (g.map v)=g.map v) :
        g.map=0 ∨ g.map=LinearMap.id := by
      subst N
      exact ModuleData.unit_idempotent_trivial hneg g hg
    exact general _ h (f.vertex b) (hi b)
  rcases ht with ht | ht
  · exact Or.inl (B.idempotent_zero_of_top_zero f hi ht)
  · right
    have hh : (f.complement.vertex b).map = 0 := by
      change LinearMap.id - (f.vertex b).map = 0
      rw [ht,sub_self]
    obtain ⟨hv,he⟩ := B.idempotent_zero_of_top_zero f.complement
      (f.complement_idempotent hi) hh
    constructor
    · intro x
      exact (sub_eq_zero.mp (hv x)).symm
    · intro e
      exact (sub_eq_zero.mp (he e)).symm

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
  (B : BoundarySheaf hneg G α b)
noncomputable section

include hzero in
 theorem endomorphism_bijective_of_top (f : B.sheaf.Endomorphism)
    (ht : Function.Bijective (f.vertex b).map) :
    (∀ x, Function.Bijective (f.vertex x).map) ∧
    (∀ e, Function.Bijective (f.edge e).map) := by
  have hv : ∀ x, Function.Bijective (f.vertex x).map := by
    intro x
    induction x using WellFoundedGT.induction with
    | ind x ih =>
      by_cases hx : x=b
      · exact hx ▸ ht
      let j : Sheaf.AboveIso B.sheaf.forget B.sheaf.forget x :=
        { vertex y hy := LinearEquiv.ofBijective (f.vertex y).map (ih y hy)
          edge e he := LinearEquiv.ofBijective (f.edge e).map
            (f.edge_bijective_of_vertex B.quotient e (ih _ he))
          lower e he v := f.lower e v
          upper e he v := f.upper e v }
      let T := ModuleData.range (B.sheaf.stalkHom x)
      let g : T ≃ₗ[A] T := LinearEquiv.ofSubmodules j.boundary _ _
        (j.map_stalk_image B.flabby.flabby B.generated B.flabby.flabby B.generated)
      have hg : ∀ n v, v ∈ T.piece n → g v ∈ T.piece n := by
        intro n v hv e he
        exact (f.edge e.val).graded n _ (hv e he)
      let π : ModuleData.Hom (B.sheaf.vertex x) T :=
        { map := (B.sheaf.forget.stalkMap x).rangeRestrict
          graded := fun n v hv => (B.sheaf.stalkHom x).graded n v hv }
      have hπs : Function.Surjective π.map := by
        intro v
        obtain ⟨w,hw⟩ := v.property
        exact ⟨w,Subtype.ext hw⟩
      have hπm : LinearMap.ker π.map ≤
          positiveIdeal 𝓐 • (⊤ : Submodule A (B.sheaf.vertex x)) := by
        intro v hv
        apply (B.sheaf.kernelMinimal_iff x).mp (B.minimal x hx)
        have hh : π.map v = 0 := LinearMap.mem_ker.mp hv
        exact congrArg (fun z : T => z.val) hh
      let C : ModuleData.MinimalCover T := ⟨B.sheaf.vertex x,B.free x,π,hπs,hπm⟩
      apply C.bijective_of_boundaryIso hneg hzero (f.vertex x) g hg
      intro v
      apply Subtype.ext
      funext e
      change B.sheaf.forget.stalkMap x ((f.vertex x).map v) e =
        (f.edge e.val).map (B.sheaf.forget.stalkMap x v e)
      rcases e with ⟨e,rfl⟩
      exact (f.lower e v).symm
  exact ⟨hv,fun e => f.edge_bijective_of_vertex B.quotient e (hv _)⟩

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
  (B : BoundarySheaf hneg G α b) (hb : ∀ x, x ≤ b)
  (C : GradedSheaf (𝓐 := 𝓐) G)
  (hCq : C.UpperQuotient α) (hCfree : ∀ x, Module.Free A (C.vertex x))
  (hCf : C.forget.Flabby) (hCg : C.forget.Generated)
noncomputable section

include hzero hb hCq hCfree hCf hCg in
 theorem splitIn_of_top_split
    (i : ModuleData.Hom (B.sheaf.vertex b) (C.vertex b))
    (p : ModuleData.Hom (C.vertex b) (B.sheaf.vertex b))
    (hpi : ∀ v, p.map (i.map v)=v) : Nonempty (GradedSheaf.SplitIn B.sheaf C) := by
  obtain ⟨ii,hii⟩ := GradedSheaf.exists_hom_top hneg hzero α B.quotient hCq B.free
    B.flabby.flabby B.generated hCf hCg b hb i
  obtain ⟨pp,hpp⟩ := GradedSheaf.exists_hom_top hneg hzero α hCq B.quotient hCfree
    hCf hCg B.flabby.flabby B.generated b hb p
  let f := pp.comp ii
  have ht : Function.Bijective (f.toEndomorphism.vertex b).map := by
    have heq : (f.toEndomorphism.vertex b).map = LinearMap.id := by
      apply LinearMap.ext
      intro v
      change (pp.vertex b).map ((ii.vertex b).map v)=v
      rw [hpp,hii]
      exact hpi v
    rw [heq]
    exact Function.bijective_id
  obtain ⟨hv,he⟩ := B.endomorphism_bijective_of_top hzero f.toEndomorphism ht
  let fi := f.inverse hv he
  refine ⟨⟨ii.comp fi,pp,?_,?_⟩⟩
  · intro x v
    exact (f.vertex x).map_inverse (hv x) v
  · intro e v
    exact (f.edge e).map_inverse (he e) v

end
end KLInvariance.MomentGraph.BoundarySheaf
end

end OAI
