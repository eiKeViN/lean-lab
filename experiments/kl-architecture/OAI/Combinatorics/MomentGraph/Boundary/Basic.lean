import Mathlib
import OAI.Combinatorics.MomentGraph.Sheaf.Isomorphism

/-! Semantic home: OAI.Combinatorics.MomentGraph.Boundary.Basic. Source spans: GradedSheaves:16.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.MomentGraph
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} [DirectSum.Decomposition 𝓐] [SetLike.GradedMonoid 𝓐]
  (hneg : ∀ n < 0, 𝓐 n = ⊥)

/-- The outcome of the actual minimal boundary construction. Full upward-kernel
freeness, integral duality and KL characters are NOT part of this structure. -/
structure BoundarySheaf {V E : Type um} [PartialOrder V] (G : OrderedGraph V E)
    (α : E → A) (b : V) where
  sheaf : GradedSheaf (𝓐 := 𝓐) G
  free : sheaf.FreeStalks
  quotient : sheaf.UpperQuotient α
  flabby : sheaf.EdgeFlabby
  generated : sheaf.forget.Generated
  top : sheaf.vertex b = ModuleData.unit hneg
  minimal : ∀ x, x ≠ b → sheaf.KernelMinimal x

variable {V E : Type um} [PartialOrder V] (G : OrderedGraph V E)

noncomputable def singletonSheaf [IsEmpty E] : GradedSheaf (𝓐 := 𝓐) G where
  vertex := fun _ => ModuleData.unit hneg
  edge := isEmptyElim
  lower := isEmptyElim
  upper := isEmptyElim

 theorem singleton_boundarySheaf (b : V) (hV : ∀ x, x=b) (α : E → A) :
    Nonempty (BoundarySheaf hneg G α b) := by
  have hempty : IsEmpty E := ⟨fun e => (G.increasing e).ne ((hV _).trans (hV _).symm)⟩
  let := hempty
  let B := singletonSheaf hneg G
  refine ⟨⟨B,?_,?_,?_,?_,rfl,?_⟩⟩
  · intro x
    exact ModuleData.unit_free hneg
  · intro e
    exact isEmptyElim e
  · intro Ω _ f _
    exact ⟨f,fun e => isEmptyElim e,fun _ _ => rfl⟩
  · intro x v
    exact ⟨fun _ => v,fun e => isEmptyElim e,rfl⟩
  · intro x hx
    exact (hx (hV x)).elim

variable [IsNoetherianRing A]
  (hscalar : ∀ a : A, ∃ c : k, a-algebraMap k A c ∈ positiveIdeal 𝓐)

include hscalar in
 theorem exists_boundarySheaf_card (n : ℕ)
    [Fintype V] [Fintype E] (b : V) (hb : ∀ x, x ≤ b)
    (α : E → A) (hα : ∀ e, α e ∈ 𝓐 1) (hn : Fintype.card V = n) :
    Nonempty (BoundarySheaf hneg G α b) := by
  classical
  induction n using Nat.strong_induction_on generalizing V E with
  | h n ih =>
    by_cases hV : ∀ x : V, x=b
    · exact singleton_boundarySheaf hneg G b hV α
    obtain ⟨y,hy⟩ := not_forall.mp hV
    obtain ⟨x,hx⟩ := exists_minimal_of_wellFoundedLT (fun _ : V => True) ⟨b,trivial⟩
    have hxb : x ≠ b := by
      intro he
      have hlt : y < x := he ▸ lt_of_le_of_ne (hb y) hy
      exact hx.not_lt trivial hlt
    have ht (e : E) : G.target e ≠ x := by
      intro he
      exact hx.not_lt trivial (he ▸ G.increasing e)
    let V' := {y : V // y ≠ x}
    let E' := {e : E // G.source e ≠ x}
    let D := {e : E // G.source e = x}
    let G' := removeGraph G x ht
    let τ := removeTarget G x ht
    let b' : V' := ⟨b,hxb.symm⟩
    let α' : E' → A := fun e => α e.val
    let β : D → A := fun e => α e.val
    have hβ : ∀ e : D, β e ∈ 𝓐 1 := fun e => hα e.val
    have hcard : Fintype.card V' < n := by
      rw [← hn]
      exact Fintype.card_subtype_lt (x := x) (not_not.mpr rfl)
    obtain ⟨B⟩ := ih (Fintype.card V') hcard G' b' (fun y => hb y.val)
      α' (fun e => hα e.val) rfl
    obtain ⟨C⟩ := ModuleData.exists_minimalCover hneg hscalar (B.sheaf.attachImage τ β hβ)
    let H := B.sheaf.extendBottom τ β hβ C
    let e := splitGraph G x ht
    refine ⟨⟨H.reindex e,?_,?_,?_,?_,?_,?_⟩⟩
    · exact H.reindex_freeStalks e (B.sheaf.extendBottom_freeStalks τ β hβ C B.free)
    · have hh := H.reindex_upperQuotient e
        (B.sheaf.extendBottom_upperQuotient τ β hβ C B.quotient)
      have he : (Sum.elim α' β) ∘ e.edge = α := splitEdge_labels G α x
      exact he ▸ hh
    · exact H.reindex_edgeFlabby e (B.sheaf.extendBottom_edgeFlabby τ β hβ C B.flabby)
    · exact H.reindex_generated e (B.sheaf.extendBottom_generated τ β hβ C B.generated)
    · change H.vertex (splitVertex x b) = _
      rw [splitVertex_ne x b hxb.symm]
      exact B.top
    · intro z hz
      apply H.reindex_kernelMinimal e z
      by_cases hzx : z=x
      · subst z
        change H.KernelMinimal (splitVertex x x)
        rw [splitVertex_self]
        exact B.sheaf.extendBottom_kernelMinimal_bot τ β hβ C
      · change H.KernelMinimal (splitVertex x z)
        rw [splitVertex_ne x z hzx]
        apply B.sheaf.extendBottom_kernelMinimal_coe τ β hβ C ⟨z,hzx⟩
        apply B.minimal
        intro hzz
        exact hz (congrArg Subtype.val hzz)

include hscalar in
 theorem exists_boundarySheaf [Fintype V] [Fintype E] (b : V) (hb : ∀ x, x ≤ b)
    (α : E → A) (hα : ∀ e, α e ∈ 𝓐 1) : Nonempty (BoundarySheaf hneg G α b) :=
  exists_boundarySheaf_card hneg G hscalar (Fintype.card V) b hb α hα rfl

end KLInvariance.MomentGraph
end

end OAI
