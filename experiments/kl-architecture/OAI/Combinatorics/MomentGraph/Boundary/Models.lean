import Mathlib
import OAI.Combinatorics.MomentGraph.Boundary.Summand
import OAI.Combinatorics.MomentGraph.GradedSheaf.Models

/-! Semantic home: OAI.Combinatorics.MomentGraph.Boundary.Models. Source spans: CharacterReciprocity:17, CharacterReciprocity:28.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.MomentGraph.BoundarySheaf
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} [DirectSum.Decomposition 𝓐] [SetLike.GradedMonoid 𝓐]
  [IsDomain A] {hneg : ∀ n < 0, 𝓐 n=⊥}
  {V E : Type um} [PartialOrder V] {G : OrderedGraph V E} {α : E → A} {b : V}
  (B : BoundarySheaf hneg G α b)
noncomputable section

 theorem top_nontrivial : Nontrivial (B.sheaf.vertex b) := by
  let e := ModuleData.equivOfEq B.top
  let z : ModuleData.unit.{uk,ua,um} hneg := fun _ => (0 : A)
  let o : ModuleData.unit.{uk,ua,um} hneg := fun _ => (1 : A)
  refine ⟨⟨e.symm z,e.symm o,?_⟩⟩
  intro h
  exact zero_ne_one (congrFun (e.symm.injective h) PUnit.unit)

 variable [IsNoetherianRing A] [Fintype V] [Fintype E]

 theorem iso_of_primitive_top_split
    (hzero : ∀ a ∈ 𝓐 0, ∃ c : k, algebraMap k A c=a)
    (hb : ∀ x, x≤b) (C : GradedSheaf (𝓐 := 𝓐) G)
    (hCq : C.UpperQuotient α) (hCfree : ∀ x, Module.Free A (C.vertex x))
    (hCf : C.forget.Flabby) (hCg : C.forget.Generated)
    (hCp : (GradedSheaf.Hom.id C).PrimitiveProjector)
    (i : ModuleData.Hom (B.sheaf.vertex b) (C.vertex b))
    (p : ModuleData.Hom (C.vertex b) (B.sheaf.vertex b))
    (hpi : ∀ v, p.map (i.map v)=v) : Nonempty (GradedSheaf.Iso B.sheaf C) := by
  let := B.top_nontrivial
  obtain ⟨s⟩ := B.splitIn_of_top_split hzero hb C hCq hCfree hCf hCg i p hpi
  exact ⟨s.isoOfPrimitive hCp b⟩

end
end KLInvariance.MomentGraph.BoundarySheaf
end


section
namespace KLInvariance.MomentGraph.BoundarySheaf
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A B : Type ua} [CommRing A] [CommRing B]
  [Algebra k A] [Algebra k B]
  {𝓐 : ℤ → Submodule k A} {𝓑 : ℤ → Submodule k B}
  [DirectSum.Decomposition 𝓐] [SetLike.GradedMonoid 𝓐]
  [DirectSum.Decomposition 𝓑] [SetLike.GradedMonoid 𝓑]
  [IsDomain A] [IsDomain B] [IsNoetherianRing B]
  (e : A ≃ₐ[k] B) (he : ∀ n a, a∈𝓐 n ↔ e a∈𝓑 n)
  {hA : ∀ n<0,𝓐 n=⊥} {hB : ∀ n<0,𝓑 n=⊥}
  {V E : Type um} [PartialOrder V] [Fintype V] [Fintype E]
  {G : OrderedGraph V E} {α : E → A} {b : V}
  (S : BoundarySheaf hA G α b) (T : BoundarySheaf hB G (fun q => e (α q)) b)
noncomputable section

 theorem iso_coefficientChange
    (hzero : ∀ a ∈ 𝓑 0, ∃ c : k, algebraMap k B c=a)
    (hb : ∀ x, x≤b) : Nonempty
      (GradedSheaf.Iso T.sheaf (GradedSheaf.coefficientChange e he S.sheaf)) := by
  exact T.iso_of_primitive_top_split hzero hb (GradedSheaf.coefficientChange e he S.sheaf)
    (GradedSheaf.coefficientChange_upperQuotient e he S.sheaf α S.quotient)
    (GradedSheaf.coefficientChange_free e he S.sheaf S.free)
    (GradedSheaf.coefficientChange_flabby e he S.sheaf S.flabby.flabby)
    (GradedSheaf.coefficientChange_generated e he S.sheaf S.generated)
    (GradedSheaf.coefficientChange_primitive e he S.sheaf S.primitive_identity)
    (ModuleData.changeTopInclusion e he S.top T.top)
    (ModuleData.changeTopProjection e he S.top T.top)
    (ModuleData.changeTop_split e he S.top T.top)

end
end KLInvariance.MomentGraph.BoundarySheaf
end

end OAI
