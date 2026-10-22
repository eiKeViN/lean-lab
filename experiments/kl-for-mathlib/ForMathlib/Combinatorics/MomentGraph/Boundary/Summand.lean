import Mathlib
import ForMathlib.Combinatorics.MomentGraph.Boundary.Hom
import ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Summand

/-! Semantic home: ForMathlib.Combinatorics.MomentGraph.Boundary.Summand. Source spans: BalancedPairings:33.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.MomentGraph.BoundarySheaf
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} [DirectSum.Decomposition 𝓐] [SetLike.GradedMonoid 𝓐]
  {hneg : ∀ n < 0, 𝓐 n=⊥} {V E : Type um} [PartialOrder V] [Finite V]
  {G : OrderedGraph V E} {α : E → A} {b : V} [IsDomain A]
  (B : BoundarySheaf hneg G α b)

 theorem primitive_identity : (GradedSheaf.Hom.id B.sheaf).PrimitiveProjector := by
  constructor
  · apply GradedSheaf.Hom.eq_of_maps <;> intros <;> rfl
  · intro f hf _ _
    have hi : ∀ x v, (f.toEndomorphism.vertex x).map ((f.toEndomorphism.vertex x).map v)=
        (f.toEndomorphism.vertex x).map v := by
      intro x v
      exact congrArg (fun q : GradedSheaf.Hom B.sheaf B.sheaf => (q.vertex x).map v) hf
    rcases B.idempotent_trivial f.toEndomorphism hi with hz | hi
    · left
      apply GradedSheaf.Hom.eq_of_maps
      · intro x v
        exact LinearMap.congr_fun (hz.1 x) v
      · intro e v
        exact LinearMap.congr_fun (hz.2 e) v
    · right
      apply GradedSheaf.Hom.eq_of_maps
      · intro x v
        exact LinearMap.congr_fun (hi.1 x) v
      · intro e v
        exact LinearMap.congr_fun (hi.2 e) v

 theorem split_projector_primitive
    {C : GradedSheaf (𝓐 := 𝓐) G} (s : GradedSheaf.SplitIn B.sheaf C) :
    s.projector.PrimitiveProjector :=
  s.primitive_projector_of_id B.primitive_identity

end KLInvariance.MomentGraph.BoundarySheaf
end

end OAI
