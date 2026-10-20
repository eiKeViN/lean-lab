import Mathlib
import OAI.Combinatorics.MomentGraph.Boundary.Uniqueness
import OAI.RepresentationTheory.BottSamelson.Character

/-! Semantic home: OAI.RepresentationTheory.BottSamelson.CanonicalPairing. Source spans: EdgeLocalization:15, EdgeLocalization:16, EdgeLocalization:18.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.TitsSpace
open Module _root_.OAI.KLInvariance.Graded MomentGraph BruhatGraph
universe u us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  (l : List I) (hl : cs.IsReduced l)
  (B : BoundarySheaf (symmetricGrading_negative basis)
    (graph cs 1 (cs.wordProd l)) (symmetricLabel cs 1 (cs.wordProd l))
    ⟨cs.wordProd l,one_bruhat cs _,bruhat_refl cs _⟩)
  (s : GradedSheaf.SplitIn B.sheaf (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l)))
noncomputable section

 def bottCanonicalAdjointHom : GradedSheaf.Hom B.sheaf
    (bottSplitAdjointSheaf cs basis l hl B.sheaf s) :=
  (bottSplitAdjointSplit cs basis l hl B s).projection.comp s.inclusion

 theorem bottCanonicalAdjointHom_top_bijective : Function.Bijective
    ((bottCanonicalAdjointHom cs basis l hl B s).vertex
      ⟨cs.wordProd l,one_bruhat cs _,bruhat_refl cs _⟩).map := by
  apply s.comparison_bijective (bottSplitAdjointSplit cs basis l hl B s)
  · exact bottBoundarySplit_top_fixed cs basis l hl _ B s
  · exact bottBoundarySplitAdjoint_top_fixed cs basis l hl _ B s

 def bottCanonicalAdjointIso : GradedSheaf.Iso B.sheaf
    (bottSplitAdjointSheaf cs basis l hl B.sheaf s) := by
  classical
  let := symmetricCoefficientNoetherian basis
  let := interval_finite cs 1 (cs.wordProd l)
  let := Fintype.ofFinite (Interval cs 1 (cs.wordProd l))
  let := Fintype.ofFinite (Edge cs 1 (cs.wordProd l))
  let j := (bottBoundarySheaf_iso_adjoint cs basis l hl B s).some
  exact B.homIsoOfIso (symmetricGrading_zero basis) j
    ((bottSplitAdjointSplit cs basis l hl B s).upperQuotient
      (bottGradedProjectionSheaf_upperQuotient cs basis l 1 (cs.wordProd l)))
    (bottCanonicalAdjointHom cs basis l hl B s)
    (bottCanonicalAdjointHom_top_bijective cs basis l hl B s)

 theorem bottCanonicalAdjointIso_vertex (x : Interval cs 1 (cs.wordProd l))
    (v : B.sheaf.vertex x) :
    ((bottCanonicalAdjointIso cs basis l hl B s).vertex x v).val=
      ((bottAdjointSheaf cs basis l hl s.projector).vertex x).map
        ((s.inclusion.vertex x).map v) := rfl

end
end KLInvariance.TitsSpace
end


section
namespace KLInvariance.TitsSpace
open Module _root_.OAI.KLInvariance.Graded MomentGraph BruhatGraph
universe u us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  (l : List I) (hl : cs.IsReduced l)
  (B : BoundarySheaf (symmetricGrading_negative basis)
    (graph cs 1 (cs.wordProd l)) (symmetricLabel cs 1 (cs.wordProd l))
    ⟨cs.wordProd l,one_bruhat cs _,bruhat_refl cs _⟩)
  (s : GradedSheaf.SplitIn B.sheaf (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l)))
noncomputable section

 theorem bottSplitRightWord_fixed (n : B.sheaf.forget.sections Set.univ) :
    bottEndOfSheaf cs basis l hl s.projector (bottSplitRightWord cs basis l hl B.sheaf s n)=
      bottSplitRightWord cs basis l hl B.sheaf s n := by
  apply bottVertexProjection_injective cs l hl
  funext x
  change bottStalkProjection cs l x.val _=bottStalkProjection cs l x.val _
  rw [bottEndOfSheaf_coordinates,bottSplitRightWord_coordinates]
  change (s.inclusion.vertex x).map
      ((s.projection.vertex x).map ((s.inclusion.vertex x).map (n.val x)))=
    (s.inclusion.vertex x).map (n.val x)
  exact congrArg (s.inclusion.vertex x).map (s.vertex_split x (n.val x))

 theorem bottCanonicalAdjointWord (m : B.sheaf.forget.sections Set.univ) :
    bottSplitLeftWord cs basis l hl B.sheaf s
      ((bottCanonicalAdjointIso cs basis l hl B s).toIso.sections Set.univ m)=
    bottAdjoint cs l (bottEndOfSheaf cs basis l hl s.projector)
      (bottSplitRightWord cs basis l hl B.sheaf s m) := by
  apply bottVertexProjection_injective cs l hl
  funext x
  change bottStalkProjection cs l x.val _=bottStalkProjection cs l x.val _
  rw [bottSplitLeftWord_coordinates]
  exact (bottCanonicalAdjointIso_vertex cs basis l hl B s x (m.val x)).trans
    ((congrArg ((bottAdjointSheaf cs basis l hl s.projector).vertex x).map
      (bottSplitRightWord_coordinates cs basis l hl B.sheaf s m x).symm).trans
      (bottAdjointSheaf_vertex cs basis l hl s.projector x _))

 def bottCanonicalPerfectPairing : GradedSheaf.PerfectPairing B.sheaf (l.length : ℤ) :=
  bottRecognizedPerfectPairing cs basis l hl B.sheaf s
    (bottCanonicalAdjointIso cs basis l hl B s)

 theorem bottCanonicalPerfectPairing_apply (m n : B.sheaf.forget.sections Set.univ) :
    (bottCanonicalPerfectPairing cs basis l hl B s).pairing m n=
      bottSamelsonDuality cs l (bottSplitRightWord cs basis l hl B.sheaf s m)
        (bottSplitRightWord cs basis l hl B.sheaf s n) := by
  change bottSplitAdjointEquivDual cs basis l hl B.sheaf s
    ((bottCanonicalAdjointIso cs basis l hl B s).toIso.sections Set.univ m) n=_
  rw [bottSplitAdjointWord_apply,bottCanonicalAdjointWord]
  change bottSamelsonDuality cs l
    (PerfectAdjoint.adjoint (bottSamelsonDuality cs l)
      (bottEndOfSheaf cs basis l hl s.projector) _) _=_
  rw [PerfectAdjoint.pairing,bottSplitRightWord_fixed]

 theorem bottCanonicalPerfectPairing_symmetric (m n : B.sheaf.forget.sections Set.univ) :
    (bottCanonicalPerfectPairing cs basis l hl B s).pairing m n=
      (bottCanonicalPerfectPairing cs basis l hl B s).pairing n m := by
  exact (bottCanonicalPerfectPairing_apply cs basis l hl B s m n).trans
    ((bottSamelson_symmetric cs l _ _).trans
      (bottCanonicalPerfectPairing_apply cs basis l hl B s n m).symm)

end
end KLInvariance.TitsSpace
end


section
namespace KLInvariance.TitsSpace
open Module _root_.OAI.KLInvariance.Graded MomentGraph BruhatGraph
universe u us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
noncomputable section

 theorem symmetricBoundarySheaf_symmetricPairing_word (l : List I) (hl : cs.IsReduced l)
    (B : BoundarySheaf (symmetricGrading_negative basis)
      (graph cs 1 (cs.wordProd l)) (symmetricLabel cs 1 (cs.wordProd l))
      ⟨cs.wordProd l,one_bruhat cs _,bruhat_refl cs _⟩) :
    Nonempty (GradedSheaf.SymmetricPerfectPairing B.sheaf (cs.length (cs.wordProd l) : ℤ)) := by
  obtain ⟨s⟩ := bottBoundarySheaf_splitIn cs basis l hl B
  have hd : cs.length (cs.wordProd l)=l.length := hl
  rw [hd]
  exact ⟨{ toPerfectPairing := bottCanonicalPerfectPairing cs basis l hl B s
           symmetric := bottCanonicalPerfectPairing_symmetric cs basis l hl B s }⟩

 theorem symmetricBoundarySheaf_symmetricPairing (b : W) :
    Nonempty (GradedSheaf.SymmetricPerfectPairing
      (symmetricBoundarySheaf cs basis b).sheaf (cs.length b : ℤ)) := by
  obtain ⟨l,hl,he⟩ := cs.exists_isReduced b
  subst b
  exact symmetricBoundarySheaf_symmetricPairing_word cs basis l hl _

end
end KLInvariance.TitsSpace
end

end OAI
