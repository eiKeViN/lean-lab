import Lean
import Mathlib
import ForMathlib.Combinatorics.MomentGraph.Boundary.Models
import ForMathlib.RepresentationTheory.Hecke.PositiveWord
import OAI.KL.BottSamelson.Support
import OAI.KL.Sheaves.FreeModel
import OAI.KL.BottSamelson.StalkCharacter
import OAI.KL.BottSamelson.Flabby

/-! Semantic home: OAI.KL.BottSamelson.Character. Source spans: CharacterReciprocity:20, CharacterReciprocity:21, CharacterReciprocity:18, CharacterReciprocity:22, CharacterReciprocity:23, CharacterReciprocity:12, CharacterReciprocity:16.
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
  (B : GradedSheaf (𝓐 := symmetricGrading basis) (graph cs 1 (cs.wordProd l)))
  (s : GradedSheaf.SplitIn B (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l)))
noncomputable section

 def bottSplitRightWord (n : B.forget.sections Set.univ) : BottSamelsonModule cs l := by
  let := symmetricCoefficientNoetherian basis
  exact (bottImageSectionWordEquiv cs basis l hl s.projector s.projector_vertex
    ((s.imageSectionEquiv Set.univ).symm n)).val

 def bottSplitLeftWord
    (m : (bottSplitAdjointSheaf cs basis l hl B s).forget.sections Set.univ) :
    BottSamelsonModule cs l := by
  let := symmetricCoefficientNoetherian basis
  exact (bottImageSectionWordEquiv cs basis l hl (bottAdjointSheaf cs basis l hl s.projector)
    (bottAdjointSheaf_vertex_idempotent cs basis l hl s.projector s.projector_vertex) m).val

 theorem bottSplitRightWord_coordinates (n : B.forget.sections Set.univ)
    (x : Interval cs 1 (cs.wordProd l)) :
    bottStalkProjection cs l x.val (bottSplitRightWord cs basis l hl B s n)=
      (s.inclusion.vertex x).map (n.val x) := by
  let := symmetricCoefficientNoetherian basis
  exact (bottImageSectionWordEquiv_coordinates cs basis l hl s.projector s.projector_vertex
    ((s.imageSectionEquiv Set.univ).symm n) x).trans
      (s.imageSectionEquiv_symm_coordinates Set.univ n x)

 theorem bottSplitLeftWord_coordinates
    (m : (bottSplitAdjointSheaf cs basis l hl B s).forget.sections Set.univ)
    (x : Interval cs 1 (cs.wordProd l)) :
    bottStalkProjection cs l x.val (bottSplitLeftWord cs basis l hl B s m)=(m.val x).val := by
  let := symmetricCoefficientNoetherian basis
  exact bottImageSectionWordEquiv_coordinates cs basis l hl
    (bottAdjointSheaf cs basis l hl s.projector)
    (bottAdjointSheaf_vertex_idempotent cs basis l hl s.projector s.projector_vertex) m x

 theorem bottSplitAdjointWord_apply
    (m : (bottSplitAdjointSheaf cs basis l hl B s).forget.sections Set.univ)
    (n : B.forget.sections Set.univ) :
    bottSplitAdjointEquivDual cs basis l hl B s m n=
      bottSamelsonDuality cs l (bottSplitLeftWord cs basis l hl B s m)
        (bottSplitRightWord cs basis l hl B s n) := by
  let := symmetricCoefficientNoetherian basis
  exact bottAdjointImageEquivDual_apply cs basis l hl s.projector s.projector_vertex m
    ((s.imageSectionEquiv Set.univ).symm n)

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
  (B : GradedSheaf (𝓐 := symmetricGrading basis) (graph cs 1 (cs.wordProd l)))
  (s : GradedSheaf.SplitIn B (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l)))
  (j : GradedSheaf.Iso B (bottSplitAdjointSheaf cs basis l hl B s))
noncomputable section

 def bottRecognizedPerfectPairing : GradedSheaf.PerfectPairing B (l.length : ℤ) where
  pairing := (j.toIso.sections Set.univ).trans (bottSplitAdjointEquivDual cs basis l hl B s)
  homogeneous i q m n hm hn := bottSplitAdjointPairing_homogeneous cs basis l hl B s i q
    (j.toIso.sections Set.univ m) n (fun x => j.vertex_graded x i _ (hm x)) hn
  left_orthogonal x m n hm hn := by
    change bottSplitAdjointEquivDual cs basis l hl B s (j.toIso.sections Set.univ m) n=0
    rw [bottSplitAdjointWord_apply]
    apply bottStalk_supported_annihilates cs l hl x
    · intro y hy
      rw [bottSplitLeftWord_coordinates]
      change ((j.vertex y (m.val y)).val)=0
      rw [hm y hy,map_zero]
      rfl
    · rw [bottSplitRightWord_coordinates]
      change (s.inclusion.vertex x).map (n.val x)=0
      rw [hn]
      exact (s.inclusion.vertex x).map.map_zero
  right_orthogonal x m n hm hn := by
    change bottSplitAdjointEquivDual cs basis l hl B s (j.toIso.sections Set.univ m) n=0
    rw [bottSplitAdjointWord_apply,bottSamelson_symmetric]
    apply bottStalk_supported_annihilates cs l hl x
    · intro y hy
      rw [bottSplitRightWord_coordinates]
      change (s.inclusion.vertex y).map (n.val y)=0
      rw [hn y hy]
      exact (s.inclusion.vertex y).map.map_zero
    · rw [bottSplitLeftWord_coordinates]
      change ((j.vertex x (m.val x)).val)=0
      rw [hm,map_zero]
      rfl

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

 def bottSplitAdjointSplit : GradedSheaf.SplitIn
    (bottSplitAdjointSheaf cs basis l hl B.sheaf s)
    (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l)) := by
  let := symmetricCoefficientNoetherian basis
  exact (bottAdjointSheaf cs basis l hl s.projector).imageSplit
    (bottAdjointSheaf_vertex_idempotent cs basis l hl s.projector s.projector_vertex)
    (bottAdjointSheaf_edge_idempotent cs basis l hl s.projector s.projector_vertex)

 theorem bottSplitAdjoint_free (x : Interval cs 1 (cs.wordProd l)) :
    Module.Free (SymmetricCoefficient (M := M))
      ((bottSplitAdjointSheaf cs basis l hl B.sheaf s).vertex x) := by
  let := symmetricCoefficientNoetherian basis
  let : Module.Free (SymmetricCoefficient (M := M))
      ((bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l)).vertex x) :=
    bottStalkFree cs l x.val
  exact (bottSplitAdjointSplit cs basis l hl B s).vertex_free
    (symmetricGrading_negative basis) (symmetricGrading_zero basis) x

 def bottSplitAdjointTopInclusion : ModuleData.Hom
    (B.sheaf.vertex ⟨cs.wordProd l,one_bruhat cs _,bruhat_refl cs _⟩)
    ((bottSplitAdjointSheaf cs basis l hl B.sheaf s).vertex
      ⟨cs.wordProd l,one_bruhat cs _,bruhat_refl cs _⟩) :=
  ((bottSplitAdjointSplit cs basis l hl B s).projection.vertex _).comp
    (bottBoundarySheafTopInclusion cs basis l hl B)

 def bottSplitAdjointTopProjection : ModuleData.Hom
    ((bottSplitAdjointSheaf cs basis l hl B.sheaf s).vertex
      ⟨cs.wordProd l,one_bruhat cs _,bruhat_refl cs _⟩)
    (B.sheaf.vertex ⟨cs.wordProd l,one_bruhat cs _,bruhat_refl cs _⟩) :=
  (bottBoundarySheafTopProjection cs basis l hl B).comp
    ((bottSplitAdjointSplit cs basis l hl B s).inclusion.vertex _)

 theorem bottSplitAdjointTop_split
    (v : B.sheaf.vertex ⟨cs.wordProd l,one_bruhat cs _,bruhat_refl cs _⟩) :
    (bottSplitAdjointTopProjection cs basis l hl B s).map
      ((bottSplitAdjointTopInclusion cs basis l hl B s).map v)=v := by
  change (bottBoundarySheafTopProjection cs basis l hl B).map
    (((bottAdjointSheaf cs basis l hl s.projector).vertex
      ⟨cs.wordProd l,one_bruhat cs _,bruhat_refl cs _⟩).map
      ((bottBoundarySheafTopInclusion cs basis l hl B).map v))=v
  exact (congrArg (bottBoundarySheafTopProjection cs basis l hl B).map
    (bottBoundarySplitAdjoint_top_fixed cs basis l hl _ B s
      ((bottBoundarySheafTopInclusion cs basis l hl B).map v))).trans
    (bottBoundarySheafTop_split cs basis l hl B v)

 theorem bottBoundarySheaf_iso_adjoint : Nonempty
    (GradedSheaf.Iso B.sheaf (bottSplitAdjointSheaf cs basis l hl B.sheaf s)) := by
  classical
  let := symmetricCoefficientNoetherian basis
  let := interval_finite cs 1 (cs.wordProd l)
  let := Fintype.ofFinite (Interval cs 1 (cs.wordProd l))
  let := Fintype.ofFinite (Edge cs 1 (cs.wordProd l))
  let t := bottSplitAdjointSplit cs basis l hl B s
  exact B.iso_of_primitive_top_split (symmetricGrading_zero basis) (fun x => x.property.2)
    (bottSplitAdjointSheaf cs basis l hl B.sheaf s)
    (t.upperQuotient (bottGradedProjectionSheaf_upperQuotient cs basis l 1 (cs.wordProd l)))
    (bottSplitAdjoint_free cs basis l hl B s)
    (t.flabby (bottProjectionSheaf_flabby cs l hl))
    (t.generated (bottProjectionSheaf_generated cs l 1 (cs.wordProd l)))
    (bottBoundarySplitAdjoint_primitive cs basis l hl _ B s)
    (bottSplitAdjointTopInclusion cs basis l hl B s)
    (bottSplitAdjointTopProjection cs basis l hl B s)
    (bottSplitAdjointTop_split cs basis l hl B s)

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

 omit [Fintype σ] in
 theorem symmetric_scalar_mod_positive (a : SymmetricCoefficient (M := M)) :
    ∃ c : ℝ, a-algebraMap ℝ (SymmetricCoefficient (M := M)) c ∈ positiveIdeal (symmetricGrading basis) := by
  obtain ⟨c,hc⟩ := symmetricGrading_zero basis _
    (DirectSum.decompose (symmetricGrading basis) a 0).property
  refine ⟨c,?_⟩
  rw [positiveIdeal_eq_augmentation_ker _ (symmetricGrading_negative basis)]
  change component (symmetricGrading basis) 0 (a-algebraMap ℝ (SymmetricCoefficient (M := M)) c)=0
  rw [map_sub,hc]
  rw [show component (symmetricGrading basis) 0
    (DirectSum.decompose (symmetricGrading basis) a 0 : SymmetricCoefficient (M := M)) =
    (DirectSum.decompose (symmetricGrading basis) a 0 : SymmetricCoefficient (M := M)) from
    DirectSum.decompose_of_mem_same _ (DirectSum.decompose (symmetricGrading basis) a 0).property]
  exact sub_self _

 theorem symmetricLabel_homogeneous (u b : W) (e : Edge cs u b) :
    symmetricLabel cs u b e ∈ symmetricGrading basis 1 :=
  (mem_symmetricGrading basis 1 _).mpr (polynomialLabel_homogeneous cs u b basis e)

 theorem exists_symmetricBoundarySheaf (b : W) :
    Nonempty (BoundarySheaf (symmetricGrading_negative basis)
      (graph cs 1 b) (symmetricLabel cs 1 b) ⟨b,one_bruhat cs b,bruhat_refl cs b⟩) := by
  classical
  let := symmetricCoefficientNoetherian basis
  let := interval_finite cs 1 b
  let := Fintype.ofFinite (Interval cs 1 b)
  let := Fintype.ofFinite (Edge cs 1 b)
  exact MomentGraph.exists_boundarySheaf (symmetricGrading_negative basis)
    (graph cs 1 b) (symmetric_scalar_mod_positive basis)
    ⟨b,one_bruhat cs b,bruhat_refl cs b⟩ (fun x => x.property.2)
    (symmetricLabel cs 1 b) (symmetricLabel_homogeneous cs basis 1 b)

 def symmetricBoundarySheaf (b : W) :
    BoundarySheaf (symmetricGrading_negative basis)
      (graph cs 1 b) (symmetricLabel cs 1 b) ⟨b,one_bruhat cs b,bruhat_refl cs b⟩ :=
  (exists_symmetricBoundarySheaf cs basis b).some

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

 theorem symmetricBoundarySheaf_perfectPairing_word (l : List I) (hl : cs.IsReduced l)
    (B : BoundarySheaf (symmetricGrading_negative basis)
      (graph cs 1 (cs.wordProd l)) (symmetricLabel cs 1 (cs.wordProd l))
      ⟨cs.wordProd l,one_bruhat cs _,bruhat_refl cs _⟩) :
    Nonempty (GradedSheaf.PerfectPairing B.sheaf (cs.length (cs.wordProd l) : ℤ)) := by
  obtain ⟨s⟩ := bottBoundarySheaf_splitIn cs basis l hl B
  obtain ⟨j⟩ := bottBoundarySheaf_iso_adjoint cs basis l hl B s
  have hd : cs.length (cs.wordProd l)=l.length := hl
  rw [hd]
  exact ⟨bottRecognizedPerfectPairing cs basis l hl B.sheaf s j⟩

 theorem symmetricBoundarySheaf_perfectPairing (b : W) :
    Nonempty (GradedSheaf.PerfectPairing (symmetricBoundarySheaf cs basis b).sheaf (cs.length b : ℤ)) := by
  obtain ⟨l,hl,he⟩ := cs.exists_isReduced b
  subst b
  exact symmetricBoundarySheaf_perfectPairing_word cs basis l hl _

end
end KLInvariance.TitsSpace
end


section
namespace KLInvariance.TitsSpace
open Module _root_.OAI.KLInvariance.Graded MomentGraph BruhatGraph
universe u
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W)
  {σ : Type u} [Fintype σ] (basis : Basis σ ℝ (Extended M))
noncomputable section

 theorem bottSection_left_orthogonal (l : List I) (hl : cs.IsReduced l)
    (x : Interval cs 1 (cs.wordProd l))
    (m n : (bottProjectionSheaf cs l 1 (cs.wordProd l)).sections Set.univ)
    (hm : ∀ y, y≠x → m.val y=0) (hn : n.val x=0) :
    bottSectionDuality cs l hl m n=0 := by
  obtain ⟨a,rfl⟩ := bottSection_surjective cs l hl m
  obtain ⟨b,rfl⟩ := bottSection_surjective cs l hl n
  rw [bottSectionDuality_apply]
  exact bottStalk_supported_annihilates cs l hl x a b hm hn

 theorem bottSection_right_orthogonal (l : List I) (hl : cs.IsReduced l)
    (x : Interval cs 1 (cs.wordProd l))
    (m n : (bottProjectionSheaf cs l 1 (cs.wordProd l)).sections Set.univ)
    (hm : m.val x=0) (hn : ∀ y, y≠x → n.val y=0) :
    bottSectionDuality cs l hl m n=0 := by
  rw [bottSection_symmetric]
  exact bottSection_left_orthogonal cs l hl x n m hn hm

 def bottWordPerfectPairing (l : List I) (hl : cs.IsReduced l) :
    GradedSheaf.PerfectPairing (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l))
      (l.length : ℤ) where
  pairing := bottSectionDuality cs l hl
  homogeneous := bottSectionDuality_homogeneous cs basis l hl
  left_orthogonal := bottSection_left_orthogonal cs l hl
  right_orthogonal := bottSection_right_orthogonal cs l hl

 def bottPolynomialPerfectPairing (l : List I) (hl : cs.IsReduced l) :
    GradedSheaf.PerfectPairing (bottPolynomialSheaf cs basis l 1 (cs.wordProd l)) (l.length : ℤ) :=
  (bottWordPerfectPairing cs basis l hl).coefficientChange (SymmetricAlgebra.equivMvPolynomial basis)
    (mem_symmetricGrading basis)

 def bottFreeSheaf (l : List I) : FreeSheaf cs 1 (cs.wordProd l) basis where
  sheaf := bottPolynomialSheaf cs basis l 1 (cs.wordProd l)
  free := bottPolynomialSheaf_free cs basis l 1 (cs.wordProd l)
  quotient := bottPolynomialSheaf_quotient cs basis l 1 (cs.wordProd l)
  generated := bottPolynomialSheaf_generated cs basis l 1 (cs.wordProd l)

local instance finiteEdges (l : List I) : Fintype (Edge cs 1 (cs.wordProd l)) := Fintype.ofFinite _
local instance _root_.OAI.KLInvariance.TitsSpace.instDecidableEq_oAI_1 (a : Type*) : DecidableEq a := Classical.decEq a

 def bottFreeDuality (l : List I) (hl : cs.IsReduced l) :
    FreeSheaf.SectionDuality cs 1 (cs.wordProd l) basis (bottFreeSheaf cs basis l) :=
  FreeSheaf.dualityOfPairing cs 1 (cs.wordProd l) basis _ (bottPolynomialPerfectPairing cs basis l hl)

 theorem bottKernelFree (l : List I) (hl : cs.IsReduced l) (x : Interval cs 1 (cs.wordProd l)) :
    Module.Free (Coefficient (σ := σ))
      (GradedSheaf.kernelData (bottPolynomialSheaf cs basis l 1 (cs.wordProd l)) x) :=
  FreeSheaf.kernel_free cs (cs.wordProd l) basis _ (bottFreeDuality cs basis l hl) x

 theorem bottKernelCharacter (l : List I) (hl : cs.IsReduced l)
    [Fintype (Interval cs 1 (cs.wordProd l))] (x : Interval cs 1 (cs.wordProd l)) :
    GradedSheaf.freeKernelChar (bottPolynomialSheaf cs basis l 1 (cs.wordProd l))
      (bottKernelFree cs basis l hl) x=Polynomial.reflect (rankDifference cs x.val (cs.wordProd l))
        (bottStalkCharacter cs basis l x.val) := by
  have he : cs.length (cs.wordProd l)=l.length := hl
  change _=Polynomial.reflect (cs.length (cs.wordProd l)-cs.length x.val) _
  rw [he]
  apply FreeSheaf.kernel_character cs (cs.wordProd l) basis _ (bottFreeDuality cs basis l hl)
    l.length _ he.le x
  intro i j m a hm ha
  exact (bottPolynomialPerfectPairing cs basis l hl).homogeneous i j m a
    (fun x => hm x (Set.mem_univ x)) (fun x => ha x (Set.mem_univ x))

end
end KLInvariance.TitsSpace
end


section
namespace KLInvariance.TitsSpace
open Module _root_.OAI.KLInvariance.Graded MomentGraph BruhatGraph Polynomial
universe u
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W)
  {σ : Type u} [Fintype σ] (basis : Basis σ ℝ (Extended M))
noncomputable section
local instance _root_.OAI.KLInvariance.TitsSpace.instDecidableEq_oAI_2 (a : Type*) : DecidableEq a := Classical.decEq a
local instance rWordEdges (l : List I) : Fintype (Edge cs 1 (cs.wordProd l)) := Fintype.ofFinite _
local instance rWordInterval (l : List I) : Fintype (Interval cs 1 (cs.wordProd l)) := by
  let := interval_finite cs 1 (cs.wordProd l)
  exact Fintype.ofFinite _

 theorem bottStalkCharacter_natDegree_le (l : List I) (hl : cs.IsReduced l)
    (x : Interval cs 1 (cs.wordProd l)) :
    (bottStalkCharacter cs basis l x.val).natDegree≤rankDifference cs x.val (cs.wordProd l) := by
  let B := bottFreeSheaf cs basis l
  let := B.free x
  change (B.sheaf.vertex x).char.natDegree≤rankDifference cs x.val (cs.wordProd l)
  apply ModuleData.char_natDegree_le_of_dual_equiv _ _
    (FreeSheaf.kernelDual cs (cs.wordProd l) basis B (bottFreeDuality cs basis l hl) x)
    (rankDifference cs x.val (cs.wordProd l))
  have hd := (bottPolynomialPerfectPairing cs basis l hl).homogeneous
  have he : cs.length (cs.wordProd l)=l.length := hl
  apply FreeSheaf.kernelDual_homogeneous cs (cs.wordProd l) basis B (bottFreeDuality cs basis l hl)
    (cs.length (cs.wordProd l)) _ x (length_le_of_bruhat cs x.property.2)
  intro i j m a hm ha
  rw [he]
  exact hd i j m a (fun x => hm x (Set.mem_univ x)) (fun x => ha x (Set.mem_univ x))

 theorem bottStalkCharacter_reciprocity (l : List I) (hl : cs.IsReduced l)
    (x : Interval cs 1 (cs.wordProd l)) :
    Polynomial.reflect (rankDifference cs x.val (cs.wordProd l)) (bottStalkCharacter cs basis l x.val)=
      ∑ z ∈ lowerFinset cs (cs.wordProd l),
        OrdinaryR.polynomial cs x.val z*bottStalkCharacter cs basis l z := by
  apply Polynomial.toLaurent_injective
  let q := OrdinaryR.variableUnit
  have h := HeckeQ.positiveWord_rValue cs q l hl x.val
  have hlen : cs.length x.val≤l.length := hl ▸ length_le_of_bruhat cs x.property.2
  have hp : (↑q⁻¹ : LaurentPolynomial ℤ)^cs.length x.val * (q:LaurentPolynomial ℤ)^l.length=
      (q:LaurentPolynomial ℤ)^(rankDifference cs x.val (cs.wordProd l)) := by
    have he : cs.length (cs.wordProd l)=l.length := hl
    rw [rankDifference,he,← Nat.sub_add_cancel hlen,pow_add]
    calc
      _ = ((↑q⁻¹:LaurentPolynomial ℤ)*(q:LaurentPolynomial ℤ))^cs.length x.val *
          (q:LaurentPolynomial ℤ)^(l.length-cs.length x.val) := by rw [mul_pow]; ring
      _ = _ := by rw [q.inv_mul]; simp
  rw [hp] at h
  have hv (p : Polynomial ℤ) : Polynomial.toLaurent p=
      Polynomial.eval₂ (Int.castRingHom (LaurentPolynomial ℤ)) (q:LaurentPolynomial ℤ) p := by
    induction p using Polynomial.induction_on' with
    | add p r hp hr => simp only [map_add,Polynomial.eval₂_add,hp,hr]
    | monomial n a => simp [q,Polynomial.toLaurent_C_mul_T]
  rw [hv,eval₂_reflect_unit q _ _ (bottStalkCharacter_natDegree_le cs basis l hl x)]
  rw [hv]
  simp only [Polynomial.eval₂_finsetSum,Polynomial.eval₂_mul,OrdinaryR.polynomial_eval,
    bottStalkCharacter_eq_heckeWord,HeckeQ.eval_positiveWord]
  exact h.symm

 theorem bottKernelCharacter_rConvolution (l : List I) (hl : cs.IsReduced l)
    (x : Interval cs 1 (cs.wordProd l)) :
    GradedSheaf.freeKernelChar (bottPolynomialSheaf cs basis l 1 (cs.wordProd l))
      (bottKernelFree cs basis l hl) x=
      ∑ z : Interval cs 1 (cs.wordProd l),
        OrdinaryR.polynomial cs x.val z.val*bottStalkCharacter cs basis l z.val := by
  rw [bottKernelCharacter cs basis l hl x,bottStalkCharacter_reciprocity cs basis l hl x]
  exact Finset.sum_subtype (F := (inferInstance : Fintype (Interval cs 1 (cs.wordProd l))))
    (lowerFinset cs (cs.wordProd l))
    (fun z => by simp only [mem_lowerFinset]; exact ⟨fun h => ⟨one_bruhat cs z,h⟩,And.right⟩)
    (fun z => OrdinaryR.polynomial cs x.val z*bottStalkCharacter cs basis l z)

end
end KLInvariance.TitsSpace
end

end OAI

open Lean
namespace BoundaryCodec
partial def nameJson : Name → Json
  | .anonymous => Json.arr #[]
  | .str p s => toJson (#[nameJson p, toJson s])
  | .num p n => toJson (#[nameJson p, toJson n, Json.null])
partial def levelJson : Level → Json
  | .zero => toJson (#[toJson "zero"])
  | .succ u => toJson (#[toJson "succ", levelJson u])
  | .max u v => toJson (#[toJson "max", levelJson u, levelJson v])
  | .imax u v => toJson (#[toJson "imax", levelJson u, levelJson v])
  | .param n => toJson (#[toJson "param", nameJson n])
  | .mvar _ => panic! "unclosed level"
structure Dump where
  ids : ExprStructMap Nat := {}
  nodes : Array Json := #[]
partial def encode (e : Expr) : StateM Dump Nat := do
  if let .mdata _ b := e then return ← encode b
  if let some i := (← get).ids[ExprStructEq.mk e]? then return i
  let node : Array Json ← match e with
    | .bvar n => pure #[toJson "bvar", toJson n]
    | .sort u => pure #[toJson "sort", levelJson u]
    | .const n us => pure #[toJson "const", nameJson n, toJson (us.map levelJson)]
    | .app f a => do pure #[toJson "app", toJson (← encode f), toJson (← encode a)]
    | .lam n t b bi | .forallE n t b bi => do
      let tag := if e.isLambda then "lam" else "forall"
      let bi := match bi with | .default => 0 | .implicit => 1 | .strictImplicit => 2 | .instImplicit => 3
      pure #[toJson tag, nameJson n, toJson (← encode t), toJson (← encode b), toJson bi]
    | .letE n t v b nondep => do pure #[toJson "let", nameJson n, toJson (← encode t), toJson (← encode v), toJson (← encode b), toJson nondep]
    | .lit (.natVal n) => pure #[toJson "nat", toJson n]
    | .lit (.strVal s) => pure #[toJson "str", toJson s]
    | .proj n i b => do pure #[toJson "proj", nameJson n, toJson i, toJson (← encode b)]
    | _ => panic! "unclosed expression"
  let s ← get
  set ({ids := s.ids.insert (ExprStructEq.mk e) s.nodes.size, nodes := s.nodes.push (toJson node)} : Dump)
  return s.nodes.size
partial def readName (j : Json) : Except String Name := do
  let a ← j.getArr?
  if a.isEmpty then return .anonymous
  if a.size == 2 then return .str (← readName a[0]!) (← a[1]!.getStr?)
  if a.size == 3 then return .num (← readName a[0]!) (← fromJson? a[1]!)
  throw "bad name"
partial def readLevel (j : Json) : Except String Level := do
  let a ← j.getArr?
  match ← a[0]!.getStr? with
  | "zero" => do pure (.zero)
  | "succ" => do pure (.succ (← readLevel a[1]!))
  | "max" => do pure (.max (← readLevel a[1]!) (← readLevel a[2]!))
  | "imax" => do pure (.imax (← readLevel a[1]!) (← readLevel a[2]!))
  | "param" => do pure (.param (← readName a[1]!))
  | _ => throw "bad level"
def decode (nodes : Array Json) : Except String (Array Expr) := do
  let mut es := #[]
  for j in nodes do
    let a ← j.getArr?
    let child := fun (i : Nat) => (show Except String Expr from do
      let n : Nat ← fromJson? a[i]!
      if n < es.size then return es[n]! else throw "non-topological DAG")
    let e : Expr ← match ← a[0]!.getStr? with
      | "bvar" => do pure (.bvar (← fromJson? a[1]!))
      | "sort" => do pure (.sort (← readLevel a[1]!))
      | "const" => do pure (.const (← readName a[1]!) (← (← a[2]!.getArr?).toList.mapM readLevel))
      | "app" => do pure (.app (← child 1) (← child 2))
      | "lam" | "forall" => do
        let bi : Nat ← fromJson? a[4]!
        let bi ← match bi with | 0 => pure BinderInfo.default | 1 => pure .implicit | 2 => pure .strictImplicit | 3 => pure .instImplicit | _ => throw "bad binder"
        if (← a[0]!.getStr?) == "lam" then pure (.lam (← readName a[1]!) (← child 2) (← child 3) bi)
        else pure (.forallE (← readName a[1]!) (← child 2) (← child 3) bi)
      | "let" => do pure (.letE (← readName a[1]!) (← child 2) (← child 3) (← child 4) (← fromJson? a[5]!))
      | "nat" => do pure (.lit (.natVal (← fromJson? a[1]!)))
      | "str" => do pure (.lit (.strVal (← fromJson? a[1]!)))
      | "proj" => do pure (.proj (← readName a[1]!) (← fromJson? a[2]!) (← child 3))
      | _ => throw "bad expression"
    es := es.push e
  return es
end BoundaryCodec

open Lean Meta Elab Command BoundaryCodec
run_elab do
  let names : Array Name := #[`OAI.KLInvariance.TitsSpace.bottSplitLeftWord_coordinates]
  let env := (← Lean.getEnv).setExporting false
  let mut dump : BoundaryCodec.Dump := {}
  let mut records : Array Json := #[]
  let mut aux : Array Json := #[]
  let mut pending : Array Name := names
  let mut seen : Array Name := #[]
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    if seen.contains n then continue
    seen := seen.push n
    let some ci := env.find? n | throwError "old name missing {n}"
    let (ti, ds) := (BoundaryCodec.encode ci.type).run dump
    dump := ds
    if names.contains n then
      records := records.push (Json.arr #[BoundaryCodec.nameJson n, toJson (ci.levelParams.map BoundaryCodec.nameJson), toJson ti, toJson (Lean.defeqAttr.hasTag env n), toJson (Lean.backwardDefeqAttr.hasTag env n)])
    let visit := fun (e : Expr) => e.foldConsts #[] fun n ns =>
      if n.toString.contains "_proof_" || n.toString.contains "match_" then ns.push n else ns
    pending := pending ++ visit ci.type
    if n.toString.contains "_proof_" || n.toString.contains "match_" then
      let some v := ci.value? (allowOpaque := true) | continue
      pending := pending ++ visit v
      let (vi, ds) := (BoundaryCodec.encode v).run dump
      dump := ds
      aux := aux.push (Json.arr #[BoundaryCodec.nameJson n, toJson (ci.levelParams.map BoundaryCodec.nameJson), toJson ti, toJson vi, toJson (match ci with | .thmInfo _ => "theorem" | _ => "def")])
  IO.FS.writeFile "/workspace/lean-lab/results/matcher-compat/OAI.KL.BottSamelson.Character.ordinary-old.json" ((Json.mkObj [("nodes",toJson dump.nodes),("records",toJson records),("aux",toJson aux)]).compress)
  IO.println s!"Captured {records.size} actual old types and {aux.size} helper declarations."

open Lean

structure TypeDumpState where
  ids : ExprStructMap Nat := {}
  proofIds : ExprStructMap Nat := {}
  next : Nat := 0
  privateOwners : Std.HashMap Name Name := {}
  proofAliases : NameHashSet := {}
  unrenamed : NameHashSet := {}

-- Alpha equivalence ignores binder display names. Only compiler-private OAI
-- owner prefixes are erased from constant names; their user names stay exact.
-- There are no duplicate private user names in the pinned source.
private def canonicalConstant (n : Name) : Name :=
  if n.toString.startsWith "_private.OAI." then
    (privateToUserName? n).getD n
  else n

-- Keep every mathematical expression constructor, universe, binder info,
-- constant, application and de Bruijn index. Metadata and binder display names
-- have no effect on the mathematical type. A local compiler theorem auxiliary
-- is represented by its full proposition, using kernel proof irrelevance.
-- No proof body, general definition, data instance or user theorem is unfolded.
partial def dumpType (env : Environment) (out : IO.FS.Handle) (e : Expr)
    (proofContext := false) : StateT TypeDumpState IO Nat := do
  let cached : TypeDumpState ← get
  let cache := if proofContext then cached.proofIds else cached.ids
  if let some id := cache[ExprStructEq.mk e]? then return id
  if let .mdata _ body := e then return ← dumpType env out body proofContext
  let fields ← match e with
    | .bvar i => pure ["bvar", toString i]
    | .sort u => pure ["sort", reprStr u]
    | .const n us =>
      let proofName := match n with
        | .str _ s => s.startsWith "_proof_"
        | _ => false
      if n.isInternal && n.toString.startsWith "OAI." && proofName then
        if let some (.thmInfo info) := env.find? n then
          -- Kernel theorem declarations prove propositions. Their full
          -- proposition, including parameters, is retained; only its binder
          -- display/implicitness metadata is irrelevant to the proof value.
          let proposition ← dumpType env out (info.type.instantiateLevelParams info.levelParams us) true
          modify fun st => { st with proofAliases := st.proofAliases.insert n }
          pure ["proof", toString proposition]
        else pure ["const", reprStr n, reprStr us]
      else
        let canonical := canonicalConstant n
        if canonical != n then
          if env.contains canonical then
            throw <| IO.userError "Private canonical name collides with an unrenamed global constant"
          if let some previous := (← get).privateOwners[canonical]? then
            if previous != n then throw <| IO.userError "Ambiguous private type constant"
          modify fun st => { st with privateOwners := st.privateOwners.insert canonical n }
        pure ["const", reprStr canonical, reprStr us]
    | .app f a => do
      let f ← dumpType env out f proofContext; let a ← dumpType env out a proofContext
      pure ["app", toString f, toString a]
    | .lam _ t b bi | .forallE _ t b bi => do
      let t ← dumpType env out t proofContext; let b ← dumpType env out b proofContext
      pure [if e.isLambda then "lam" else "forall", "_", if proofContext then "kernel" else reprStr bi, toString t, toString b]
    | .letE _ t v b nondep => do
      let t ← dumpType env out t proofContext; let v ← dumpType env out v proofContext; let b ← dumpType env out b proofContext
      pure ["let", "_", toString t, toString v, toString b, toString nondep]
    | .lit v => pure ["lit", reprStr v]
    | .proj n i b => do
      let b ← dumpType env out b proofContext
      pure ["proj", reprStr n, toString i, toString b]
    | .fvar _ | .mvar _ => throw <| IO.userError "Non-closed declaration type"
    | .mdata _ _ => unreachable!
  match e with
  | .const n _ =>
    if fields.head! == "const" && canonicalConstant n == n then
      modify fun st => { st with unrenamed := st.unrenamed.insert n }
  | .proj n _ _ => modify fun st => { st with unrenamed := st.unrenamed.insert n }
  | _ => pure ()
  let state : TypeDumpState ← get
  if proofContext then
    set { state with proofIds := state.proofIds.insert (ExprStructEq.mk e) state.next, next := state.next+1 }
  else
    set { state with ids := state.ids.insert (ExprStructEq.mk e) state.next, next := state.next+1 }
  out.putStrLn s!"NODE\t{state.next}\t{(toJson fields).compress}"
  return state.next

private def declarationKind : ConstantInfo → String
  | .axiomInfo _ => "axiom" | .defnInfo _ => "def"
  | .thmInfo _ => "theorem" | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient" | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor" | .recInfo _ => "recursor"

-- This experiment accepts duplicate serialized theorem records only.
-- Other ConstantInfo variants fail closed; their safety/hints are not omitted
-- from a purported full-record comparison. ExprStructEq retains binder names
-- and annotations, unlike BEq Expr (Expr.eqv).
private def sameSerializedTheorem (a b : ConstantInfo) : Bool :=
  match a, b with
  | .thmInfo a, .thmInfo b =>
    a.name == b.name && a.levelParams == b.levelParams &&
      ExprStructEq.mk a.type == ExprStructEq.mk b.type &&
      ExprStructEq.mk a.value == ExprStructEq.mk b.value && a.all == b.all
  | _, _ => false


run_elab do
  let env := (← Lean.getEnv).setExporting false
  let out ← IO.FS.Handle.mk "/workspace/lean-lab/results/matcher-compat/OAI.KL.BottSamelson.Character.ordinary-old.tsv" .write
  let action : StateT TypeDumpState IO Unit := do
    out.putStrLn "FORMAT\tkl-public-types-v3"
    for n in #[`OAI.KLInvariance.TitsSpace.bottSplitLeftWord_coordinates] do
      let some ci := env.find? n | throw <| IO.userError "missing selected old name"
      out.putStrLn "MODULE\tOAI.KL.BottSamelson.Character"
      let id ← dumpType env out ci.type
      out.putStrLn s!"TYPE\t{n}\t{(toJson (reprStr ci.levelParams)).compress}\t{id}\t{declarationKind ci}"
    let st ← get
    for n in st.proofAliases.toArray do out.putStrLn s!"PROOF_ALIAS\t{n}"
    out.putStrLn s!"PRIVATE_SUMMARY\t{st.privateOwners.size}\t{st.unrenamed.size}\t0\t0"
    out.putStrLn s!"SUMMARY\t1\t0\t{st.proofAliases.size}"
  discard <| action.run {}
  out.flush
