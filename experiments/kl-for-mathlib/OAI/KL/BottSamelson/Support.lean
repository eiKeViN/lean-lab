module
public import Mathlib
public import ForMathlib.Algebra.Module.Graded.ModuleData.Duality
public import ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Duality
public import ForMathlib.LinearAlgebra.Dual.BalancedCut
public import OAI.KL.BottSamelson.AdjointSheaf
public import OAI.KL.Sheaves.LowerCharacter
public import OAI.KL.BottSamelson.Flabby

public section

/-! Semantic home: OAI.KL.BottSamelson.Support. Source spans: Support:3, Support:12, Support:11, Support:2, Support:6, Support:8.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.TitsSpace
open Module _root_.OAI.KLInvariance.Graded
universe u us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {σ : Type us} (basis : Basis σ ℝ (Extended M))
noncomputable section

 theorem symmetricGrading_zero (a : SymmetricCoefficient (M := M))
    (ha : a ∈ symmetricGrading basis 0) :
    ∃ c : ℝ, algebraMap ℝ (SymmetricCoefficient (M := M)) c=a := by
  obtain ⟨c,hc⟩ := polynomialGrading_zero ℝ σ
    (SymmetricAlgebra.equivMvPolynomial basis a) ((mem_symmetricGrading basis 0 a).mp ha)
  refine ⟨c,?_⟩
  apply (SymmetricAlgebra.equivMvPolynomial basis).injective
  exact ((SymmetricAlgebra.equivMvPolynomial basis).commutes c).trans hc

end
end KLInvariance.TitsSpace
end


section
namespace KLInvariance.TitsSpace
open Module MomentGraph BruhatGraph
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

 theorem bottSupported_of_stalkSupport (l : List I) (hl : cs.IsReduced l)
    (x : Interval cs 1 (cs.wordProd l)) (m : BottSamelsonModule cs l)
    (hm : ∀ y : Interval cs 1 (cs.wordProd l), y≠x → bottStalkProjection cs l y.val m=0) :
    m∈bottWeightSupported cs l x.val := by
  intro e he
  let y : Interval cs 1 (cs.wordProd l) :=
    ⟨bottWeight cs l e,one_bruhat cs _,bottWeight_bruhat cs l hl e⟩
  have hy : y≠x := fun h => he (congrArg Subtype.val h)
  exact congrFun (congrArg Subtype.val (hm y hy)) ⟨e,rfl⟩

 theorem bottStalk_supported_annihilates (l : List I) (hl : cs.IsReduced l)
    (x : Interval cs 1 (cs.wordProd l)) (m n : BottSamelsonModule cs l)
    (hm : ∀ y : Interval cs 1 (cs.wordProd l), y≠x → bottStalkProjection cs l y.val m=0)
    (hn : bottStalkProjection cs l x.val n=0) : bottSamelsonDuality cs l m n=0 :=
  bott_supported_annihilates cs l x.val (bottSupported_of_stalkSupport cs l hl x m hm) n
    (congrArg Subtype.val hn)

end
end KLInvariance.TitsSpace
end


section
namespace KLInvariance.TitsSpace
open Module MomentGraph BruhatGraph
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section
local instance _root_.OAI.KLInvariance.TitsSpace.instDecidableEq_oAI (a : Type*) : DecidableEq a := Classical.decEq a

 theorem bottSection_supported_annihilates (l : List I) (hl : cs.IsReduced l)
    (x : Interval cs 1 (cs.wordProd l))
    (s z : (bottProjectionSheaf cs l 1 (cs.wordProd l)).sections Set.univ)
    (hs : s ∈ IntegralSupport.supported
      ((bottProjectionSheaf cs l 1 (cs.wordProd l)).sections Set.univ) x)
    (hz : z.val x=0) : bottSectionDuality cs l hl s z=0 := by
  classical
  obtain ⟨m,rfl⟩ := bottSection_surjective cs l hl s
  obtain ⟨n,rfl⟩ := bottSection_surjective cs l hl z
  rw [bottSectionDuality_apply]
  apply bott_supported_annihilates cs l x.val
  · intro e he
    let y : Interval cs 1 (cs.wordProd l) :=
      ⟨bottWeight cs l e,one_bruhat cs _,bottWeight_bruhat cs l hl e⟩
    have hy : y ≠ x := fun h => he (congrArg Subtype.val h)
    have hh := hs y hy
    exact congrFun (congrArg Subtype.val hh) ⟨e,rfl⟩
  · exact congrArg Subtype.val hz

 theorem bottSection_projector_balanced (l : List I) (hl : cs.IsReduced l)
    (p : SymmetricCoefficient (M := M)) (hp : p ≠ 0)
    (x : Interval cs 1 (cs.wordProd l))
    (c : End (SymmetricCoefficient (M := M))
      ((bottProjectionSheaf cs l 1 (cs.wordProd l)).sections Set.univ))
    (hself : ∀ m, (c m).val x=p • m.val x)
    (hother : ∀ m y, y ≠ x → (c m).val y=0)
    (s z : (bottProjectionSheaf cs l 1 (cs.wordProd l)).sections Set.univ) :
    bottSectionDuality cs l hl (c s) z = bottSectionDuality cs l hl s (c z) := by
  classical
  apply BalancedCuts.balanced (bottSectionDuality cs l hl).toLinearMap
    (bottSection_symmetric cs l hl)
    (IntegralSupport.projection (A := fun y : Interval cs 1 (cs.wordProd l) => bottStalk cs l y.val)
      ((bottProjectionSheaf cs l 1 (cs.wordProd l)).sections Set.univ) x)
    c p hp hself
  intro m n hn
  exact bottSection_supported_annihilates cs l hl x (c m) n (hother m) hn

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
  (α : Edge cs 1 (cs.wordProd l) → SymmetricCoefficient (M := M))
  (B : BoundarySheaf (symmetricGrading_negative basis)
    (graph cs 1 (cs.wordProd l)) α
    ⟨cs.wordProd l,one_bruhat cs _,bruhat_refl cs _⟩)
  (s : GradedSheaf.SplitIn B.sheaf (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l)))
noncomputable section

include hl in
 theorem bottBoundarySplit_top_fixed (v : bottStalk cs l (cs.wordProd l)) :
    (s.projector.vertex ⟨cs.wordProd l,one_bruhat cs _,bruhat_refl cs _⟩).map v=v := by
  exact ModuleData.split_reverse_of_unit (symmetricGrading_negative basis) B.top
    (bottTopHom cs basis l hl) (bottTopInvHom cs basis l hl)
    (bottTopInvHom_top cs basis l hl)
    (s.inclusion.vertex ⟨cs.wordProd l,one_bruhat cs _,bruhat_refl cs _⟩)
    (s.projection.vertex ⟨cs.wordProd l,one_bruhat cs _,bruhat_refl cs _⟩)
    (s.vertex_split ⟨cs.wordProd l,one_bruhat cs _,bruhat_refl cs _⟩) v

 theorem bottBoundarySplitAdjoint_top_fixed (v : bottStalk cs l (cs.wordProd l)) :
    ((bottAdjointSheaf cs basis l hl s.projector).vertex
      ⟨cs.wordProd l,one_bruhat cs _,bruhat_refl cs _⟩).map v=v :=
  bottAdjointSheaf_fixed_stalk cs basis l hl s.projector
    ⟨cs.wordProd l,one_bruhat cs _,bruhat_refl cs _⟩
    (bottBoundarySplit_top_fixed cs basis l hl α B s) v

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

 @[expose] def symmetricLabel (u b : W) (e : Edge cs u b) : SymmetricCoefficient (M := M) :=
  SymmetricAlgebra.ι ℝ (Extended M) (embed M (BruhatGraph.root cs u b e).val)

 theorem symmetricLabel_represents (u b : W) (e : Edge cs u b) :
    Represents M cs (label cs u b e) (BruhatGraph.root cs u b e).val :=
  positiveRoot_represents M cs ⟨label cs u b e,label_isReflection cs u b e⟩

 theorem bottGradedProjectionSheaf_upperQuotient (l : List I) (u b : W) :
    (bottGradedProjectionSheaf cs basis l u b).UpperQuotient (symmetricLabel cs u b) := by
  intro e
  exact ⟨bottProjectionSheaf_upper_surjective cs l u b e,
    bottProjectionSheaf_upper_kernel cs l u b e (symmetricLabel_represents cs u b e)⟩

 @[expose] def bottBoundarySheafTopInclusion (l : List I) (hl : cs.IsReduced l)
    (B : BoundarySheaf (symmetricGrading_negative basis)
      (graph cs 1 (cs.wordProd l)) (symmetricLabel cs 1 (cs.wordProd l))
      ⟨cs.wordProd l,one_bruhat cs _,bruhat_refl cs _⟩) :
    ModuleData.Hom (B.sheaf.vertex ⟨cs.wordProd l,one_bruhat cs _,bruhat_refl cs _⟩)
      (bottStalkData cs basis l (cs.wordProd l)) :=
  (bottTopInvHom cs basis l hl).comp
    ⟨(ModuleData.equivOfEq B.top).toLinearMap,ModuleData.equivOfEq_graded B.top⟩

 @[expose] def bottBoundarySheafTopProjection (l : List I) (hl : cs.IsReduced l)
    (B : BoundarySheaf (symmetricGrading_negative basis)
      (graph cs 1 (cs.wordProd l)) (symmetricLabel cs 1 (cs.wordProd l))
      ⟨cs.wordProd l,one_bruhat cs _,bruhat_refl cs _⟩) :
    ModuleData.Hom (bottStalkData cs basis l (cs.wordProd l))
      (B.sheaf.vertex ⟨cs.wordProd l,one_bruhat cs _,bruhat_refl cs _⟩) :=
  (⟨(ModuleData.equivOfEq B.top.symm).toLinearMap,ModuleData.equivOfEq_graded B.top.symm⟩ :
    ModuleData.Hom _ _).comp (bottTopHom cs basis l hl)

 theorem bottBoundarySheafTop_split (l : List I) (hl : cs.IsReduced l)
    (B : BoundarySheaf (symmetricGrading_negative basis)
      (graph cs 1 (cs.wordProd l)) (symmetricLabel cs 1 (cs.wordProd l))
      ⟨cs.wordProd l,one_bruhat cs _,bruhat_refl cs _⟩)
    (v : B.sheaf.vertex ⟨cs.wordProd l,one_bruhat cs _,bruhat_refl cs _⟩) :
    (bottBoundarySheafTopProjection cs basis l hl B).map
      ((bottBoundarySheafTopInclusion cs basis l hl B).map v)=v := by
  change ModuleData.equivOfEq B.top.symm ((bottTopHom cs basis l hl).map
    ((bottTopInvHom cs basis l hl).map (ModuleData.equivOfEq B.top v)))=v
  rw [bottTopHom_inv]
  exact ModuleData.equivOfEq_inverse B.top v

 theorem bottBoundarySheaf_splitIn (l : List I) (hl : cs.IsReduced l)
    (B : BoundarySheaf (symmetricGrading_negative basis)
      (graph cs 1 (cs.wordProd l)) (symmetricLabel cs 1 (cs.wordProd l))
      ⟨cs.wordProd l,one_bruhat cs _,bruhat_refl cs _⟩) :
    Nonempty (GradedSheaf.SplitIn B.sheaf (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l))) := by
  classical
  let := symmetricCoefficientNoetherian basis
  let := interval_finite cs 1 (cs.wordProd l)
  let := Fintype.ofFinite (Interval cs 1 (cs.wordProd l))
  let := Fintype.ofFinite (Edge cs 1 (cs.wordProd l))
  exact B.splitIn_of_top_split (symmetricGrading_zero basis) (fun x => x.property.2)
    (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l))
    (bottGradedProjectionSheaf_upperQuotient cs basis l 1 (cs.wordProd l))
    (fun x => bottStalkFree cs l x.val) (bottProjectionSheaf_flabby cs l hl)
    (bottProjectionSheaf_generated cs l 1 (cs.wordProd l))
    (bottBoundarySheafTopInclusion cs basis l hl B) (bottBoundarySheafTopProjection cs basis l hl B)
    (bottBoundarySheafTop_split cs basis l hl B)

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

 @[expose] def bottPolynomialSheaf (l : List I) (u b : W) :
    GradedSheaf (𝓐 := polynomialGrading ℝ σ) (graph cs u b) :=
  GradedSheaf.coefficientChange (SymmetricAlgebra.equivMvPolynomial basis)
    (mem_symmetricGrading basis) (bottGradedProjectionSheaf cs basis l u b)

 theorem bottPolynomialSheaf_free (l : List I) (u b : W) :
    (bottPolynomialSheaf cs basis l u b).FreeStalks :=
  GradedSheaf.coefficientChange_free _ _ _ (fun x => bottStalkFree cs l x.val)

 theorem bottPolynomialSheaf_quotient (l : List I) (u b : W) :
    (bottPolynomialSheaf cs basis l u b).UpperQuotient (polynomialLabel cs u b basis) :=
  GradedSheaf.coefficientChange_upperQuotient _ _ _ _
    (bottGradedProjectionSheaf_upperQuotient cs basis l u b)

 theorem bottPolynomialSheaf_flabby (l : List I) (hl : cs.IsReduced l) :
    (bottPolynomialSheaf cs basis l 1 (cs.wordProd l)).forget.Flabby :=
  GradedSheaf.coefficientChange_flabby _ _ _ (bottProjectionSheaf_flabby cs l hl)

 theorem bottPolynomialSheaf_generated (l : List I) (u b : W) :
    (bottPolynomialSheaf cs basis l u b).forget.Generated :=
  GradedSheaf.coefficientChange_generated _ _ _ (bottProjectionSheaf_generated cs l u b)

 theorem bottPolynomialSheaf_character (l : List I) (u b : W) (x : Interval cs u b) :
    GradedSheaf.freeStalkChar (bottPolynomialSheaf cs basis l u b)
      (bottPolynomialSheaf_free cs basis l u b) x=bottStalkCharacter cs basis l x.val := rfl

 theorem bottStalkCharacter_decomposition (l : List I) (hl : cs.IsReduced l)
    [Fintype (Interval cs 1 (cs.wordProd l))] :
    ∃ m : Interval cs 1 (cs.wordProd l) → Polynomial ℤ,
      (∀ y n, 0≤(m y).coeff n) ∧ ∀ x,
      bottStalkCharacter cs basis l x.val=
        ∑ y, m y*lowerCharacter cs (cs.wordProd l) basis y x := by
  classical
  let := Fintype.ofFinite (Edge cs 1 (cs.wordProd l))
  obtain ⟨m,hm,he⟩ := GradedSheaf.exists_stalkCharacter_decomposition
    (boundaryModels cs (cs.wordProd l) basis)
    (bottPolynomialSheaf cs basis l 1 (cs.wordProd l))
    (bottPolynomialSheaf_free cs basis l 1 (cs.wordProd l))
    (bottPolynomialSheaf_quotient cs basis l 1 (cs.wordProd l))
    (bottPolynomialSheaf_flabby cs basis l hl)
    (bottPolynomialSheaf_generated cs basis l 1 (cs.wordProd l))
  refine ⟨m,hm,fun x => ?_⟩
  simpa only [bottPolynomialSheaf_character,boundaryModels_character] using he x

end
end KLInvariance.TitsSpace
end

end OAI
