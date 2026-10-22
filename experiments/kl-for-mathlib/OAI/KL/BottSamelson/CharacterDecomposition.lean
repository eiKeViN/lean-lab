module
public import Mathlib
public import OAI.KL.Sheaves.Reciprocity

public section

/-! Semantic home: OAI.KL.BottSamelson.CharacterDecomposition. Source spans: CharacterReciprocity:34.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.TitsSpace
open Module _root_.OAI.KLInvariance.Graded MomentGraph BruhatGraph Polynomial
universe u
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W)
  {σ : Type u} [Fintype σ] (basis : Basis σ ℝ (Extended M))
noncomputable section

 theorem bottCharacter_decomposition_both (l : List I) (hl : cs.IsReduced l)
    [Fintype (Interval cs 1 (cs.wordProd l))] :
    ∃ m : Interval cs 1 (cs.wordProd l) → Polynomial ℤ,
      (∀ y n, 0≤(m y).coeff n) ∧
      (∀ x, bottStalkCharacter cs basis l x.val=
        ∑ y, m y*lowerCharacter cs (cs.wordProd l) basis y x) ∧
      (∀ x, GradedSheaf.freeKernelChar (bottPolynomialSheaf cs basis l 1 (cs.wordProd l))
        (bottKernelFree cs basis l hl) x=
        ∑ y, m y*Polynomial.reflect (rankDifference cs x.val y.val)
          (lowerCharacter cs (cs.wordProd l) basis y x)) := by
  classical
  let := Fintype.ofFinite (Edge cs 1 (cs.wordProd l))
  obtain ⟨m,hm,he,hk⟩ := GradedSheaf.exists_character_decomposition
    (boundaryModels cs (cs.wordProd l) basis) (boundaryModels_kernelFree cs (cs.wordProd l) basis)
    (bottPolynomialSheaf cs basis l 1 (cs.wordProd l))
    (bottPolynomialSheaf_free cs basis l 1 (cs.wordProd l)) (bottKernelFree cs basis l hl)
    (bottPolynomialSheaf_quotient cs basis l 1 (cs.wordProd l))
    (bottPolynomialSheaf_flabby cs basis l hl) (bottPolynomialSheaf_generated cs basis l 1 (cs.wordProd l))
  refine ⟨m,hm,fun x => ?_,fun x => ?_⟩
  · simpa only [bottPolynomialSheaf_character,boundaryModels_character] using he x
  · simpa only [boundaryModels_kernelCharacter] using hk x

end
end KLInvariance.TitsSpace
end

end OAI
