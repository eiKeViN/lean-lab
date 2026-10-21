import Mathlib
import ForMathlib.Algebra.Module.Graded.Hilbert.Numerator
import ForMathlib.RepresentationTheory.Hecke.Coefficients
import OAI.KL.BottSamelson.Stalks

/-! Semantic home: OAI.KL.BottSamelson.StalkCharacter. Source spans: IntegralPairings:2, IntegralPairings:4.
See migration.json and MIGRATION.md for exact provenance.
Bott stalk-character rank recurrences, top and zero normalization and equality with the Hecke word coefficients, independently of upper-set section projectivity. -/

namespace OAI

section
namespace KLInvariance.TitsSpace
open Module _root_.OAI.KLInvariance.Graded
universe u
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W)
  {σ : Type u} [Fintype σ] (basis : Basis σ ℝ (Extended M))
noncomputable section

 theorem bottStalk_finrank_descent (i : I) (l : List I) (x : W)
    (h : cs.length (cs.simple i*x)<cs.length x) (n : ℤ) :
    Module.finrank ℝ (bottStalkPiece cs basis (i::l) x n)=
      Module.finrank ℝ (bottStalkPiece cs basis l (cs.simple i*x) n)+
      Module.finrank ℝ (bottStalkPiece cs basis l x (n-1)) := by
  have hdim := Hilbert.finrank_exact (A := ℝ) (bottStalkPiece cs basis (i::l) x)
    (bottStalkPiece cs basis l (cs.simple i*x)) (bottHeadRight cs i l x)
    (bottHeadRight_homogeneous cs basis i l x) (bottHeadRight_surjective cs i l x) n
  have hk := finrank_homogeneousEquiv (k := ℝ)
    (N := LinearMap.ker (bottHeadRight cs i l x)) (bottStalkPiece cs basis l x)
    (bottHeadRightKernelPiece cs basis i l x) (bottHeadRightKernelEquiv cs i l x h) 1
    (bottHeadRightKernelEquiv_homogeneous cs basis i l x h) n
  change Module.finrank ℝ (bottStalkPiece cs basis (i::l) x n)=
    Module.finrank ℝ (bottHeadRightKernelPiece cs basis i l x n)+
      Module.finrank ℝ (bottStalkPiece cs basis l (cs.simple i*x) n) at hdim
  rw [hk] at hdim
  omega

 theorem bottStalkCharacter_ascent (i : I) (l : List I) (x : W)
    (h : cs.length x<cs.length (cs.simple i*x)) :
    bottStalkCharacter cs basis (i::l) x=bottStalkCharacter cs basis l x+
      Polynomial.X*bottStalkCharacter cs basis l (cs.simple i*x) := by
  apply Hilbert.numerator_add_shift
    (fun n => Module.finrank ℝ (bottStalkPiece cs basis (i::l) x n))
    (fun n => Module.finrank ℝ (bottStalkPiece cs basis l x n))
    (fun n => Module.finrank ℝ (bottStalkPiece cs basis l (cs.simple i*x) n))
    _ _ _ (fun q => (1-q)⁻¹ ^ Fintype.card σ)
  · intro q _ hq
    exact pow_ne_zero _ (inv_ne_zero (sub_ne_zero.mpr (ne_of_gt hq)))
  · exact fun _ => bottStalkCharacter_hasSum cs basis (i::l) x
  · exact fun _ => bottStalkCharacter_hasSum cs basis l x
  · exact fun _ => bottStalkCharacter_hasSum cs basis l (cs.simple i*x)
  · exact bottStalk_finrank_ascent cs basis i l x h

 theorem bottStalkCharacter_descent (i : I) (l : List I) (x : W)
    (h : cs.length (cs.simple i*x)<cs.length x) :
    bottStalkCharacter cs basis (i::l) x=bottStalkCharacter cs basis l (cs.simple i*x)+
      Polynomial.X*bottStalkCharacter cs basis l x := by
  apply Hilbert.numerator_add_shift
    (fun n => Module.finrank ℝ (bottStalkPiece cs basis (i::l) x n))
    (fun n => Module.finrank ℝ (bottStalkPiece cs basis l (cs.simple i*x) n))
    (fun n => Module.finrank ℝ (bottStalkPiece cs basis l x n))
    _ _ _ (fun q => (1-q)⁻¹ ^ Fintype.card σ)
  · intro q _ hq
    exact pow_ne_zero _ (inv_ne_zero (sub_ne_zero.mpr (ne_of_gt hq)))
  · exact fun _ => bottStalkCharacter_hasSum cs basis (i::l) x
  · exact fun _ => bottStalkCharacter_hasSum cs basis l (cs.simple i*x)
  · exact fun _ => bottStalkCharacter_hasSum cs basis l x
  · exact bottStalk_finrank_descent cs basis i l x h

end
end KLInvariance.TitsSpace
end


section
namespace KLInvariance.TitsSpace
open Module _root_.OAI.KLInvariance.Graded
universe u
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W)
  {σ : Type u} [Fintype σ] (basis : Basis σ ℝ (Extended M))
noncomputable section
local instance _root_.OAI.KLInvariance.TitsSpace.instDecidable_oAI_7 (p : Prop) : Decidable p := Classical.propDecidable p

 theorem bottStalkCharacter_zero (l : List I) (x : W)
    [Subsingleton (bottStalk cs l x)] : bottStalkCharacter cs basis l x=0 := by
  apply Hilbert.numerator_unique
    (fun n => Module.finrank ℝ (bottStalkPiece cs basis l x n)) _ _
    (fun q => (1-q)⁻¹ ^ Fintype.card σ)
  · intro q _ hq
    exact pow_ne_zero _ (inv_ne_zero (sub_ne_zero.mpr (ne_of_gt hq)))
  · exact fun _ => bottStalkCharacter_hasSum cs basis l x
  · intro q _ _
    simpa only [Module.finrank_zero_of_subsingleton,Nat.cast_zero,zero_mul,Polynomial.eval₂_zero] using (hasSum_zero : HasSum (fun _ : ℤ => (0 : ℝ)) 0)

 def bottTopPolynomialEquiv (l : List I) (hl : cs.IsReduced l) :
    bottStalk cs l (cs.wordProd l) ≃ₗ[ℝ] MvPolynomial σ ℝ :=
  ((bottTopStalkEquiv cs l hl).restrictScalars ℝ).trans
    (SymmetricAlgebra.equivMvPolynomial basis).toLinearEquiv

omit [Fintype σ] in
 theorem bottTopPolynomialEquiv_homogeneous (l : List I) (hl : cs.IsReduced l)
    (n : ℤ) (s : bottStalk cs l (cs.wordProd l)) (hs : s∈bottStalkPiece cs basis l (cs.wordProd l) n) :
    bottTopPolynomialEquiv cs basis l hl s∈polynomialGrading ℝ σ n := by
  apply (mem_symmetricGrading basis n _).mp
  exact (bottTopStalkEquiv_homogeneous cs basis l hl n s).mpr hs

 theorem bottStalkCharacter_top (l : List I) (hl : cs.IsReduced l) :
    bottStalkCharacter cs basis l (cs.wordProd l)=1 := by
  have hd (n : ℤ) : Module.finrank ℝ (bottStalkPiece cs basis l (cs.wordProd l) n)=
      Module.finrank ℝ (polynomialGrading ℝ σ n) := by
    have hh := finrank_homogeneousEquiv (bottStalkPiece cs basis l (cs.wordProd l))
      (polynomialGrading ℝ σ) (bottTopPolynomialEquiv cs basis l hl) 0
      (fun n s hs => by simpa only [add_zero] using bottTopPolynomialEquiv_homogeneous cs basis l hl n s hs) n
    have hz : n-(0:ℤ)=n := Int.sub_zero n
    rw [hz] at hh
    exact hh.symm
  apply Hilbert.numerator_unique
    (fun n => Module.finrank ℝ (bottStalkPiece cs basis l (cs.wordProd l) n)) _ _
    (fun q => (1-q)⁻¹ ^ Fintype.card σ)
  · intro q _ hq
    exact pow_ne_zero _ (inv_ne_zero (sub_ne_zero.mpr (ne_of_gt hq)))
  · exact fun _ => bottStalkCharacter_hasSum cs basis l (cs.wordProd l)
  · intro q hq hq1
    simpa only [hd,Polynomial.eval₂_one,one_mul] using Hilbert.hasSum_polynomial ℝ σ hq.le hq1

 theorem bottStalkCharacter_nil (x : W) :
    bottStalkCharacter cs basis [] x=if x=1 then 1 else 0 := by
  classical
  by_cases hx : x=1
  · subst x
    simpa using bottStalkCharacter_top cs basis [] (by simp [CoxeterSystem.IsReduced])
  · let := bottStalk_nil_subsingleton cs x hx
    rw [ite_eq_right hx]
    exact bottStalkCharacter_zero cs basis [] x

 theorem bottStalkCharacter_eq_heckeWord (l : List I) (x : W) :
    bottStalkCharacter cs basis l x=HeckeQ.positiveWord cs (Polynomial.X : Polynomial ℤ) l x := by
  classical
  induction l generalizing x with
  | nil => simp only [bottStalkCharacter_nil,HeckeQ.positiveWord_nil,Hecke.basis,
      Finsupp.single_apply]; split_ifs <;> simp_all
  | cons i l ih =>
    rw [HeckeQ.positiveWord_cons_coeff]
    by_cases hd : cs.length (cs.simple i*x)<cs.length x
    · rw [ite_eq_left hd,bottStalkCharacter_descent cs basis i l x hd,ih,ih]
    · have ha : cs.length x<cs.length (cs.simple i*x) := by
        have := cs.length_simple_mul x i
        omega
      rw [ite_eq_right hd,bottStalkCharacter_ascent cs basis i l x ha,ih,ih]

end
end KLInvariance.TitsSpace
end

end OAI
