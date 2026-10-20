import Mathlib
import OAI.GroupTheory.Coxeter.Bruhat.LowerFinset
import OAI.RepresentationTheory.Hecke.Coefficients
import OAI.RepresentationTheory.Hecke.DualR

/-! Semantic home: OAI.RepresentationTheory.Hecke.PositiveWord. Source spans: CharacterReciprocity:13, CharacterReciprocity:14.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.HeckeQ
open Hecke (Space basis)
variable {I W C : Type*} [Group W] {M : CoxeterMatrix I} [CommRing C]
noncomputable section

 theorem one_add_leftInv (cs : CoxeterSystem M W) (q : Cˣ) (i : I) (v : Space W C) :
    v+leftInv cs q i v=(↑q⁻¹:C) • (v+left cs (q:C) i v) := by
  rw [leftInv_apply,smul_sub,smul_smul,smul_add]
  have h : (↑q⁻¹:C)*((q:C)-1)=1-(↑q⁻¹:C) := by rw [mul_sub,q.inv_mul,mul_one]
  rw [h,sub_smul,one_smul]
  module

 theorem barLinear_positiveWord (cs : CoxeterSystem M W) (q : Cˣ) (l : List I) :
    barLinear cs q (positiveWord cs (↑q⁻¹:C) l)=
      (↑q⁻¹:C)^l.length • positiveWord cs (q:C) l := by
  induction l with
  | nil => simp [barBasis_one]
  | cons i l ih =>
    simp only [positiveWord,map_add]
    have h := congrArg (fun f : Module.End C (Space W C) => f (positiveWord cs (↑q⁻¹:C) l))
      (barLinear_left cs q i)
    simp only [Module.End.mul_apply] at h
    rw [h,ih,map_smul,← smul_add,one_add_leftInv,smul_smul,List.length_cons,pow_succ]

 theorem positiveWord_support (cs : CoxeterSystem M W) (q : C) (l : List I)
    (hl : cs.IsReduced l) : (positiveWord cs q l).support ⊆ lowerFinset cs (cs.wordProd l) := by
  classical
  induction l with
  | nil => simpa [positiveWord,Hecke.basis,lowerFinset] using
      (show (Finsupp.single 1 (1:C)).support ⊆ lowerFinset cs 1 by
        intro x hx
        by_cases h : x=1
        · subst x; exact (mem_lowerFinset cs 1 1).mpr .refl
        · simp [Finsupp.mem_support_iff,Ne.symm h] at hx)
  | cons i l ih =>
    have ht : cs.IsReduced l := by simpa using hl.drop 1
    have ha : ¬cs.length (cs.simple i*cs.wordProd l)<cs.length (cs.wordProd l) := by
      have h := hl.eq
      simp only [cs.wordProd_cons,List.length_cons,←ht.eq] at h
      omega
    intro x hx
    apply (mem_lowerFinset cs (cs.wordProd (i::l)) x).mpr
    have step (y : W) (hy : BruhatLE cs y (cs.wordProd l)) :
        BruhatLE cs (upperSimple cs i y) (cs.wordProd (i::l)) := by
      simpa only [upperSimple,ite_eq_right ha,cs.wordProd_cons] using upperSimple_mono cs i hy
    have h : positiveWord cs q l x≠0 ∨ positiveWord cs q l (cs.simple i*x)≠0 := by
      by_contra hn
      push Not at hn
      rw [Finsupp.mem_support_iff,positiveWord_cons_coeff,hn.1,hn.2] at hx
      split_ifs at hx <;> simp_all
    rcases h with h|h
    · exact (le_upperSimple cs i x).trans
        (step x ((mem_lowerFinset cs _ _).mp (ih ht (Finsupp.mem_support_iff.mpr h))))
    · have hh := step (cs.simple i*x)
        ((mem_lowerFinset cs _ _).mp (ih ht (Finsupp.mem_support_iff.mpr h)))
      rw [upperSimple_mul] at hh
      exact (le_upperSimple cs i x).trans hh

 theorem positiveWord_rValue (cs : CoxeterSystem M W) (q : Cˣ) (l : List I)
    (hl : cs.IsReduced l) (x : W) :
    ∑ z ∈ lowerFinset cs (cs.wordProd l), rValue cs q x z * positiveWord cs (q:C) l z=
      (↑q⁻¹:C)^cs.length x * (q:C)^l.length * positiveWord cs (↑q⁻¹:C) l x := by
  classical
  have h := congrArg (fun v : Space W C => v x) (barLinear_positiveWord cs q⁻¹ l)
  simp only [inv_inv] at h
  rw [barLinear,Finsupp.linearCombination_apply,Finsupp.sum_apply,
    Finsupp.sum_of_support_subset _ (positiveWord_support cs (q:C) l hl) _ (by simp)] at h
  simp only [Finsupp.smul_apply,smul_eq_mul] at h
  have hr (z : W) : rValue cs q x z=(↑q⁻¹:C)^cs.length x * barBasis cs q⁻¹ z x := by
    simpa using rValue_inverse_eq_barBasis cs q⁻¹ x z
  simp only [hr,mul_assoc,←Finset.mul_sum]
  rw [show (∑ z ∈ lowerFinset cs (cs.wordProd l), barBasis cs q⁻¹ z x * positiveWord cs (q:C) l z)=
      (q:C)^l.length * positiveWord cs (↑q⁻¹:C) l x by
    simpa only [mul_comm] using h]

end
end KLInvariance.HeckeQ
end


section
namespace KLInvariance.HeckeQ
open Hecke (Space basis)
variable {I W C : Type*} [Group W] {M : CoxeterMatrix I} [CommRing C]
noncomputable section

 theorem eval_positiveWord (cs : CoxeterSystem M W) (q : C) (l : List I) (x : W) :
    Polynomial.eval₂ (Int.castRingHom C) q
      (positiveWord cs (Polynomial.X : Polynomial ℤ) l x)=positiveWord cs q l x := by
  classical
  induction l generalizing x with
  | nil => simp only [positiveWord_nil,Hecke.basis,Finsupp.single_apply]; split_ifs <;> simp
  | cons i l ih =>
    rw [positiveWord_cons_coeff,positiveWord_cons_coeff]
    split_ifs <;> simp only [Polynomial.eval₂_add,Polynomial.eval₂_mul,
      Polynomial.eval₂_X,ih]

end
end KLInvariance.HeckeQ
end

end OAI
