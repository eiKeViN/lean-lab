import Mathlib
import ForMathlib.RepresentationTheory.Hecke.Operators

/-! Semantic home: ForMathlib.RepresentationTheory.Hecke.Coefficients. Source spans: IntegralPairings:3.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.HeckeQ
open Hecke (Space basis)
variable {I W C : Type*} [Group W] {M : CoxeterMatrix I} [CommRing C]
noncomputable section

 theorem left_coeff (cs : CoxeterSystem M W) (q : C) (i : I) (v : Space W C) (x : W) :
    left cs q i v x =
      if cs.length (cs.simple i*x)<cs.length x then v (cs.simple i*x)+(q-1)*v x
      else q*v (cs.simple i*x) := by
  classical
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v v' hv hv' =>
    simp only [map_add,Finsupp.add_apply,hv,hv']
    split_ifs <;> ring
  | single w c =>
    have hc : Finsupp.single w c=c • (basis w : Space W C) := by
      simp [basis,Finsupp.smul_single]
    rw [hc,map_smul,left_basis]
    by_cases h : w=cs.simple i*x
    · subst w
      have hd : cs.length (cs.simple i*(cs.simple i*x))<cs.length (cs.simple i*x) ↔
          ¬cs.length (cs.simple i*x)<cs.length x := by
        simp only [cs.simple_mul_simple_cancel_left]
        have := cs.length_simple_mul x i
        omega
      have hn : cs.simple i*x≠x := by
        intro he
        have := cs.length_simple_mul x i
        rw [he] at this
        omega
      simp only [Finsupp.smul_apply,smul_eq_mul,basis,Finsupp.single_apply,
        cs.simple_mul_simple_cancel_left,hn,ite_false]
      have hlength := cs.length_simple_mul x i
      split_ifs <;> try omega
      all_goals simp [Ne.symm hn] <;> try ring
    · have hn : cs.simple i*w≠x := by
        intro he
        apply h
        rw [←he]
        simp
      by_cases hw : w=x
      · subst w
        simp only [Finsupp.smul_apply,smul_eq_mul,basis,Finsupp.single_apply,
          Ne.symm hn,ite_false]
        split_ifs <;> simp [Ne.symm hn] ; try ring
      · simp only [Finsupp.smul_apply,smul_eq_mul,basis,Finsupp.single_apply,
          h,hw,ite_false]
        split_ifs <;> simp [hn,hw]

 theorem left_plus_coeff (cs : CoxeterSystem M W) (q : C) (i : I)
    (v : Space W C) (x : W) :
    (v+left cs q i v) x = if cs.length (cs.simple i*x)<cs.length x then
      v (cs.simple i*x)+q*v x else v x+q*v (cs.simple i*x) := by
  rw [Finsupp.add_apply,left_coeff]
  split_ifs <;> ring

 def positiveWord (cs : CoxeterSystem M W) (q : C) : List I → Space W C
  | [] => basis 1
  | i::l => positiveWord cs q l+left cs q i (positiveWord cs q l)

 @[simp] theorem positiveWord_nil (cs : CoxeterSystem M W) (q : C) :
    positiveWord cs q []=basis 1 := rfl

 theorem positiveWord_cons_coeff (cs : CoxeterSystem M W) (q : C) (i : I)
    (l : List I) (x : W) :
    positiveWord cs q (i::l) x = if cs.length (cs.simple i*x)<cs.length x then
      positiveWord cs q l (cs.simple i*x)+q*positiveWord cs q l x
      else positiveWord cs q l x+q*positiveWord cs q l (cs.simple i*x) :=
  left_plus_coeff cs q i (positiveWord cs q l) x

end
end KLInvariance.HeckeQ
end

end OAI
