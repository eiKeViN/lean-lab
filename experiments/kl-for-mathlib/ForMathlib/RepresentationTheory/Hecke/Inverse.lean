import Mathlib
import ForMathlib.GroupTheory.Coxeter.Bruhat.LowerFinset
import ForMathlib.RepresentationTheory.Hecke.Operators

/-! Semantic home: ForMathlib.RepresentationTheory.Hecke.Inverse. Source spans: Hecke:4.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

namespace KLInvariance

open Polynomial

universe u v u' v'

variable {B : Type u} {W : Type v} [klPreservedInstance1 : Group W] {M : CoxeterMatrix B}


attribute [local instance] OAI.KLInvariance.instDecidableEq_oAI
namespace HeckeQ

open Hecke (Space basis)
variable {C : Type*} [CommRing C]

theorem bar_coeff_inverse (cs : CoxeterSystem M W) (q : Cˣ) (x y : W) :
    ∑ z ∈ lowerFinset cs y, barBasis cs q z x * barBasis cs q⁻¹ y z =
      if x = y then 1 else 0 := by
  classical
  have h := congrArg (fun v : Space W C => v x) (barLinear_barBasis cs q y)
  rw [barLinear, Finsupp.linearCombination_apply, Finsupp.sum_apply] at h
  have hs : (barBasis cs q⁻¹ y).support ⊆ lowerFinset cs y := by
    intro z hz
    apply (mem_lowerFinset cs y z).mpr
    by_contra hn
    exact Finsupp.mem_support_iff.mp hz (barBasis_zero cs _ _ _ hn)
  rw [Finsupp.sum_of_support_subset _ hs _ (by simp), basis, Finsupp.single_apply] at h
  simpa only [Finsupp.smul_apply, smul_eq_mul, mul_comm, eq_comm] using h

theorem rValue_inverse_factor (cs : CoxeterSystem M W) (q : Cˣ) (x z y : W) :
    rValue cs q x z * (q : C) ^ cs.length y * (↑q⁻¹ : C) ^ cs.length z *
        rValue cs q⁻¹ z y =
      ((-1 : C) ^ cs.length x * (-1 : C) ^ cs.length y) *
        (barBasis cs q z x * barBasis cs q⁻¹ y z) := by
  simp only [rValue]
  rw [neg_pow (q : C), neg_pow (↑q⁻¹ : C)]
  calc
    _ = ((-1 : C) ^ cs.length x * (-1 : C) ^ cs.length y) *
        (((-1 : C) * (-1)) ^ cs.length z *
          ((q : C) * (↑q⁻¹ : C)) ^ cs.length z *
          ((q : C) * (↑q⁻¹ : C)) ^ cs.length y) *
        (barBasis cs q z x * barBasis cs q⁻¹ y z) := by simp only [mul_pow]; ring
    _ = _ := by simp

/-- The exact R-kernel identity, before specialization to polynomials. -/
theorem rValue_inverse (cs : CoxeterSystem M W) (q : Cˣ) (x y : W) :
    ∑ z ∈ lowerFinset cs y,
      rValue cs q x z * (q : C) ^ cs.length y * (↑q⁻¹ : C) ^ cs.length z *
        rValue cs q⁻¹ z y = if x = y then 1 else 0 := by
  classical
  simp_rw [rValue_inverse_factor]
  rw [← Finset.mul_sum, bar_coeff_inverse]
  split_ifs with h
  · subst y
    rw [← mul_pow]
    simp
  · simp

end HeckeQ
end KLInvariance

end OAI
