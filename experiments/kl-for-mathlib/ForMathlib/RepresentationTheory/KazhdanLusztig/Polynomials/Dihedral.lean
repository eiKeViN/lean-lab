module
public import Mathlib
public import ForMathlib.GroupTheory.Coxeter.Dihedral.Words
public import ForMathlib.RepresentationTheory.Hecke.DualR
public import ForMathlib.RepresentationTheory.KazhdanLusztig.Polynomials.Canonical

public section

/-! Semantic home: ForMathlib.RepresentationTheory.KazhdanLusztig.Polynomials.Dihedral. Source spans: Dihedral:4, Dihedral:5, Dihedral:7, Dihedral:8.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.Dihedral

@[expose] noncomputable local instance _root_.OAI.KLInvariance.Dihedral.instDecidable_oAI_1 (p : Prop) : Decidable p := Classical.propDecidable p

open Hecke (Space basis)
variable {W : Type*} [Group W] {M : CoxeterMatrix Bool}
variable {C : Type*} [CommRing C]

@[expose] noncomputable def lowerSum (cs : CoxeterSystem M W) (w : W) : Space W C :=
  ∑ z ∈ lowerFinset cs w, basis z

@[simp] theorem lowerSum_coeff (cs : CoxeterSystem M W) (w x : W) :
    (lowerSum cs w : Space W C) x = if BruhatLE cs x w then 1 else 0 := by
  classical
  simp [lowerSum, basis, Finsupp.single_apply, eq_comm]

@[simp] theorem lowerSum_one (cs : CoxeterSystem M W) :
    (lowerSum cs 1 : Space W C) = basis 1 := by
  classical
  ext x
  simp only [lowerSum_coeff, basis, Finsupp.single_apply]
  have h : BruhatLE cs x 1 ↔ 1 = x := by
    rw [bruhat_iff_length_lt_or_eq]
    simp [eq_comm]
  rw [h]

/-- The two members of an s-string enter a lower ideal together precisely
on the common lower interval appearing in the source's rank-two product. -/
theorem double_string (cs : CoxeterSystem M W) (i : Bool) (n : ℕ)
    (hr : cs.IsReduced (alt i (n+2))) (x : W) :
    (BruhatLE cs x (cs.wordProd (alt (!i) (n+1))) ∧
      BruhatLE cs (cs.simple i * x) (cs.wordProd (alt (!i) (n+1)))) ↔
    (0 < n ∧ BruhatLE cs x (cs.wordProd (alt i n))) := by
  have hr' : cs.IsReduced (alt (!i) (n+1)) := by simpa using hr.drop 1
  have hrp := reduced_alt_take cs hr (show n ≤ n+2 by omega)
  have hlenw : cs.length (cs.wordProd (alt i (n+2))) = n+2 := by
    simpa only [length_alt] using hr.eq
  have hlenz : cs.length (cs.wordProd (alt (!i) (n+1))) = n+1 := by
    simpa only [length_alt] using hr'.eq
  have hlenp : cs.length (cs.wordProd (alt i n)) = n := by
    simpa only [length_alt] using hrp.eq
  have hsz : cs.simple i * cs.wordProd (alt (!i) (n+1)) =
      cs.wordProd (alt i (n+2)) := by rw [alt_succ i (n+1), cs.wordProd_cons]
  constructor
  · rintro ⟨hx, hsx⟩
    have hxlen := length_le_of_bruhat cs hx
    have hsxlen := length_le_of_bruhat cs hsx
    have hxl : cs.length x < n+1 := by
      rcases (bruhat_iff_length_lt_or_eq cs _ _).mp hx with h | rfl
      · omega
      · rw [hsz, hlenw] at hsxlen
        omega
    have hsxl : cs.length (cs.simple i * x) < n+1 := by
      rcases (bruhat_iff_length_lt_or_eq cs _ _).mp hsx with h | h
      · omega
      · have heq : x = cs.wordProd (alt i (n+2)) := by
          rw [← hsz, ← h, cs.simple_mul_simple_cancel_left]
        rw [heq, hlenw] at hxl
        omega
    have hchange := cs.length_simple_mul x i
    have hn : 0 < n := by omega
    refine ⟨hn, ?_⟩
    by_cases hxlt : cs.length x < n
    · exact shorter_bruhat cs (by omega)
    · have hxi : cs.length x = n := by omega
      have hdesc : cs.length (cs.simple i * x) < cs.length x := by omega
      have heq := eq_alt_of_descent cs i hdesc
      rw [hxi] at heq
      rw [heq]
      exact bruhat_refl cs _
  · rintro ⟨hn, hx⟩
    have hxlen := length_le_of_bruhat cs hx
    constructor
    · exact shorter_bruhat cs (by omega)
    · by_cases hxlt : cs.length x < n
      · have := cs.length_simple_mul x i
        exact shorter_bruhat cs (by omega)
      · have heq : x = cs.wordProd (alt i n) := by
          rcases (bruhat_iff_length_lt_or_eq cs _ _).mp hx with h | h
          · omega
          · exact h
        obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show n ≠ 0 by omega)
        have hrpt : cs.IsReduced (alt (!i) k) := by simpa using hrp.drop 1
        have hpk : cs.length (cs.simple i * x) = k := by
          rw [heq, alt_succ, cs.wordProd_cons, cs.simple_mul_simple_cancel_left,
            hrpt.eq, length_alt]
        exact shorter_bruhat cs (by omega)

end KLInvariance.Dihedral
end


section
namespace KLInvariance.Dihedral

@[expose] noncomputable local instance _root_.OAI.KLInvariance.Dihedral.instDecidable_oAI_2 (p : Prop) : Decidable p := Classical.propDecidable p

open Hecke (Space basis)
variable {W : Type*} [Group W] {M : CoxeterMatrix Bool}
variable {C : Type*} [CommRing C]

theorem left_plus_coeff (cs : CoxeterSystem M W) (q : Cˣ) (i : Bool)
    (v : Space W C) (x : W) :
    (v + HeckeQ.left cs (q : C) i v) x =
      if cs.length (cs.simple i * x) < cs.length x then
        v (cs.simple i * x) + (q : C) * v x
      else v x + (q : C) * v (cs.simple i * x) := by
  have h := congrArg (fun t : Space W C => (q : C) * t x)
    (HeckeQ.leftInv_apply cs q i v)
  simp only [Finsupp.smul_apply, smul_eq_mul, Finsupp.sub_apply, ← mul_assoc,
    q.mul_inv, one_mul] at h
  rw [HeckeQ.leftInv_coeff] at h
  simp only [Finsupp.add_apply]
  split_ifs at h ⊢
  · linear_combination -h + v (cs.simple i * x) * q.mul_inv
  · linear_combination -h + v x * q.mul_inv

theorem union_string (cs : CoxeterSystem M W) (i : Bool) {z : W}
    (hz : cs.length z < cs.length (cs.simple i * z)) (x : W) :
    BruhatLE cs x (cs.simple i * z) ↔
      BruhatLE cs x z ∨ BruhatLE cs (cs.simple i * x) z := by
  have hsz : cs.length (cs.simple i * (cs.simple i * z)) <
      cs.length (cs.simple i * z) := by simpa using hz
  constructor
  · intro h
    have hh := lowerSimple_mono cs i h
    simp only [lowerSimple, cs.simple_mul_simple_cancel_left] at hh
    split_ifs at hh with hx
    · exact Or.inr hh
    · exact Or.inl hh
  · rintro (h | h)
    · apply bruhat_trans cs h
      exact Relation.ReflTransGen.single ⟨hz, cs.simple i, cs.isReflection_simple i, rfl⟩
    · simpa only [cs.simple_mul_simple_cancel_left] using
        Hecke.simple_mul_le_ascent cs i h hz

@[expose] noncomputable def correction (cs : CoxeterSystem M W) (i : Bool) (n : ℕ) : Space W C :=
  if n = 0 then 0 else lowerSum cs (cs.wordProd (alt i n))

@[simp] theorem correction_coeff (cs : CoxeterSystem M W) (i : Bool) (n : ℕ) (x : W) :
    (correction cs i n : Space W C) x =
      if 0 < n ∧ BruhatLE cs x (cs.wordProd (alt i n)) then 1 else 0 := by
  classical
  by_cases h : n = 0
  · simp [correction, h]
  · have hn : 0 < n := Nat.pos_of_ne_zero h
    simp [correction, h, hn]

/-- The Hecke sum identity `loc:dihedral-product`, before normalization by
q to a half-integer power. Every interval here is genuine strong Bruhat. -/
theorem lowerSum_product (cs : CoxeterSystem M W) (q : Cˣ) (i : Bool) (n : ℕ)
    (hr : cs.IsReduced (alt i (n+2))) :
    lowerSum cs (cs.wordProd (alt (!i) (n+1))) +
      HeckeQ.left cs (q : C) i (lowerSum cs (cs.wordProd (alt (!i) (n+1)))) =
    lowerSum cs (cs.wordProd (alt i (n+2))) + (q : C) • correction cs i n := by
  classical
  have hr' : cs.IsReduced (alt (!i) (n+1)) := by simpa using hr.drop 1
  have hz : cs.length (cs.wordProd (alt (!i) (n+1))) <
      cs.length (cs.simple i * cs.wordProd (alt (!i) (n+1))) := by
    rw [← cs.wordProd_cons, ← alt_succ, hr.eq, hr'.eq, length_alt, length_alt]
    omega
  ext x
  rw [left_plus_coeff, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul,
    correction_coeff, lowerSum_coeff, lowerSum_coeff, lowerSum_coeff]
  have hu := union_string cs i hz x
  rw [← cs.wordProd_cons, ← alt_succ] at hu
  have hd := double_string cs i n hr x
  simp only [hu, ← hd]
  by_cases hdesc : cs.length (cs.simple i * x) < cs.length x
  · have hclosure : BruhatLE cs x (cs.wordProd (alt (!i) (n+1))) →
        BruhatLE cs (cs.simple i * x) (cs.wordProd (alt (!i) (n+1))) := by
      intro h
      apply bruhat_trans cs _ h
      exact Relation.ReflTransGen.single
        ⟨hdesc, cs.simple i, cs.isReflection_simple i, by simp⟩
    by_cases hx : BruhatLE cs x (cs.wordProd (alt (!i) (n+1)))
    · simp [-alt_succ, hdesc, hx, hclosure hx]
    · by_cases hs : BruhatLE cs (cs.simple i * x) (cs.wordProd (alt (!i) (n+1))) <;>
        simp [-alt_succ, hdesc, hx, hs]
  · have hasc : cs.length x < cs.length (cs.simple i * x) := by
      have := cs.length_simple_mul x i
      omega
    have hclosure : BruhatLE cs (cs.simple i * x) (cs.wordProd (alt (!i) (n+1))) →
        BruhatLE cs x (cs.wordProd (alt (!i) (n+1))) := by
      intro h
      apply bruhat_trans cs _ h
      exact Relation.ReflTransGen.single
        ⟨hasc, cs.simple i, cs.isReflection_simple i, rfl⟩
    by_cases hs : BruhatLE cs (cs.simple i * x) (cs.wordProd (alt (!i) (n+1)))
    · simp [-alt_succ, hdesc, hs, hclosure hs]
    · by_cases hx : BruhatLE cs x (cs.wordProd (alt (!i) (n+1))) <;>
        simp [-alt_succ, hdesc, hx, hs]

end KLInvariance.Dihedral
end


section
namespace KLInvariance.Dihedral

@[expose] noncomputable local instance _root_.OAI.KLInvariance.Dihedral.instDecidable_oAI_3 (p : Prop) : Decidable p := Classical.propDecidable p

open Hecke (Space basis)
variable {W : Type*} [Group W] {M : CoxeterMatrix Bool}
variable {C : Type*} [CommRing C]

@[simp] theorem lowerSum_simple (cs : CoxeterSystem M W) (i : Bool) :
    (lowerSum cs (cs.simple i) : Space W C) = basis 1 + basis (cs.simple i) := by
  classical
  ext x
  rw [lowerSum_coeff, bruhat_iff_length_lt_or_eq, cs.length_simple]
  simp only [Nat.lt_one_iff, cs.length_eq_zero_iff, Finsupp.add_apply, basis,
    Finsupp.single_apply]
  have hi : cs.simple i ≠ 1 := by
    intro h
    have := cs.length_simple i
    simp [h] at this
  by_cases hx : x = 1
  · subst x
    simp [hi]
  · by_cases hs : x = cs.simple i
    · subst x
      simp [hi, Ne.symm hi]
    · simp [hx, hs, Ne.symm hx, Ne.symm hs]

theorem plus_leftInv (cs : CoxeterSystem M W) (q : Cˣ) (i : Bool)
    (v : Space W C) :
    v + HeckeQ.leftInv cs q i v =
      (↑q⁻¹:C) • (v + HeckeQ.left cs (q:C) i v) := by
  rw [HeckeQ.leftInv_apply, smul_sub, smul_smul, mul_sub, q.inv_mul, mul_one]
  module

/-- Unnormalized form of bar invariance of the dihedral constant sums. -/
theorem bar_lowerSum_alt (cs : CoxeterSystem M W) (q : Cˣ) (i : Bool) (n : ℕ)
    (hr : cs.IsReduced (alt i n)) :
    HeckeQ.barLinear cs q (lowerSum cs (cs.wordProd (alt i n))) =
      (↑q⁻¹:C)^n • lowerSum cs (cs.wordProd (alt i n)) := by
  induction n using Nat.strong_induction_on generalizing i with
  | h n ih =>
    rcases n with _ | (_ | n)
    · simp
    · have hasc : cs.length (1:W) < cs.length (cs.simple i * 1) := by simp
      have hb := HeckeQ.barBasis_simple_mul_ascent cs q i 1 hasc
      simp only [mul_one, HeckeQ.barBasis_one] at hb
      simp only [alt_succ, alt_zero, cs.wordProd_singleton, lowerSum_simple,
        map_add, HeckeQ.barLinear_basis, HeckeQ.barBasis_one, hb]
      rw [plus_leftInv, HeckeQ.left_basis]
      simp
    · have hr' : cs.IsReduced (alt (!i) (n+1)) := by simpa using hr.drop 1
      have hrp := reduced_alt_take cs hr (show n ≤ n+2 by omega)
      have hz := ih (n+1) (by omega) (!i) hr'
      have hc : HeckeQ.barLinear cs q (correction cs i n) =
          (↑q⁻¹:C)^n • correction cs i n := by
        by_cases hn : n = 0
        · simp [correction, hn]
        · simp only [correction, ite_eq_right hn]
          exact ih n (by omega) i hrp
      have hprod := lowerSum_product cs q i n hr
      have hbar := congrArg (HeckeQ.barLinear cs q)
        (lowerSum_product cs q⁻¹ i n hr)
      have hinter := congrArg (fun f : Module.End C (Space W C) =>
          f (lowerSum cs (cs.wordProd (alt (!i) (n+1)))))
        (HeckeQ.barLinear_left cs q i)
      simp only [map_add, map_smul, Module.End.mul_apply] at hbar hinter
      rw [hinter, hz, map_smul, ← smul_add, plus_leftInv, hprod] at hbar
      simp only [smul_add, smul_smul, hc] at hbar
      have hq1 : (↑q⁻¹:C)^(n+1) * (↑q⁻¹:C) = (↑q⁻¹:C)^(n+2) := by
        exact (pow_succ (↑q⁻¹:C) (n+1)).symm
      have hq2 : (↑q⁻¹:C)^(n+1) * ((↑q⁻¹:C) * (q:C)) =
          (↑q⁻¹:C) * (↑q⁻¹:C)^n := by rw [q.inv_mul, mul_one, pow_succ'];
      rw [hq1, hq2] at hbar
      exact add_right_cancel hbar.symm

theorem bar_lowerSum (cs : CoxeterSystem M W) (q : Cˣ) (w : W) :
    HeckeQ.barLinear cs q (lowerSum cs w) =
      (↑q⁻¹:C)^cs.length w • lowerSum cs w := by
  obtain ⟨i, hi⟩ := exists_alt cs w
  have hr : cs.IsReduced (alt i (cs.length w)) := by
    simp only [CoxeterSystem.IsReduced, ← hi, length_alt]
  simpa only [← hi] using bar_lowerSum_alt cs q i (cs.length w) hr

end KLInvariance.Dihedral
end


section
namespace KLInvariance.Dihedral

@[expose] noncomputable local instance _root_.OAI.KLInvariance.Dihedral.instDecidable_oAI_4 (p : Prop) : Decidable p := Classical.propDecidable p

open Hecke (Space basis)
open Polynomial
variable {W : Type*} [Group W] {M : CoxeterMatrix Bool}
variable {C : Type*} [CommRing C]

theorem rValue_sum (cs : CoxeterSystem M W) (q : Cˣ) (x y : W)
    (hxy : BruhatLE cs x y) :
    ∑ z ∈ lowerFinset cs y, HeckeQ.rValue cs q x z =
      (q:C) ^ rankDifference cs x y := by
  classical
  have hb := congrArg (fun f : Space W C => f x) (bar_lowerSum cs q⁻¹ y)
  simp only [Finsupp.smul_apply, smul_eq_mul, inv_inv, lowerSum_coeff,
    ite_eq_left hxy, mul_one] at hb
  rw [lowerSum, map_sum] at hb
  simp only [Finsupp.coe_finsetSum, Finset.sum_apply, HeckeQ.barLinear_basis] at hb
  have hlen : cs.length y = cs.length x + rankDifference cs x y := by
    have := length_le_of_bruhat cs hxy
    unfold rankDifference
    omega
  calc
    _ = (↑q⁻¹:C)^cs.length x *
        ∑ z ∈ lowerFinset cs y, HeckeQ.barBasis cs q⁻¹ z x := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z hz
      simpa using HeckeQ.rValue_inverse_eq_barBasis cs q⁻¹ x z
    _ = (↑q⁻¹:C)^cs.length x * (q:C)^cs.length y := by rw [hb]
    _ = _ := by
      rw [hlen, pow_add]
      calc
        _ = ((↑q⁻¹:C) * (q:C))^cs.length x * (q:C)^rankDifference cs x y := by
          rw [mul_pow]; ring
        _ = _ := by rw [q.inv_mul]; simp

theorem rPolynomial_sum (cs : CoxeterSystem M W) (x y : W)
    (hxy : BruhatLE cs x y) :
    ∑ z ∈ lowerFinset cs y, OrdinaryR.polynomial cs x z =
      (X:ℤ[X]) ^ rankDifference cs x y := by
  apply Polynomial.toLaurent_injective
  simpa using rValue_sum cs OrdinaryR.variableUnit x y hxy

@[expose] noncomputable def constantP (cs : CoxeterSystem M W) (x y : W) : ℤ[X] :=
  if BruhatLE cs x y then 1 else 0

theorem constant_normalizedKL (cs : CoxeterSystem M W) :
    NormalizedKL cs (OrdinaryR.polynomial cs, constantP cs) where
  R_diagonal := OrdinaryR.polynomial_diagonal cs
  R_zero := OrdinaryR.polynomial_zero cs
  R_recursion := OrdinaryR.polynomial_recursion cs
  P_diagonal := by intro x; simp [constantP, bruhat_refl cs x]
  P_zero := by intro x y h; simp [constantP, h]
  P_degree := by
    intro x y hxy hne
    have := length_lt_of_bruhat_ne cs hxy hne
    simp only [constantP, ite_eq_left hxy, natDegree_one, mul_zero]
    unfold rankDifference
    omega
  reciprocity := by
    intro x y hxy
    simp only [constantP, ite_eq_left hxy, reflect_one]
    classical
    let := interval_finite cs x y
    let : Fintype (Interval cs x y) := Fintype.ofFinite _
    rw [finsum_eq_sum_of_fintype]
    have heq : (∑ z : Interval cs x y,
        OrdinaryR.polynomial cs x z.val * (if BruhatLE cs z.val y then 1 else 0)) =
        ∑ z : Interval cs x y, OrdinaryR.polynomial cs x z.val := by
      apply Finset.sum_congr rfl
      intro z hz
      rw [ite_eq_left z.property.2, mul_one]
    rw [heq]
    have hsum := Finset.sum_subtype (F := (inferInstance : Fintype (Interval cs x y)))
      ((lowerFinset cs y).filter (fun z => BruhatLE cs x z))
      (fun z => by simp only [Finset.mem_filter, mem_lowerFinset]; exact and_comm)
      (fun z => OrdinaryR.polynomial cs x z)
    symm
    refine hsum.symm.trans (Eq.trans ?_ (rPolynomial_sum cs x y hxy))
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro z hz hnot
    have hnxz : ¬BruhatLE cs x z := fun hxz => hnot (Finset.mem_filter.mpr ⟨hz, hxz⟩)
    exact OrdinaryR.polynomial_zero cs x z hnxz

/-- The manuscript's necessary dihedral calculation (`loc:dihedral-kl`),
for the actual KL family, with the exact standard normalization. This is
support for localization, not a substitute for general invariance. -/
theorem klPolynomial_eq_one (cs : CoxeterSystem M W) (x y : W)
    (hxy : BruhatLE cs x y) : klPolynomial cs x y = 1 := by
  have heq := normalizedKL_unique cs (klFamilies_spec cs) (constant_normalizedKL cs)
  have hp := congrArg (fun RP : PolynomialFamilies W => RP.2 x y) heq
  simpa only [klPolynomial, constantP, ite_eq_left hxy] using hp

end KLInvariance.Dihedral
end

end OAI
