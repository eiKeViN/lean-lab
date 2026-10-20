import Mathlib
import OAI.RepresentationTheory.KazhdanLusztig.Polynomials.Canonical

/-! Semantic home: OAI.RepresentationTheory.KazhdanLusztig.Polynomials.Normalization. Source spans: Dihedral:9.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance
open Polynomial
universe u v
variable {B : Type u} {W : Type v} [Group W] {M : CoxeterMatrix B}

/-- The exact square-parameter normalization, proved from the two genuine
Hecke recurrences. Integer exponents let the formula include incomparable
pairs without silently changing the R-polynomial definition. -/
theorem rPolynomial_normalization {C : Type*} [Field C]
    (cs : CoxeterSystem M W) (v : C) (hv : v ≠ 0) (x y : W) :
    eval₂ (Int.castRingHom C) (v^2) (rPolynomial cs x y) =
      v ^ ((cs.length y : ℤ) - cs.length x) *
        eval₂ (Int.castRingHom C) (v-v⁻¹) (Hecke.rTilde cs x y) := by
  rw [rPolynomial_eq_constructed]
  suffices ∀ n : ℕ, ∀ y : W, cs.length y = n → ∀ x,
    eval₂ (Int.castRingHom C) (v^2) (OrdinaryR.polynomial cs x y) =
      v ^ ((cs.length y : ℤ) - cs.length x) *
        eval₂ (Int.castRingHom C) (v-v⁻¹) (Hecke.rTilde cs x y) from
    this _ y rfl x
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro y hy x
    by_cases h1 : y=1
    · subst y
      by_cases hx : x=1
      · subst x; simp
      · have hn : ¬BruhatLE cs x 1 := by
          intro h
          have hl := length_le_of_bruhat cs h
          have hx0 : cs.length x=0 := by simpa using hl
          exact hx (cs.length_eq_zero_iff.mp hx0)
        rw [OrdinaryR.polynomial_zero cs _ _ hn,Hecke.rTilde_zero cs _ _ hn]
        simp
    · obtain ⟨i,hi⟩ := cs.exists_leftDescent_of_ne_one h1
      have hlt : cs.length (cs.simple i*y)<n := hy ▸ hi
      have hylen : cs.length (cs.simple i*y)+1=cs.length y := by
        have := cs.length_simple_mul y i; omega
      rw [OrdinaryR.polynomial_recursion cs x y i hi,Hecke.rTilde_recursion cs x y i hi]
      by_cases hx : cs.length (cs.simple i*x)<cs.length x
      · rw [ite_eq_left hx,ite_eq_left hx,ih _ hlt _ rfl (cs.simple i*x)]
        congr 2
        have := cs.length_simple_mul x i
        omega
      · rw [ite_eq_right hx,ite_eq_right hx]
        simp only [eval₂_add,eval₂_mul,eval₂_sub,eval₂_X,eval₂_one]
        rw [ih _ hlt _ rfl x,ih _ hlt _ rfl (cs.simple i*x)]
        have hxlen : cs.length (cs.simple i*x)=cs.length x+1 := by
          have := cs.length_simple_mul x i; omega
        have h1 : (cs.length (cs.simple i*y) : ℤ)-cs.length x =
            ((cs.length y : ℤ)-cs.length x)-1 := by omega
        have h2 : (cs.length (cs.simple i*y) : ℤ)-cs.length (cs.simple i*x) =
            ((cs.length y : ℤ)-cs.length x)-2 := by omega
        rw [h1,h2,zpow_sub₀ hv ((cs.length y : ℤ)-cs.length x) 1,
          zpow_sub₀ hv ((cs.length y : ℤ)-cs.length x) 2]
        simp only [zpow_ofNat]
        field_simp [hv]
        ; ring

/-- The manuscript's q^{-d/2} P(q), written with t^2=q so no square-root
branch is hidden. This is an evaluation of the already constructed genuine
KL polynomial, not a new combinatorial invariant. -/
noncomputable def scaledKL {C : Type*} [Field C]
    (cs : CoxeterSystem M W) (t : C) (x b : W) : C :=
  t ^ ((cs.length x : ℤ)-cs.length b) *
    eval₂ (Int.castRingHom C) (t^2) (klPolynomial cs x b)

/-- Exact normalized reciprocity in the direction useful for reversing the
parameter. No path formula and no moment-graph assumption occurs here. -/
theorem scaledKL_reciprocity_inverse {C : Type*} [Field C]
    (cs : CoxeterSystem M W) (v : C) (hv : v ≠ 0)
    (x b : W) (hxb : BruhatLE cs x b) :
    scaledKL cs v⁻¹ x b = ∑ᶠ z : Interval cs x b,
      eval₂ (Int.castRingHom C) (v-v⁻¹) (Hecke.rTilde cs x z.val) *
        scaledKL cs v z.val b := by
  classical
  let : Finite (Interval cs x b) := interval_finite cs x b
  let : Fintype (Interval cs x b) := Fintype.ofFinite _
  have hrec := (klFamilies_spec cs).reciprocity x b hxb
  change reflect (rankDifference cs x b) (klPolynomial cs x b) =
      ∑ᶠ z : Interval cs x b, rPolynomial cs x z.val * klPolynomial cs z.val b at hrec
  have hdeg : (klPolynomial cs x b).natDegree ≤ rankDifference cs x b := by
    rw [klPolynomial_eq_constructed]
    exact CanonicalP.polynomial_degree cs x b
  let q : Cˣ := Units.mk0 (v^2) (pow_ne_zero 2 hv)
  have heval := congrArg (eval₂ (Int.castRingHom C) (q : C)) hrec
  rw [eval₂_reflect_unit q _ _ hdeg] at heval
  simp only [finsum_eq_sum_of_fintype,eval₂_finsetSum,eval₂_mul] at heval ⊢
  have hq : (q : C) = v^2 := rfl
  have hqi : (↑q⁻¹ : C) = (v⁻¹)^2 := by simp [q,inv_pow]
  rw [hq,hqi] at heval
  have heq := congrArg (fun a : C => v ^ ((cs.length x : ℤ)-cs.length b)*a) heval
  have hd : (rankDifference cs x b : ℤ) = (cs.length b : ℤ)-cs.length x := by
    have hlen := length_le_of_bruhat cs hxb
    simp [rankDifference,Int.ofNat_sub hlen]
  have hscale : v ^ ((cs.length x : ℤ)-cs.length b) *
      (v^2)^(rankDifference cs x b) =
        (v⁻¹) ^ ((cs.length x : ℤ)-cs.length b) := by
    rw [←pow_mul,←zpow_natCast,←zpow_add₀ hv,inv_zpow,←zpow_neg]
    congr 1
    push_cast
    omega
  rw [←mul_assoc,hscale,Finset.mul_sum] at heq
  change (v⁻¹)^((cs.length x : ℤ)-cs.length b)*
      eval₂ (Int.castRingHom C) ((v⁻¹)^2) (klPolynomial cs x b) = _
  rw [heq]
  apply Finset.sum_congr rfl
  intro z _
  rw [rPolynomial_normalization cs v hv]
  unfold scaledKL
  calc
    _ = (v ^ ((cs.length x : ℤ)-cs.length b) *
        v ^ ((cs.length z.val : ℤ)-cs.length x)) *
        eval₂ (Int.castRingHom C) (v-v⁻¹) (Hecke.rTilde cs x z.val) *
        eval₂ (Int.castRingHom C) (v^2) (klPolynomial cs z.val b) := by ring
    _ = _ := by
      rw [←zpow_add₀ hv,show (cs.length x : ℤ)-cs.length b+
        ((cs.length z.val : ℤ)-cs.length x) =
        (cs.length z.val : ℤ)-cs.length b by ring]
      ring


theorem scaledKL_reciprocity {C : Type*} [Field C]
    (cs : CoxeterSystem M W) (v : C) (hv : v ≠ 0)
    (x b : W) (hxb : BruhatLE cs x b) :
    scaledKL cs v x b = ∑ᶠ z : Interval cs x b,
      eval₂ (Int.castRingHom C) (v⁻¹-v) (Hecke.rTilde cs x z.val) *
        scaledKL cs v⁻¹ z.val b := by
  simpa only [inv_inv] using scaledKL_reciprocity_inverse cs v⁻¹ (inv_ne_zero hv) x b hxb

end KLInvariance
end

end OAI
