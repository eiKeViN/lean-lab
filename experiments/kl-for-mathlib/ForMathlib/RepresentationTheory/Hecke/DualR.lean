module
public import Mathlib
public import ForMathlib.RepresentationTheory.Hecke.Operators

public section

/-! Semantic home: ForMathlib.RepresentationTheory.Hecke.DualR. Source spans: Dihedral:6.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.HeckeQ

universe uR vR
variable {B : Type uR} {W : Type vR} [Group W] {M : CoxeterMatrix B}
variable {C : Type*} [CommRing C]

@[expose] noncomputable def dualR (cs : CoxeterSystem M W) (q : Cˣ) (x y : W) : C :=
  (-(q : C)) ^ cs.length y * (-(↑q⁻¹ : C)) ^ cs.length x * rValue cs q⁻¹ x y

@[simp] theorem dualR_diagonal (cs : CoxeterSystem M W) (q : Cˣ) (x : W) :
    dualR cs q x x = 1 := by
  rw [dualR, rValue_diagonal, mul_one, ← mul_pow]
  simp

theorem dualR_zero (cs : CoxeterSystem M W) (q : Cˣ) (x y : W)
    (h : ¬BruhatLE cs x y) : dualR cs q x y = 0 := by
  simp [dualR, rValue_zero cs q⁻¹ x y h]

theorem dualR_recursion (cs : CoxeterSystem M W) (q : Cˣ) (x y : W) (i : B)
    (hy : cs.length (cs.simple i * y) < cs.length y) :
    dualR cs q x y =
      if cs.length (cs.simple i * x) < cs.length x then
        dualR cs q (cs.simple i * x) (cs.simple i * y)
      else ((q : C) - 1) * dualR cs q x (cs.simple i * y) +
        (q : C) * dualR cs q (cs.simple i * x) (cs.simple i * y) := by
  have hyl : cs.length y = cs.length (cs.simple i * y) + 1 := by
    have := cs.length_simple_mul y i
    omega
  unfold dualR
  rw [rValue_recursion cs q⁻¹ x y i hy]
  split_ifs with hx
  · have hxl : cs.length x = cs.length (cs.simple i * x) + 1 := by
      have := cs.length_simple_mul x i
      omega
    rw [hyl, hxl, pow_succ, pow_succ]
    calc
      _ = (-(q:C)) ^ cs.length (cs.simple i * y) *
          (-(↑q⁻¹:C)) ^ cs.length (cs.simple i * x) *
          rValue cs q⁻¹ (cs.simple i * x) (cs.simple i * y) *
          ((q:C) * (↑q⁻¹:C)) := by ring
      _ = _ := by rw [q.mul_inv, mul_one]
  · have hxl : cs.length (cs.simple i * x) = cs.length x + 1 := by
      have := cs.length_simple_mul x i
      omega
    rw [hyl, hxl, pow_succ, pow_succ]
    have hq : (-(q:C)) * ((↑q⁻¹:C) - 1) = (q:C) - 1 := by
      rw [mul_sub, neg_mul, q.mul_inv, mul_one]
      ring
    calc
      _ = (-(q:C)) ^ cs.length (cs.simple i * y) *
          (-(↑q⁻¹:C)) ^ cs.length x *
          ((-(q:C)) * ((↑q⁻¹:C) - 1)) * rValue cs q⁻¹ x (cs.simple i * y) +
          (q:C) * ((-(q:C)) ^ cs.length (cs.simple i * y) *
          ((-(↑q⁻¹:C)) ^ cs.length x * (-(↑q⁻¹:C))) *
          rValue cs q⁻¹ (cs.simple i * x) (cs.simple i * y)) := by ring
      _ = _ := by rw [hq]; ring

/-- Signed inversion symmetry of actual equal-parameter R-values, proved
from all-descent recurrence, not imposed as an additional normalization. -/
theorem rValue_eq_dualR (cs : CoxeterSystem M W) (q : Cˣ) (x y : W) :
    rValue cs q x y = dualR cs q x y := by
  suffices ∀ n : ℕ, ∀ y : W, cs.length y = n → ∀ x,
      rValue cs q x y = dualR cs q x y by
    exact this _ y rfl x
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro y hy x
    by_cases hy1 : y = 1
    · subst y
      by_cases hx1 : x = 1
      · subst x
        simp
      · have hnot : ¬BruhatLE cs x 1 := by
          intro h
          have hl := length_le_of_bruhat cs h
          have hl0 : cs.length x = 0 := by simpa using hl
          exact hx1 (cs.length_eq_zero_iff.mp hl0)
        rw [rValue_zero cs q x 1 hnot, dualR_zero cs q x 1 hnot]
    · obtain ⟨i, hi⟩ := cs.exists_leftDescent_of_ne_one hy1
      have hsmall : cs.length (cs.simple i * y) < n := hy ▸ hi
      rw [rValue_recursion cs q x y i hi, dualR_recursion cs q x y i hi,
        ih _ hsmall _ rfl x, ih _ hsmall _ rfl (cs.simple i * x)]

/-- R at the inverse parameter is exactly the corresponding bar coefficient
with the bottom q-power. This is the coefficient form used below. -/
theorem rValue_inverse_eq_barBasis (cs : CoxeterSystem M W) (q : Cˣ) (x y : W) :
    rValue cs q⁻¹ x y = (q:C) ^ cs.length x * barBasis cs q y x := by
  rw [rValue_eq_dualR cs q⁻¹, dualR, inv_inv, rValue]
  simp only [neg_pow (↑q⁻¹:C), neg_pow (q:C)]
  have hsign (n : ℕ) : (-1:C)^n * (-1:C)^n = 1 := by
    rw [← mul_pow]; simp
  calc
    _ = ((-1:C)^cs.length y * (-1:C)^cs.length y) *
        ((-1:C)^cs.length x * (-1:C)^cs.length x) *
        (((↑q⁻¹:C) * (q:C)) ^ cs.length y) *
        (q:C)^cs.length x * barBasis cs q y x := by ring
    _ = _ := by rw [hsign, hsign, q.inv_mul]; simp

end KLInvariance.HeckeQ
end

end OAI
