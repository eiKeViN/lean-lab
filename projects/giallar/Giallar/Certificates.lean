/-
Copyright (c) 2026 Kevin Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Zhao
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Rat.BigOperators
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Certificates for external linear and integer optimizers

An external optimizer supplies a candidate and a finite certificate. The duality lemmas work over
any linearly ordered commutative ring. The executable checker uses exact rational arithmetic;
integer branches are interpreted on integer assignments, with no floating-point comparisons.

## Main results

* `dual_lower_bound`: a nonnegative linear combination of rows gives a lower bound.
* `infeasible_of_certificate`: a positive lower bound on zero refutes feasibility.
* `check_sound`: acceptance of a finite branch tree certifies its integer objective lower bound.
* `check_optimal`: a feasible candidate attaining that bound is globally integer optimal.

The checker constructs child constraints itself. A certificate cannot silently add constraints.
These statements concern result certificates, not the implementation of an external solver.
-/

@[expose] public section

namespace Giallar.Certificates

open Finset

section Linear

variable {R ι κ : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
  [Fintype ι] [Fintype κ]

/-- The dot product of finite vectors, with no inner-product conjugation. -/
def dot (a x : κ → R) : R := ∑ j, a j * x j

/-- A vector satisfies every row of the inequality system `A x ≥ b`. -/
def Feasible (A : ι → κ → R) (b : ι → R) (x : κ → R) : Prop :=
  ∀ i, b i ≤ dot (A i) x

/-- Nonnegative row multipliers whose weighted coefficients equal the objective. -/
def IsDual (A : ι → κ → R) (c : κ → R) (w : ι → R) : Prop :=
  (∀ i, 0 ≤ w i) ∧ ∀ j, ∑ i, w i * A i j = c j

omit [LinearOrder R] [IsStrictOrderedRing R] in
/-- Interchanging the two finite sums computes the weighted row expression. -/
theorem weighted_rows_eq (A : ι → κ → R) (c : κ → R) (w : ι → R)
    (h : ∀ j, ∑ i, w i * A i j = c j) (x : κ → R) :
    ∑ i, w i * dot (A i) x = dot c x := by
  simp only [dot, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  simp only [← mul_assoc, ← Finset.sum_mul, h]

/-- Weak duality: a checked nonnegative row combination is a valid objective lower bound. -/
theorem dual_lower_bound (A : ι → κ → R) (b : ι → R) (c : κ → R)
    (w : ι → R) (hw : IsDual A c w) (x : κ → R) (hx : Feasible A b x) :
    (∑ i, w i * b i) ≤ dot c x := by
  rw [← weighted_rows_eq A c w hw.2 x]
  exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hx i) (hw.1 i)

/-- A nonnegative combination with zero coefficients and positive right side refutes feasibility. -/
theorem infeasible_of_certificate (A : ι → κ → R) (b : ι → R) (w : ι → R)
    (hw : IsDual A 0 w) (hpos : 0 < ∑ i, w i * b i) :
    ¬ ∃ x, Feasible A b x := by
  rintro ⟨x, hx⟩
  have h := dual_lower_bound A b 0 w hw x hx
  simp only [dot, Pi.zero_apply, zero_mul, Finset.sum_const_zero] at h
  exact (not_lt_of_ge h) hpos

/-- A feasible candidate meeting a dual bound minimizes the objective on all feasible points. -/
theorem optimal_of_dual (A : ι → κ → R) (b : ι → R) (c : κ → R)
    (w : ι → R) (hw : IsDual A c w) (x₀ : κ → R) (hx₀ : Feasible A b x₀)
    (hvalue : dot c x₀ = ∑ i, w i * b i) :
    Feasible A b x₀ ∧ ∀ x, Feasible A b x → dot c x₀ ≤ dot c x := by
  refine ⟨hx₀, fun x hx => ?_⟩
  rw [hvalue]
  exact dual_lower_bound A b c w hw x hx

end Linear

/-- A rational dual certificate also bounds arbitrary real feasible points. -/
theorem rational_dual_lower_bound_real {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : ι → κ → ℚ) (b : ι → ℚ) (c : κ → ℚ) (w : ι → ℚ)
    (hw : IsDual A c w) (x : κ → ℝ)
    (hx : Feasible (fun i j => (A i j : ℝ)) (fun i => (b i : ℝ)) x) :
    ((∑ i, w i * b i : ℚ) : ℝ) ≤ dot (fun j => (c j : ℝ)) x := by
  have hreal : IsDual (fun i j => (A i j : ℝ))
      (fun j => (c j : ℝ)) (fun i => (w i : ℝ)) := by
    constructor
    · intro i
      change 0 ≤ (w i : ℝ)
      exact Rat.cast_nonneg.mpr (hw.1 i)
    · intro j
      change ∑ i, (w i : ℝ) * (A i j : ℝ) = (c j : ℝ)
      simpa only [Rat.cast_sum, Rat.cast_mul] using
        congrArg (fun q : ℚ => (q : ℝ)) (hw.2 j)
  simpa only [Rat.cast_sum, Rat.cast_mul] using
    dual_lower_bound _ _ _ _ hreal x hx

/-- A finite rational inequality system. Its row count is part of the type. -/
structure System (n m : ℕ) where
  /-- The coefficients of each row. -/
  coeff : Fin m → Fin n → ℚ
  /-- The lower bound of each row. -/
  rhs : Fin m → ℚ

namespace System

variable {n m : ℕ}

/-- Feasibility for an exact rational assignment. -/
def feasible (P : System n m) (x : Fin n → ℚ) : Prop := Feasible P.coeff P.rhs x

/-- Prepend one row; all previous rows are retained without alteration. -/
def prepend (P : System n m) (a : Fin n → ℚ) (b : ℚ) : System n (m + 1) where
  coeff := Fin.cases a P.coeff
  rhs := Fin.cases b P.rhs

@[simp]
theorem feasible_prepend (P : System n m) (a : Fin n → ℚ) (b : ℚ)
    (x : Fin n → ℚ) :
    (P.prepend a b).feasible x ↔ b ≤ dot a x ∧ P.feasible x := by
  simp [feasible, Feasible, prepend, Fin.forall_fin_succ]

/-- The row `-xⱼ ≥ -k` encoding the left integer branch. -/
def upperRow (j : Fin n) : Fin n → ℚ := fun i => if i = j then -1 else 0

/-- The row `xⱼ ≥ k + 1` encoding the right integer branch. -/
def lowerRow (j : Fin n) : Fin n → ℚ := fun i => if i = j then 1 else 0

@[simp]
theorem dot_upperRow (j : Fin n) (x : Fin n → ℚ) : dot (upperRow j) x = -x j := by
  simp [dot, upperRow]

@[simp]
theorem dot_lowerRow (j : Fin n) (x : Fin n → ℚ) : dot (lowerRow j) x = x j := by
  simp [dot, lowerRow]

end System

/-- A finite certificate tree. Leaves provide row multipliers; internal nodes split one integer.
The row count increases at each branch because the checker prepends that branch's inequality. -/
inductive BranchCertificate (n : ℕ) : ℕ → Type
  /-- A dual lower-bound leaf. -/
  | bound {m : ℕ} (weights : Fin m → ℚ) : BranchCertificate n m
  /-- An infeasible leaf. -/
  | infeasible {m : ℕ} (weights : Fin m → ℚ) : BranchCertificate n m
  /-- The exhaustive integer split `xⱼ ≤ k` or `xⱼ ≥ k + 1`. -/
  | split {m : ℕ} (j : Fin n) (k : ℤ)
      (left right : BranchCertificate n (m + 1)) : BranchCertificate n m

/-- Decidability of the finite dual-certificate conditions over rational numbers. -/
instance {n m : ℕ} (A : Fin m → Fin n → ℚ) (c : Fin n → ℚ) (w : Fin m → ℚ) :
    Decidable (IsDual A c w) :=
  inferInstanceAs (Decidable ((∀ i, 0 ≤ w i) ∧ ∀ j, ∑ i, w i * A i j = c j))

/-- Check a finite branch certificate with exact rational arithmetic. -/
def check {n m : ℕ} (P : System n m) (c : Fin n → ℚ) (v : ℚ) :
    BranchCertificate n m → Bool
  | .bound w => decide (IsDual P.coeff c w ∧ v ≤ ∑ i, w i * P.rhs i)
  | .infeasible w => decide (IsDual P.coeff 0 w ∧ 0 < ∑ i, w i * P.rhs i)
  | .split j k left right =>
    check (P.prepend (System.upperRow j) (-(k : ℚ))) c v left &&
      check (P.prepend (System.lowerRow j) ((k : ℚ) + 1)) c v right

/-- An accepted branch tree bounds every integer assignment satisfying the original rows. -/
theorem check_sound {n m : ℕ} (P : System n m) (c : Fin n → ℚ) (v : ℚ)
    (cert : BranchCertificate n m) (hcheck : check P c v cert = true)
    (x : Fin n → ℤ) (hx : P.feasible fun j => (x j : ℚ)) :
    v ≤ dot c (fun j => (x j : ℚ)) := by
  induction cert with
  | bound w =>
    have h : IsDual P.coeff c w ∧ v ≤ ∑ i, w i * P.rhs i := by
      simpa [check] using hcheck
    exact h.2.trans (dual_lower_bound _ _ _ _ h.1 _ hx)
  | infeasible w =>
    have h : IsDual P.coeff 0 w ∧ 0 < ∑ i, w i * P.rhs i := by
      simpa [check] using hcheck
    exact False.elim (infeasible_of_certificate _ _ _ h.1 h.2 ⟨_, hx⟩)
  | split j k left right ihl ihr =>
    have h :
        check (P.prepend (System.upperRow j) (-(k : ℚ))) c v left = true ∧
        check (P.prepend (System.lowerRow j) ((k : ℚ) + 1)) c v right = true := by
      simpa [check, Bool.and_eq_true] using hcheck
    by_cases hleft : x j ≤ k
    · apply ihl _ h.1
      exact (System.feasible_prepend _ _ _ _).2 ⟨by
        simpa using (neg_le_neg (show (x j : ℚ) ≤ (k : ℚ) by exact_mod_cast hleft)), hx⟩
    · have hright : k + 1 ≤ x j := by omega
      apply ihr _ h.2
      exact (System.feasible_prepend _ _ _ _).2 ⟨by
        simpa using (show ((k : ℚ) + 1) ≤ (x j : ℚ) by exact_mod_cast hright), hx⟩

/-- A feasible integer candidate with the certified objective value is globally optimal. -/
theorem check_optimal {n m : ℕ} (P : System n m) (c : Fin n → ℚ) (v : ℚ)
    (cert : BranchCertificate n m) (hcheck : check P c v cert = true)
    (x₀ : Fin n → ℤ) (hx₀ : P.feasible fun j => (x₀ j : ℚ))
    (hvalue : dot c (fun j => (x₀ j : ℚ)) = v) :
    P.feasible (fun j => (x₀ j : ℚ)) ∧
      ∀ x : Fin n → ℤ, P.feasible (fun j => (x j : ℚ)) →
        dot c (fun j => (x₀ j : ℚ)) ≤ dot c (fun j => (x j : ℚ)) := by
  refine ⟨hx₀, fun x hx => ?_⟩
  rw [hvalue]
  exact check_sound P c v cert hcheck x hx

/-- Real feasibility of rational rows; this also supports problems with continuous variables. -/
def System.feasibleReal {n m : ℕ} (P : System n m) (x : Fin n → ℝ) : Prop :=
  Feasible (fun i j => (P.coeff i j : ℝ)) (fun i => (P.rhs i : ℝ)) x

@[simp]
theorem System.feasibleReal_prepend {n m : ℕ} (P : System n m)
    (a : Fin n → ℚ) (b : ℚ) (x : Fin n → ℝ) :
    (P.prepend a b).feasibleReal x ↔
      (b : ℝ) ≤ dot (fun j => (a j : ℝ)) x ∧ P.feasibleReal x := by
  simp [System.feasibleReal, Feasible, System.prepend, Fin.forall_fin_succ]

/-- Only variables on which the certificate branches must be integer-valued. Other variables
may be arbitrary real numbers, so the same tree also certifies mixed-integer programs. -/
def IntegralOnTree {n m : ℕ} (cert : BranchCertificate n m) (x : Fin n → ℝ) : Prop :=
  match cert with
  | .bound _ => True
  | .infeasible _ => True
  | .split j _ left right =>
    (∃ z : ℤ, x j = z) ∧ IntegralOnTree left x ∧ IntegralOnTree right x

/-- Accepted trees bound real feasible points provided every branched variable is integral. -/
theorem check_sound_real {n m : ℕ} (P : System n m) (c : Fin n → ℚ) (v : ℚ)
    (cert : BranchCertificate n m) (hcheck : check P c v cert = true)
    (x : Fin n → ℝ) (hx : P.feasibleReal x) (hi : IntegralOnTree cert x) :
    (v : ℝ) ≤ dot (fun j => (c j : ℝ)) x := by
  induction cert with
  | bound w =>
    have h : IsDual P.coeff c w ∧ v ≤ ∑ i, w i * P.rhs i := by
      simpa [check] using hcheck
    exact (Rat.cast_le.mpr h.2).trans (rational_dual_lower_bound_real _ _ _ _ h.1 x hx)
  | infeasible w =>
    have h : IsDual P.coeff 0 w ∧ 0 < ∑ i, w i * P.rhs i := by
      simpa [check] using hcheck
    have hb := rational_dual_lower_bound_real P.coeff P.rhs 0 w h.1 x hx
    have hp : (0 : ℝ) < ((∑ i, w i * P.rhs i : ℚ) : ℝ) := Rat.cast_pos.mpr h.2
    simp only [Pi.zero_apply, Rat.cast_zero, dot, zero_mul, Finset.sum_const_zero] at hb
    exact False.elim (not_lt_of_ge hb hp)
  | split j k left right ihl ihr =>
    have h :
        check (P.prepend (System.upperRow j) (-(k : ℚ))) c v left = true ∧
        check (P.prepend (System.lowerRow j) ((k : ℚ) + 1)) c v right = true := by
      simpa [check, Bool.and_eq_true] using hcheck
    obtain ⟨z, hz⟩ := hi.1
    by_cases hleft : z ≤ k
    · apply ihl _ h.1 _ hi.2.1
      apply (System.feasibleReal_prepend _ _ _ _).2
      refine ⟨?_, hx⟩
      have hzle : x j ≤ (k : ℝ) := by rw [hz]; exact_mod_cast hleft
      simpa [dot, System.upperRow, apply_ite] using neg_le_neg hzle
    · have hright : k + 1 ≤ z := by omega
      apply ihr _ h.2 _ hi.2.2
      apply (System.feasibleReal_prepend _ _ _ _).2
      refine ⟨?_, hx⟩
      have hzle : (k : ℝ) + 1 ≤ x j := by rw [hz]; exact_mod_cast hright
      simpa [dot, System.lowerRow, apply_ite] using hzle

/-- A mixed-integer candidate attaining the tree's bound is optimal over its stated domain. -/
theorem check_optimal_real {n m : ℕ} (P : System n m) (c : Fin n → ℚ) (v : ℚ)
    (cert : BranchCertificate n m) (hcheck : check P c v cert = true)
    (x₀ : Fin n → ℝ) (hx₀ : P.feasibleReal x₀) (hi₀ : IntegralOnTree cert x₀)
    (hvalue : dot (fun j => (c j : ℝ)) x₀ = v) :
    P.feasibleReal x₀ ∧ IntegralOnTree cert x₀ ∧
      ∀ x : Fin n → ℝ, P.feasibleReal x → IntegralOnTree cert x →
        dot (fun j => (c j : ℝ)) x₀ ≤ dot (fun j => (c j : ℝ)) x := by
  refine ⟨hx₀, hi₀, fun x hx hi => ?_⟩
  rw [hvalue]
  exact check_sound_real P c v cert hcheck x hx hi

end Giallar.Certificates
