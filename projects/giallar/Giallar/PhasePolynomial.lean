/-
Copyright (c) 2026 Kevin Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Zhao
-/
module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Ring

/-!
# Phase-polynomial extraction

CNOT and phase gates act on bit vectors over `ZMod 2`. We retain the reversible linear
map and a finite list of linear parity forms with real coefficients. Extraction is
proved correct on every computational basis vector, and the basis semantics is
connected to complex matrices. The phase convention is `diag (1, exp (I * θ))`.

## Main declarations

* `cnot`: the reversible bit operation of a CNOT gate.
* `Representation`: a reversible linear map and a finite phase polynomial.
* `extract_correct`: extraction preserves the exact, phase-sensitive basis semantics.
* `Action.matrix_comp`: composition of basis actions agrees with matrix multiplication.
-/

@[expose] public section

namespace Giallar.PhasePolynomial

open scoped BigOperators

variable {Q : Type*} [Fintype Q] [DecidableEq Q]

/-- Bit vectors on a finite register. -/
abbrev Bits (Q : Type*) := Q → ZMod 2

/-- A parity is a linear Boolean-valued form on the input bits. -/
abbrev Parity (Q : Type*) := Bits Q →ₗ[ZMod 2] ZMod 2

/-- Interpret a bit as the real number zero or one. -/
def bitValue (b : ZMod 2) : ℝ := if b = 0 then 0 else 1

@[simp] theorem bitValue_zero : bitValue (0 : ZMod 2) = 0 := by simp [bitValue]

@[simp] theorem bitValue_one : bitValue (1 : ZMod 2) = 1 := by simp [bitValue]

/-- Add the control bit to the target bit. -/
def cnotFun (c t : Q) (x : Bits Q) : Bits Q := Function.update x t (x t + x c)

omit [Fintype Q] in
@[simp] theorem cnotFun_apply_target (c t : Q) (x : Bits Q) :
    cnotFun c t x t = x t + x c := by simp [cnotFun]

omit [Fintype Q] in
@[simp] theorem cnotFun_apply_ne (c t j : Q) (x : Bits Q) (h : j ≠ t) :
    cnotFun c t x j = x j := by simp [cnotFun, h]

omit [Fintype Q] in
theorem cnotFun_involutive (c t : Q) (h : c ≠ t) :
    Function.Involutive (cnotFun c t) := by
  intro x
  funext j
  by_cases hj : j = t
  · subst j
    simp [cnotFun, h, add_assoc, ZModModule.add_self]
  · simp [cnotFun, hj]

/-- CNOT as a linear automorphism, with distinct control and target. -/
def cnot (c t : Q) (h : c ≠ t) : Bits Q ≃ₗ[ZMod 2] Bits Q where
  toFun := cnotFun c t
  invFun := cnotFun c t
  left_inv := cnotFun_involutive c t h
  right_inv := cnotFun_involutive c t h
  map_add' x y := by
    funext j
    by_cases hj : j = t
    · subst j
      simp [cnotFun]
      ring
    · simp [cnotFun, hj]
  map_smul' a x := by
    funext j
    by_cases hj : j = t
    · subst j
      simp [cnotFun, mul_add]
    · simp [cnotFun, hj]

omit [Fintype Q] in
@[simp] theorem cnot_apply (c t : Q) (h : c ≠ t) (x : Bits Q) :
    cnot c t h x = cnotFun c t x := rfl

/-- A reversible operation, including its real-valued phase on each basis vector. -/
structure Action (Q : Type*) where
  /-- The reversible transformation of the bit string. -/
  perm : Equiv.Perm (Bits Q)
  /-- The phase angle before applying the bit permutation. -/
  phase : Bits Q → ℝ

namespace Action

/-- The identity basis action. -/
def one : Action Q := ⟨Equiv.refl _, fun _ => 0⟩

/-- Execute `a`, then `b`; the second phase sees the intermediate bit string. -/
def comp (a b : Action Q) : Action Q :=
  ⟨a.perm.trans b.perm, fun x => a.phase x + b.phase (a.perm x)⟩

omit [Fintype Q] [DecidableEq Q] in
@[ext] theorem ext {a b : Action Q} (hp : a.perm = b.perm) (hf : a.phase = b.phase) :
    a = b := by cases a; cases b; simp_all

omit [Fintype Q] [DecidableEq Q] in
@[simp] theorem one_comp (a : Action Q) : one.comp a = a := by ext <;> simp [comp, one]

omit [Fintype Q] [DecidableEq Q] in
@[simp] theorem comp_one (a : Action Q) : a.comp one = a := by ext <;> simp [comp, one]

omit [Fintype Q] [DecidableEq Q] in
theorem comp_assoc (a b c : Action Q) : (a.comp b).comp c = a.comp (b.comp c) := by
  ext <;> simp [comp, add_assoc]

/-- The complex matrix of a basis action, using column vectors. -/
noncomputable def matrix (a : Action Q) : Matrix (Bits Q) (Bits Q) ℂ :=
  fun y x => if y = a.perm x then Complex.exp (Complex.I * (a.phase x : ℂ)) else 0

/-- Matrix interpretation preserves chronological composition. -/
theorem matrix_comp (a b : Action Q) : (a.comp b).matrix = b.matrix * a.matrix := by
  classical
  ext y x
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single (a.perm x)]
  · simp only [matrix, comp, Equiv.trans_apply, ite_true]
    by_cases h : y = b.perm (a.perm x)
    · simp [h, Complex.ofReal_add, mul_add, Complex.exp_add, mul_comm]
    · simp [h]
  · intro z _ hz
    simp [matrix, hz]
  · simp

omit [DecidableEq Q] in
@[simp] theorem matrix_one : (one : Action Q).matrix = 1 := by
  classical
  ext y x
  simp [matrix, one, Matrix.one_apply]

/-- Reverse the bit permutation and negate the phase seen before reversing. -/
def inverse (a : Action Q) : Action Q :=
  ⟨a.perm.symm, fun x => -a.phase (a.perm.symm x)⟩

omit [Fintype Q] [DecidableEq Q] in
/-- Reversing a basis action and then performing it cancels exactly. -/
theorem inverse_comp (a : Action Q) : a.inverse.comp a = one := by
  apply Action.ext
  · ext x
    simp [inverse, comp, one]
  · funext x
    simp [inverse, comp, one]

omit [DecidableEq Q] in
/-- Reversing a basis action gives the conjugate-transpose complex matrix. -/
theorem matrix_inverse (a : Action Q) : a.inverse.matrix = a.matrix.conjTranspose := by
  classical
  ext y x
  simp only [matrix, inverse, Matrix.conjTranspose_apply]
  by_cases h : y = a.perm.symm x
  · subst y
    simp only [Equiv.apply_symm_apply, ite_true, Complex.star_def, ← Complex.exp_conj,
      Complex.ofReal_neg, map_mul, Complex.conj_I, Complex.conj_ofReal]
    congr 1
    ring
  · have hxy : x ≠ a.perm y := by
      intro hx
      apply h
      simp [hx]
    simp [h, hxy]

/-- Every represented basis action is a genuine unitary complex matrix. -/
theorem matrix_mem_unitaryGroup (a : Action Q) :
    a.matrix ∈ Matrix.unitaryGroup (Bits Q) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  have h := matrix_comp a.inverse a
  rw [inverse_comp, matrix_one, matrix_inverse] at h
  exact h.symm

end Action

/-- The source language contains CNOT and arbitrary real phase rotations. -/
inductive Gate (Q : Type*)
  /-- A well-formed CNOT. -/
  | cx (control target : Q) (distinct : control ≠ target)
  /-- Multiply the basis amplitude by `exp (I * angle)` when this bit is one. -/
  | phase (target : Q) (angle : ℝ)

/-- The exact basis action of a source gate. -/
def Gate.action : Gate Q → Action Q
  | .cx c t h => ⟨(cnot c t h).toEquiv, fun _ => 0⟩
  | .phase j θ => ⟨Equiv.refl _, fun x => θ * bitValue (x j)⟩

/-- A finite sum of real coefficients times input parities. -/
abbrev Terms (Q : Type*) := List (Parity Q × ℝ)

/-- Evaluate a phase polynomial as a real angle. -/
def phaseValue (terms : Terms Q) (x : Bits Q) : ℝ :=
  (terms.map fun term => term.2 * bitValue (term.1 x)).sum

omit [Fintype Q] [DecidableEq Q] in
@[simp] theorem phaseValue_nil (x : Bits Q) : phaseValue [] x = 0 := rfl

omit [Fintype Q] [DecidableEq Q] in
@[simp] theorem phaseValue_cons (a : Parity Q) (θ : ℝ) (l : Terms Q) (x : Bits Q) :
    phaseValue ((a, θ) :: l) x = θ * bitValue (a x) + phaseValue l x := rfl

omit [Fintype Q] [DecidableEq Q] in
theorem phaseValue_append (l r : Terms Q) (x : Bits Q) :
    phaseValue (l ++ r) x = phaseValue l x + phaseValue r x := by
  simp [phaseValue, List.map_append, List.sum_append]

/-- A reversible linear output map and an input phase polynomial. -/
structure Representation (Q : Type*) where
  /-- The linear reversible output transformation. -/
  linear : Bits Q ≃ₗ[ZMod 2] Bits Q
  /-- The phase polynomial in the original input bits. -/
  terms : Terms Q

/-- The empty circuit representation. -/
def Representation.one : Representation Q := ⟨LinearEquiv.refl _ _, []⟩

/-- The basis interpretation of a phase representation. -/
def Representation.action (r : Representation Q) : Action Q :=
  ⟨r.linear.toEquiv, phaseValue r.terms⟩

/-- Read one gate, updating the linear map or adding its current output parity. -/
def Representation.step (r : Representation Q) : Gate Q → Representation Q
  | .cx c t h => ⟨r.linear.trans (cnot c t h), r.terms⟩
  | .phase j θ =>
      ⟨r.linear, r.terms ++ [(LinearMap.proj j ∘ₗ r.linear.toLinearMap, θ)]⟩

omit [Fintype Q] in
theorem Representation.step_correct (r : Representation Q) (g : Gate Q) :
    (r.step g).action = r.action.comp g.action := by
  cases g with
  | cx c t h => ext <;> simp [Representation.step, Representation.action, Gate.action,
      Action.comp]
  | phase j θ =>
      apply Action.ext
      · rfl
      · funext x
        simp [Representation.step, Representation.action, Gate.action, Action.comp,
          phaseValue]

/-- Exact chronological semantics of a source circuit, starting from a basis action. -/
def execute (l : List (Gate Q)) (a : Action Q) : Action Q :=
  l.foldl (fun a g => a.comp g.action) a

omit [Fintype Q] in
/-- Running a circuit after an existing action composes it with its standalone meaning. -/
theorem execute_eq_comp (l : List (Gate Q)) (a : Action Q) :
    execute l a = a.comp (execute l Action.one) := by
  induction l generalizing a with
  | nil => simp [execute]
  | cons g l ih =>
      change execute l (a.comp g.action) =
        a.comp (execute l (Action.one.comp g.action))
      rw [Action.one_comp, ih, ih g.action, Action.comp_assoc]

omit [Fintype Q] in
/-- Circuit concatenation agrees with chronological composition. -/
theorem execute_append (l r : List (Gate Q)) :
    execute (l ++ r) Action.one = (execute l Action.one).comp (execute r Action.one) := by
  rw [execute, List.foldl_append]
  exact execute_eq_comp r (execute l Action.one)

/-- Extract the representation of a source circuit. -/
def extract (l : List (Gate Q)) : Representation Q :=
  l.foldl Representation.step Representation.one

omit [Fintype Q] in
/-- Extraction from any intermediate representation preserves its full basis action. -/
theorem extract_from_correct (l : List (Gate Q)) (r : Representation Q) :
    (l.foldl Representation.step r).action = execute l r.action := by
  induction l generalizing r with
  | nil => rfl
  | cons g l ih =>
      simpa [List.foldl_cons, execute, Representation.step_correct] using ih (r.step g)

omit [Fintype Q] in
/-- Extraction of CNOT and phase gates is exact on every computational basis vector. -/
theorem extract_correct (l : List (Gate Q)) :
    (extract l).action = execute l Action.one := by
  have h : (Representation.one : Representation Q).action = Action.one := by
    apply Action.ext
    · rfl
    · funext x
      rfl
  simpa [extract, h] using extract_from_correct l (Representation.one : Representation Q)

/-- Extraction is also exact under complex matrix semantics. -/
theorem extract_matrix_correct (l : List (Gate Q)) :
    (extract l).action.matrix = (execute l Action.one).matrix := by
  rw [extract_correct]

omit [Fintype Q] [DecidableEq Q] in
/-- Two adjacent occurrences of the same parity may be merged exactly. -/
theorem phaseValue_merge (a : Parity Q) (θ η : ℝ) (l : Terms Q) (x : Bits Q) :
    phaseValue ((a, θ) :: (a, η) :: l) x =
      phaseValue ((a, θ + η) :: l) x := by
  simp only [phaseValue_cons]
  ring

omit [Fintype Q] [DecidableEq Q] in
/-- Equal multisets of terms have equal phase functions, so merging may be nonlocal. -/
theorem phaseValue_perm {l r : Terms Q} (h : l.Perm r) (x : Bits Q) :
    phaseValue l x = phaseValue r x := by
  exact (h.map _).sum_eq

omit [Fintype Q] [DecidableEq Q] in
/-- A zero phase term may be removed. -/
@[simp] theorem phaseValue_zero_cons (a : Parity Q) (l : Terms Q) (x : Bits Q) :
    phaseValue ((a, 0) :: l) x = phaseValue l x := by simp

/-- Insert one term, combining it with the first matching parity if present. -/
noncomputable def insertTerm (a : Parity Q) (θ : ℝ) : Terms Q → Terms Q
  | [] => [(a, θ)]
  | (b, η) :: l => @ite _ (a = b) (Classical.propDecidable _)
      ((a, θ + η) :: l) ((b, η) :: insertTerm a θ l)

omit [Fintype Q] [DecidableEq Q] in
/-- Combining matching parity coefficients preserves the exact phase angle. -/
theorem phaseValue_insertTerm (a : Parity Q) (θ : ℝ) (l : Terms Q) (x : Bits Q) :
    phaseValue (insertTerm a θ l) x = θ * bitValue (a x) + phaseValue l x := by
  classical
  induction l with
  | nil => simp [insertTerm]
  | cons term l ih =>
      rcases term with ⟨b, η⟩
      by_cases h : a = b
      · subst b
        simp only [insertTerm, ↓reduceIte, phaseValue_cons]
        ring
      · simp only [insertTerm, h, ↓reduceIte, phaseValue_cons, ih]
        ring

/-- Merge repeated parities throughout the finite phase polynomial. -/
noncomputable def mergeTerms : Terms Q → Terms Q
  | [] => []
  | (a, θ) :: l => insertTerm a θ (mergeTerms l)

omit [Fintype Q] [DecidableEq Q] in
/-- The nonlocal merging algorithm preserves the phase on every input. -/
theorem phaseValue_mergeTerms (l : Terms Q) (x : Bits Q) :
    phaseValue (mergeTerms l) x = phaseValue l x := by
  induction l with
  | nil => rfl
  | cons term l ih =>
      rcases term with ⟨a, θ⟩
      simp [mergeTerms, phaseValue_insertTerm, ih]

/-- Merge repeated parities in a complete representation. -/
noncomputable def Representation.merge (r : Representation Q) : Representation Q :=
  ⟨r.linear, mergeTerms r.terms⟩

omit [Fintype Q] [DecidableEq Q] in
/-- The actual nonlocal merge pass preserves the full phase-sensitive semantics. -/
theorem Representation.merge_correct (r : Representation Q) : r.merge.action = r.action := by
  apply Action.ext
  · rfl
  · funext x
    exact phaseValue_mergeTerms r.terms x

/-- The complex phase factor of an input phase polynomial. -/
noncomputable def phaseFactor (l : Terms Q) (x : Bits Q) : ℂ :=
  Complex.exp (Complex.I * (phaseValue l x : ℂ))

omit [Fintype Q] [DecidableEq Q] in
@[simp] theorem phaseFactor_nil (x : Bits Q) : phaseFactor [] x = 1 := by
  simp [phaseFactor]

omit [Fintype Q] [DecidableEq Q] in
/-- Phase factors multiply when terms are concatenated. -/
theorem phaseFactor_append (l r : Terms Q) (x : Bits Q) :
    phaseFactor (l ++ r) x = phaseFactor l x * phaseFactor r x := by
  simp [phaseFactor, phaseValue_append, Complex.ofReal_add, mul_add, Complex.exp_add]

omit [Fintype Q] [DecidableEq Q] in
/-- A phase coefficient may be shifted by an integral multiple of `2π`. -/
theorem phaseFactor_period (a : Parity Q) (θ : ℝ) (k : ℤ) (l : Terms Q)
    (x : Bits Q) :
    phaseFactor ((a, θ + 2 * Real.pi * k) :: l) x =
      phaseFactor ((a, θ) :: l) x := by
  apply Complex.exp_eq_exp_iff_exists_int.mpr
  by_cases h : a x = 0
  · refine ⟨0, ?_⟩
    simp [phaseValue, bitValue, h]
  · refine ⟨k, ?_⟩
    simp only [phaseValue_cons, bitValue, h, ite_false, mul_one, Complex.ofReal_add,
      Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_intCast]
    ring

omit [DecidableEq Q] in
/-- Periodic normalization preserves the complex matrix, including every relative phase. -/
theorem matrix_period (A : Bits Q ≃ₗ[ZMod 2] Bits Q) (a : Parity Q)
    (θ : ℝ) (k : ℤ) (l : Terms Q) :
    (Representation.action ⟨A, (a, θ + 2 * Real.pi * k) :: l⟩).matrix =
      (Representation.action ⟨A, (a, θ) :: l⟩).matrix := by
  classical
  ext y x
  simp only [Action.matrix, Representation.action]
  exact congrArg (fun z : ℂ => if y = A.toEquiv x then z else 0)
    (phaseFactor_period a θ k l x)

/-- Shift every phase coefficient by an independently chosen integral multiple of `2π`. -/
noncomputable def shiftTerms (k : Parity Q → ℤ) (l : Terms Q) : Terms Q :=
  l.map fun term => (term.1, term.2 + 2 * Real.pi * k term.1)

omit [Fintype Q] [DecidableEq Q] in
/-- Simultaneous periodic normalization preserves every basis amplitude. -/
theorem phaseFactor_shiftTerms (k : Parity Q → ℤ) (l : Terms Q) (x : Bits Q) :
    phaseFactor (shiftTerms k l) x = phaseFactor l x := by
  induction l with
  | nil => rfl
  | cons term l ih =>
      rcases term with ⟨a, θ⟩
      change phaseFactor ((a, θ + 2 * Real.pi * k a) :: shiftTerms k l) x = _
      rw [phaseFactor_period]
      change phaseFactor ([(a, θ)] ++ shiftTerms k l) x =
        phaseFactor ([(a, θ)] ++ l) x
      rw [phaseFactor_append, phaseFactor_append, ih]

omit [DecidableEq Q] in
/-- Simultaneous periodic coefficient normalization preserves the exact complex matrix. -/
theorem matrix_shiftTerms (r : Representation Q) (k : Parity Q → ℤ) :
    (Representation.action ⟨r.linear, shiftTerms k r.terms⟩).matrix = r.action.matrix := by
  classical
  ext y x
  exact congrArg (fun z : ℂ => if y = r.linear.toEquiv x then z else 0)
    (phaseFactor_shiftTerms k r.terms x)

/-- Compute any reversible linear transformation, apply one phase, and uncompute it. -/
def gadget (A : Bits Q ≃ₗ[ZMod 2] Bits Q) (j : Q) (θ : ℝ) : Action Q :=
  (Action.comp ⟨A.toEquiv, fun _ => 0⟩ (Gate.action (.phase j θ))).comp
    ⟨A.symm.toEquiv, fun _ => 0⟩

omit [Fintype Q] in
/-- The compute/phase/uncompute gadget restores the bits and phases their computed parity. -/
theorem gadget_correct (A : Bits Q ≃ₗ[ZMod 2] Bits Q) (j : Q) (θ : ℝ) :
    gadget A j θ =
      (Representation.action
        ⟨LinearEquiv.refl _ _, [(LinearMap.proj j ∘ₗ A.toLinearMap, θ)]⟩) := by
  apply Action.ext
  · ext x
    simp [gadget, Action.comp, Gate.action, Representation.action]
  · funext x
    simp [gadget, Action.comp, Gate.action, Representation.action, phaseValue]

/-- Controls used to accumulate a parity into a distinct pivot wire. -/
abbrev Controls (p : Q) := List {c : Q // c ≠ p}

/-- Compute the XOR of the chosen controls into the pivot, using actual CNOT gates. -/
def parityNetwork (p : Q) : Controls p → (Bits Q ≃ₗ[ZMod 2] Bits Q)
  | [] => LinearEquiv.refl _ _
  | c :: cs => (cnot c.val p c.property).trans (parityNetwork p cs)

omit [Fintype Q] in
/-- The parity-computation network changes no wire other than the pivot. -/
theorem parityNetwork_apply_ne (p : Q) (cs : Controls p) (x : Bits Q)
    (j : Q) (hj : j ≠ p) : parityNetwork p cs x j = x j := by
  induction cs generalizing x with
  | nil => rfl
  | cons c cs ih =>
      simp only [parityNetwork, LinearEquiv.trans_apply]
      rw [ih]
      exact cnotFun_apply_ne c.val p j x hj

omit [Fintype Q] in
/-- The network computes the stated finite parity, with no assumed synthesis oracle. -/
theorem parityNetwork_apply_target (p : Q) (cs : Controls p) (x : Bits Q) :
    parityNetwork p cs x p = x p + (cs.map fun c => x c.val).sum := by
  induction cs generalizing x with
  | nil => simp [parityNetwork]
  | cons c cs ih =>
      simp only [parityNetwork, LinearEquiv.trans_apply]
      rw [ih]
      have hs : (cs.map fun d => cnot c.val p c.property x d.val).sum =
          (cs.map fun d => x d.val).sum := by
        congr 1
        apply List.map_congr_left
        intro d _
        exact cnotFun_apply_ne c.val p d.val x d.property
      rw [hs]
      change cnotFun c.val p x p + _ = _
      rw [cnotFun_apply_target]
      simp only [List.map_cons, List.sum_cons, add_assoc]

omit [Fintype Q] in
/-- A concrete CNOT gadget implements the chosen XOR phase and restores every bit. -/
theorem parity_gadget_correct (p : Q) (cs : Controls p) (θ : ℝ) :
    gadget (parityNetwork p cs) p θ =
      ⟨Equiv.refl _, fun x => θ * bitValue (x p + (cs.map fun c => x c.val).sum)⟩ := by
  rw [gadget_correct]
  apply Action.ext
  · rfl
  · funext x
    simp [Representation.action, phaseValue, parityNetwork_apply_target]

end Giallar.PhasePolynomial
