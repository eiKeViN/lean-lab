/-
Copyright (c) 2026 Kevin Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Zhao
-/
module

public import Giallar.PhasePolynomial
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Matrix.Transvection

/-!
# CNOT synthesis of reversible Boolean linear maps

The Gaussian-elimination theorem in mathlib reduces invertible matrices to diagonal
matrices and transvections. Over `ZMod 2`, an invertible diagonal matrix is the identity,
and every nonidentity transvection is a CNOT. Consequently every reversible Boolean
linear map has a finite CNOT circuit. This is an existence theorem, not a complexity
claim about a particular executable Gaussian-elimination implementation.
-/

@[expose] public section

namespace Giallar.PhasePolynomial

open scoped BigOperators
open Matrix

variable {Q : Type*} [Fintype Q] [DecidableEq Q]

/-- A finite circuit containing only identity, CNOT, and sequential composition. -/
inductive LinearCircuit (Q : Type*)
  /-- The empty circuit. -/
  | nil
  /-- One well-formed CNOT. -/
  | cx (control target : Q) (distinct : control ≠ target)
  /-- Execute the first circuit followed by the second. -/
  | seq (first second : LinearCircuit Q)

namespace LinearCircuit

/-- The Boolean matrix denoted by a linear circuit. -/
def matrix : LinearCircuit Q → Matrix Q Q (ZMod 2)
  | .nil => 1
  | .cx c t _ => Matrix.transvection t c 1
  | .seq a b => b.matrix * a.matrix

/-- The reversible linear map denoted by a linear circuit. -/
def linear : LinearCircuit Q → (Bits Q ≃ₗ[ZMod 2] Bits Q)
  | .nil => LinearEquiv.refl _ _
  | .cx c t h => cnot c t h
  | .seq a b => a.linear.trans b.linear

/-- A transvection with coefficient one is precisely the bit operation of a CNOT. -/
theorem transvection_mulVec (c t : Q) (h : c ≠ t) (x : Bits Q) :
    Matrix.transvection t c (1 : ZMod 2) *ᵥ x = cnot c t h x := by
  change Matrix.transvection t c (1 : ZMod 2) *ᵥ x = cnotFun c t x
  funext j
  by_cases hj : j = t
  · subst j
    simp [Matrix.transvection, Matrix.add_mulVec, Matrix.single_mulVec_eq,
      cnotFun]
  · simp [Matrix.transvection, Matrix.add_mulVec, Matrix.single_mulVec_eq,
      cnotFun, hj]

/-- The generated matrix acts as the actual CNOT circuit on bit vectors. -/
theorem matrix_mulVec (c : LinearCircuit Q) (x : Bits Q) :
    c.matrix *ᵥ x = c.linear x := by
  induction c generalizing x with
  | nil => simp [matrix, linear]
  | cx control target h => exact transvection_mulVec control target h x
  | seq a b iha ihb =>
      simp only [matrix, linear, LinearEquiv.trans_apply, ← Matrix.mulVec_mulVec]
      rw [iha, ihb]

/-- Expand a linear circuit to the source gate language. -/
def gates : LinearCircuit Q → List (Gate Q)
  | .nil => []
  | .cx c t h => [.cx c t h]
  | .seq a b => a.gates ++ b.gates

omit [Fintype Q] in
/-- Expanding the linear syntax into source gates preserves its bit permutation and zero phase. -/
theorem gates_correct (c : LinearCircuit Q) :
    execute c.gates Action.one = ⟨c.linear.toEquiv, fun _ => 0⟩ := by
  induction c with
  | nil => rfl
  | cx control target h =>
      simp [gates, execute, Action.one_comp, Gate.action, linear]
  | seq a b iha ihb =>
      rw [gates, execute_append, iha, ihb]
      apply Action.ext
      · rfl
      · funext x
        simp [Action.comp]

end LinearCircuit

/-- An explicit CNOT circuit computes the controls into the pivot. -/
def parityCircuit (p : Q) : Controls p → LinearCircuit Q
  | [] => .nil
  | c :: cs => .seq (.cx c.val p c.property) (parityCircuit p cs)

omit [Fintype Q] in
/-- The explicit circuit and the parity-network linear map agree. -/
theorem parityCircuit_linear (p : Q) (cs : Controls p) :
    (parityCircuit p cs).linear = parityNetwork p cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp [parityCircuit, LinearCircuit.linear, parityNetwork, ih]

omit [Fintype Q] [DecidableEq Q] in
/-- Each control contributes exactly one CNOT to the parity-computation circuit. -/
theorem parityCircuit_length (p : Q) (cs : Controls p) :
    (parityCircuit p cs).gates.length = cs.length := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp [parityCircuit, LinearCircuit.gates, ih]

/-- The syntactic inverse of a CNOT circuit uses the same number of gates. -/
def LinearCircuit.inverse : LinearCircuit Q → LinearCircuit Q
  | .nil => .nil
  | .cx c t h => .cx c t h
  | .seq a b => .seq b.inverse a.inverse

omit [Fintype Q] in
/-- Reversing the CNOT order inverts the exact reversible linear map. -/
theorem LinearCircuit.inverse_linear (c : LinearCircuit Q) :
    c.inverse.linear = c.linear.symm := by
  induction c with
  | nil => rfl
  | cx control target h => rfl
  | seq a b iha ihb => simp [LinearCircuit.inverse, LinearCircuit.linear, iha, ihb]

omit [Fintype Q] [DecidableEq Q] in
/-- Inversion preserves the number of CNOT gates. -/
theorem LinearCircuit.inverse_length (c : LinearCircuit Q) :
    c.inverse.gates.length = c.gates.length := by
  induction c with
  | nil => rfl
  | cx control target h => rfl
  | seq a b iha ihb =>
      simp [LinearCircuit.inverse, LinearCircuit.gates, iha, ihb, Nat.add_comm]

/-- A source-level compute/phase/uncompute circuit. -/
def gadgetGates (c : LinearCircuit Q) (p : Q) (θ : ℝ) : List (Gate Q) :=
  c.gates ++ [Gate.phase p θ] ++ c.inverse.gates

omit [Fintype Q] in
/-- The source gadget has exactly its specified compute/phase/uncompute semantics. -/
theorem gadgetGates_correct (c : LinearCircuit Q) (p : Q) (θ : ℝ) :
    execute (gadgetGates c p θ) Action.one = gadget c.linear p θ := by
  rw [gadgetGates, execute_append, execute_append, LinearCircuit.gates_correct,
    LinearCircuit.gates_correct, LinearCircuit.inverse_linear]
  simp [execute, gadget]

omit [Fintype Q] [DecidableEq Q] in
/-- A parity gadget uses twice as many CNOTs as controls and one phase gate. -/
theorem parity_gadget_length (p : Q) (cs : Controls p) (θ : ℝ) :
    (gadgetGates (parityCircuit p cs) p θ).length = 2 * cs.length + 1 := by
  simp [gadgetGates, LinearCircuit.inverse_length, parityCircuit_length]
  omega

omit [DecidableEq Q] in
/-- Distinct controls yield the usual bound of two CNOTs per nonpivot register wire. -/
theorem parity_gadget_length_le (p : Q) (cs : Controls p) (hcs : cs.Nodup) (θ : ℝ) :
    (gadgetGates (parityCircuit p cs) p θ).length ≤ 2 * (Fintype.card Q - 1) + 1 := by
  classical
  have hlen := hcs.length_le_card
  have hcard : Fintype.card {c : Q // c ≠ p} = Fintype.card Q - 1 := by
    simp
  rw [hcard] at hlen
  rw [parity_gadget_length]
  omega

/-- Every Boolean scalar is either zero or one. -/
theorem bit_eq_zero_or_one (b : ZMod 2) : b = 0 ∨ b = 1 := by
  have hv : b.val = 0 ∨ b.val = 1 := by have := b.val_lt; omega
  rcases hv with h | h
  · exact Or.inl ((ZMod.val_injective 2) (by simpa using h))
  · exact Or.inr ((ZMod.val_injective 2) h)

/-- Every invertible Boolean matrix has a finite CNOT circuit. -/
theorem exists_linearCircuit_matrix (M : Matrix Q Q (ZMod 2)) (hM : M.det ≠ 0) :
    ∃ c : LinearCircuit Q, c.matrix = M := by
  refine Matrix.diagonal_transvection_induction_of_det_ne_zero
    (fun M : Matrix Q Q (ZMod 2) => ∃ c : LinearCircuit Q, c.matrix = M) M hM ?_ ?_ ?_
  · intro d hd
    have hone : d = fun _ => (1 : ZMod 2) := by
      funext j
      have hne : d j ≠ 0 := by
        intro hz
        apply hd
        simp only [Matrix.det_diagonal]
        exact Finset.prod_eq_zero (Finset.mem_univ j) hz
      exact (bit_eq_zero_or_one (d j)).resolve_left hne
    refine ⟨.nil, ?_⟩
    simp [hone, LinearCircuit.matrix]
  · intro t
    rcases bit_eq_zero_or_one t.c with hc | hc
    · refine ⟨.nil, ?_⟩
      simp [Matrix.TransvectionStruct.toMatrix, hc, LinearCircuit.matrix]
    · refine ⟨.cx t.j t.i t.hij.symm, ?_⟩
      simp [Matrix.TransvectionStruct.toMatrix, hc, LinearCircuit.matrix]
  · intro A B _ _ hA hB
    rcases hA with ⟨a, rfl⟩
    rcases hB with ⟨b, rfl⟩
    exact ⟨.seq b a, rfl⟩

omit [Fintype Q] in
/-- Every reversible linear Boolean map is the exact action of a finite CNOT circuit. -/
theorem exists_linearCircuit [Finite Q] (A : Bits Q ≃ₗ[ZMod 2] Bits Q) :
    ∃ c : LinearCircuit Q, c.linear = A := by
  let := Fintype.ofFinite Q
  let M := LinearMap.toMatrix' A.toLinearMap
  let N := LinearMap.toMatrix' A.symm.toLinearMap
  have hinv : N * M = 1 := by
    rw [← LinearMap.toMatrix'_comp]
    have hcomp : A.symm.toLinearMap.comp A.toLinearMap = LinearMap.id := by
      ext x
      simp
    rw [hcomp, LinearMap.toMatrix'_id]
  have hdet : M.det ≠ 0 := by
    intro h
    have := congrArg Matrix.det hinv
    simp [Matrix.det_mul, h] at this
  rcases exists_linearCircuit_matrix M hdet with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  ext x j
  have hv := c.matrix_mulVec x
  rw [hc, LinearMap.toMatrix'_mulVec] at hv
  exact congrFun hv.symm j

/-- A Boolean linear form is the XOR sum of its values on standard basis vectors. -/
theorem parity_apply_sum (a : Parity Q) (x : Bits Q) :
    a x = ∑ j, x j * a (Pi.single j 1) := by
  conv_lhs => rw [pi_eq_sum_univ' x]
  simp

omit [Fintype Q] in
/-- Every nonzero Boolean linear form has a standard basis vector on which it is one. -/
theorem exists_parity_pivot [Finite Q] (a : Parity Q) (ha : a ≠ 0) :
    ∃ p, a (Pi.single p 1) = 1 := by
  let := Fintype.ofFinite Q
  by_contra h
  push Not at h
  have hz : ∀ j, a (Pi.single j 1) = 0 := by
    intro j
    exact (bit_eq_zero_or_one _).resolve_right (h j)
  apply ha
  apply LinearMap.ext
  intro x
  rw [parity_apply_sum]
  simp [hz]

omit [Fintype Q] [DecidableEq Q] in
/-- A nonzero parity can be computed into one pivot by a finite CNOT network. -/
theorem exists_parity_network [Finite Q] (a : Parity Q) (ha : a ≠ 0) :
    ∃ (p : Q) (A : Bits Q ≃ₗ[ZMod 2] Bits Q), ∀ x, A x p = a x := by
  let := Fintype.ofFinite Q
  classical
  obtain ⟨p, hp⟩ := exists_parity_pivot a ha
  let s := (Finset.univ.erase p).filter fun j => a (Pi.single j 1) = 1
  have hsp : ∀ j ∈ s, j ≠ p := by
    intro j hj
    exact (Finset.mem_erase.mp (Finset.mem_filter.mp hj).1).1
  let cs : Controls p := s.toList.attach.map fun j => ⟨j.val, hsp j.val (by simpa using j.property)⟩
  refine ⟨p, parityNetwork p cs, ?_⟩
  intro x
  rw [parityNetwork_apply_target]
  have hcs : (cs.map fun c => x c.val).sum = ∑ j ∈ s, x j := by
    simp [cs, List.map_map]
  rw [hcs, parity_apply_sum]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ p)]
  simp only [hp, mul_one]
  congr 1
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j _
  rcases bit_eq_zero_or_one (a (Pi.single j 1)) with h | h <;> simp [h]

omit [Fintype Q] in
/-- Every individual parity phase has a source circuit, with all work bits restored. -/
theorem exists_phase_gates [Finite Q] (a : Parity Q) (θ : ℝ) :
    ∃ l : List (Gate Q),
      execute l Action.one = ⟨Equiv.refl _, fun x => θ * bitValue (a x)⟩ := by
  let := Fintype.ofFinite Q
  classical
  by_cases ha : a = 0
  · refine ⟨[], ?_⟩
    subst a
    apply Action.ext
    · rfl
    · funext x
      simp [execute, Action.one]
  · obtain ⟨p, A, hA⟩ := exists_parity_network a ha
    obtain ⟨c, hc⟩ := exists_linearCircuit A
    obtain ⟨d, hd⟩ := exists_linearCircuit A.symm
    refine ⟨c.gates ++ [Gate.phase p θ] ++ d.gates, ?_⟩
    rw [execute_append, execute_append, LinearCircuit.gates_correct,
      LinearCircuit.gates_correct, hc, hd]
    simp only [execute, List.foldl_cons, List.foldl_nil, Action.one_comp]
    apply Action.ext
    · ext x
      simp [Action.comp, Gate.action]
    · funext x
      simp [Action.comp, Gate.action, hA]

omit [Fintype Q] in
/-- Every finite phase polynomial has a source circuit that leaves the bits unchanged. -/
theorem exists_terms_gates [Finite Q] (terms : Terms Q) :
    ∃ l : List (Gate Q),
      execute l Action.one = ⟨Equiv.refl _, phaseValue terms⟩ := by
  let := Fintype.ofFinite Q
  induction terms with
  | nil => exact ⟨[], rfl⟩
  | cons term terms ih =>
      rcases term with ⟨a, θ⟩
      obtain ⟨l, hl⟩ := exists_phase_gates a θ
      obtain ⟨r, hr⟩ := ih
      refine ⟨l ++ r, ?_⟩
      rw [execute_append, hl, hr]
      apply Action.ext
      · rfl
      · funext x
        rfl

omit [Fintype Q] in
/-- Every phase-polynomial representation can be resynthesized exactly in the source language. -/
theorem exists_representation_gates [Finite Q] (r : Representation Q) :
    ∃ l : List (Gate Q), execute l Action.one = r.action := by
  let := Fintype.ofFinite Q
  obtain ⟨l, hl⟩ := exists_terms_gates r.terms
  obtain ⟨c, hc⟩ := exists_linearCircuit r.linear
  refine ⟨l ++ c.gates, ?_⟩
  rw [execute_append, hl, LinearCircuit.gates_correct, hc]
  apply Action.ext
  · rfl
  · funext x
    simp [Action.comp, Representation.action]

/-- Choose a finite resynthesis using the proved Gaussian-elimination existence theorem. -/
noncomputable def synthesize (r : Representation Q) : List (Gate Q) :=
  Classical.choose (exists_representation_gates r)

/-- Resynthesis preserves the complete basis semantics. -/
theorem synthesize_correct (r : Representation Q) :
    execute (synthesize r) Action.one = r.action :=
  Classical.choose_spec (exists_representation_gates r)

/-- Extract, merge nonlocal parities, then resynthesize a source circuit. -/
noncomputable def optimize (l : List (Gate Q)) : List (Gate Q) :=
  synthesize (extract l).merge

/-- The whole extract/merge/resynthesize pipeline preserves phase-sensitive matrix semantics. -/
theorem optimize_correct (l : List (Gate Q)) :
    (execute (optimize l) Action.one).matrix = (execute l Action.one).matrix := by
  rw [optimize, synthesize_correct, Representation.merge_correct, extract_correct]

end Giallar.PhasePolynomial
