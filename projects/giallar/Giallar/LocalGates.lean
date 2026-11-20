/-
Copyright (c) 2026 Kevin Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Zhao
-/
module

public import Giallar.Routing

/-!
# Local quantum gates and physical wire layouts

A local gate is a matrix indexed by bit strings on a finite ordered set of local wires.
`embeddedGate` inserts that matrix on an injection of local wires into global wires: its
basis entries use the local gate entry when the untouched coordinates agree, and zero
otherwise. This definition does not use layout conjugation.

## Main results

* `embeddedGate_relabel`: conjugation by the concrete layout matrix relabels local wires.
* `oneQubitGate_relabel`: the corresponding one-qubit gate equation.
* `twoQubitGate_relabel`: the corresponding ordered two-qubit gate equation.
-/

@[expose] public section

namespace Giallar.Routing

open Equiv

variable {W L : Type*}

/-- Transport an ordered injection of local wires along a physical layout. -/
def relabelWires (p : Perm W) (w : L ↪ W) : L ↪ W where
  toFun j := p (w j)
  inj' := p.injective.comp w.injective

@[simp]
theorem relabelWires_apply (p : Perm W) (w : L ↪ W) (j : L) :
    relabelWires p w j = p (w j) := rfl

/-- Equality of every global bit outside the image of the local-wire injection. -/
def AgreeOutside (w : L ↪ W) (x y : W → Bool) : Prop :=
  ∀ i, (∀ j, w j ≠ i) → x i = y i

/-- Insert a local quantum matrix at the indicated ordered distinct global wires.
The spectator bits are compared in the computational basis, giving their identity action. -/
noncomputable def embeddedGate (w : L ↪ W) (U : Matrix (L → Bool) (L → Bool) ℂ) :
    Matrix (W → Bool) (W → Bool) ℂ := by
  classical
  exact fun x y => if AgreeOutside w x y then U (x ∘ w) (y ∘ w) else 0

variable [Fintype W] [DecidableEq W]

/-- Coordinate form of layout conjugation for any global matrix. -/
theorem wireMatrix_conjugation (p : Perm W)
    (A : Matrix (W → Bool) (W → Bool) ℂ) :
    wireMatrix p * A * wireMatrix p⁻¹ =
      A.submatrix (wireBits p).symm (wireBits p).symm := by
  change ((wireBits p)⁻¹).toPEquiv.toMatrix * A *
      ((wireBits p⁻¹)⁻¹).toPEquiv.toMatrix = _
  rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  ext x y
  simp

omit [Fintype W] [DecidableEq W] in
/-- Agreement of untouched bits is invariant under simultaneous relabeling. -/
theorem agreeOutside_relabel (p : Perm W) (w : L ↪ W) (x y : W → Bool) :
    AgreeOutside w ((wireBits p).symm x) ((wireBits p).symm y) ↔
      AgreeOutside (relabelWires p w) x y := by
  constructor
  · intro h i hi
    have hout : ∀ j, w j ≠ p.symm i := by
      intro j hj
      apply hi j
      simp [hj]
    simpa [wireBits] using h (p.symm i) hout
  · intro h i hi
    have hout : ∀ j, relabelWires p w j ≠ p i := by
      intro j hj
      exact hi j (p.injective hj)
    exact h (p i) hout

/-- Concrete local-gate embedding commutes with layout transport. -/
theorem embeddedGate_relabel (p : Perm W) (w : L ↪ W)
    (U : Matrix (L → Bool) (L → Bool) ℂ) :
    wireMatrix p * embeddedGate w U * wireMatrix p⁻¹ =
      embeddedGate (relabelWires p w) U := by
  classical
  rw [wireMatrix_conjugation]
  ext x y
  simp only [Matrix.submatrix_apply, embeddedGate, agreeOutside_relabel]
  congr 2

/-- Ordered injection selecting one global wire. -/
def oneWire (a : W) : Fin 1 ↪ W where
  toFun := fun _ => a
  inj' := fun i j _ => Subsingleton.elim i j

/-- A one-qubit matrix embedded at a named global wire. -/
noncomputable def oneQubitGate (a : W) (U : Matrix (Fin 1 → Bool) (Fin 1 → Bool) ℂ) :
    Matrix (W → Bool) (W → Bool) ℂ :=
  embeddedGate (oneWire a) U

/-- The one-qubit embedding follows the physical layout. -/
theorem oneQubitGate_relabel (p : Perm W) (a : W)
    (U : Matrix (Fin 1 → Bool) (Fin 1 → Bool) ℂ) :
    wireMatrix p * oneQubitGate a U * wireMatrix p⁻¹ = oneQubitGate (p a) U := by
  have hw : relabelWires p (oneWire a) = oneWire (p a) := by ext i; rfl
  simpa only [oneQubitGate, hw] using embeddedGate_relabel p (oneWire a) U

/-- Ordered injection selecting two distinct global wires. -/
def twoWires (a b : W) (hab : a ≠ b) : Fin 2 ↪ W where
  toFun i := if i = 0 then a else b
  inj' := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all

/-- A two-qubit matrix embedded at an ordered pair of distinct global wires. -/
noncomputable def twoQubitGate (a b : W) (hab : a ≠ b)
    (U : Matrix (Fin 2 → Bool) (Fin 2 → Bool) ℂ) :
    Matrix (W → Bool) (W → Bool) ℂ :=
  embeddedGate (twoWires a b hab) U

/-- The ordered two-qubit embedding follows the layout on both wires. -/
theorem twoQubitGate_relabel (p : Perm W) (a b : W) (hab : a ≠ b)
    (U : Matrix (Fin 2 → Bool) (Fin 2 → Bool) ℂ) :
    wireMatrix p * twoQubitGate a b hab U * wireMatrix p⁻¹ =
      twoQubitGate (p a) (p b) (p.injective.ne hab) U := by
  have hw : relabelWires p (twoWires a b hab) =
      twoWires (p a) (p b) (p.injective.ne hab) := by
    ext i
    fin_cases i <;> simp [relabelWires, twoWires]
  simpa only [twoQubitGate, hw] using embeddedGate_relabel p (twoWires a b hab) U

end Giallar.Routing
