module
public import Mathlib

public section

/-! Semantic home: ForMathlib.Combinatorics.DirectedPaths.PositiveTransfer. Source spans: Comparison:2.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

namespace KLInvariance.Comparison
open Polynomial
section Schedule

variable {V : Type*}

@[expose] noncomputable local instance _root_.OAI.KLInvariance.Comparison.instDecidableEq_oAI : DecidableEq V := Classical.decEq V

/-- The genuine elementary transfer `id + T E_xy` from the source's edge
schedule, expressed on vectors rather than with a choice of enumeration. -/
@[expose] noncomputable def transfer (T : ℝ) (x y : V) (v : V → ℝ) : V → ℝ :=
  fun z => v z + if z = x then T * v y else 0

theorem transfer_monotone (T : ℝ) (hT : 0 ≤ T) (x y : V) :
    Monotone (transfer T x y) := by
  intro v w hv z
  dsimp [transfer]
  split_ifs
  · exact add_le_add (hv z) (mul_le_mul_of_nonneg_left (hv y) hT)
  · simpa using hv z

theorem transfer_injective (T : ℝ) (x y : V) (hxy : x ≠ y) :
    Function.Injective (transfer T x y) := by
  intro v w h
  have hy := congrFun h y
  simp only [transfer, Ne.symm hxy, ite_false, add_zero] at hy
  funext z
  have hz := congrFun h z
  dsimp [transfer] at hz
  split_ifs at hz with hz'
  · rw [hy] at hz
    exact add_right_cancel hz
  · exact add_right_cancel hz

@[expose] noncomputable def idealState (T : ℝ) (edges : ℕ → V × V) (initial : V → ℝ) :
    ℕ → V → ℝ
  | 0 => initial
  | n + 1 => transfer T (edges n).1 (edges n).2 (idealState T edges initial n)

/-- Propagation of the actual Hilbert-series bound through all earlier edges.
No freeness or positivity of the *vectors* is needed for this part. -/
theorem state_le_ideal (T : ℝ) (hT : 0 ≤ T) (edges : ℕ → V × V)
    (D : ℕ → V → ℝ) (n : ℕ)
    (hstep : ∀ k < n, D (k + 1) ≤ transfer T (edges k).1 (edges k).2 (D k)) :
    D n ≤ idealState T edges (D 0) n := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    exact (hstep n (Nat.lt_succ_self n)).trans
      (transfer_monotone T hT _ _ (ih (fun k hk => hstep k (Nat.lt_succ_of_lt hk))))

/-- Endpoint equality forces every edge-image deficit to vanish, including
those invisible in codimension one. This uses actual inequalities and the
injectivity of elementary edge transfers; it does not assume image equality.
It is the no-deficit conclusion of source (6.8). -/
theorem every_step_eq_of_endpoint_eq (T : ℝ) (hT : 0 ≤ T)
    (edges : ℕ → V × V) (D : ℕ → V → ℝ) (n : ℕ)
    (hedges : ∀ k < n, (edges k).1 ≠ (edges k).2)
    (hstep : ∀ k < n, D (k + 1) ≤ transfer T (edges k).1 (edges k).2 (D k))
    (hend : D n = idealState T edges (D 0) n) :
    ∀ k < n, D (k + 1) = transfer T (edges k).1 (edges k).2 (D k) := by
  induction n with
  | zero => omega
  | succ n ih =>
    have hD : D n ≤ idealState T edges (D 0) n :=
      state_le_ideal T hT edges D n (fun k hk => hstep k (Nat.lt_succ_of_lt hk))
    have ht := transfer_monotone T hT (edges n).1 (edges n).2 hD
    have hlast : D (n + 1) = transfer T (edges n).1 (edges n).2 (D n) := by
      apply le_antisymm (hstep n (Nat.lt_succ_self n))
      exact ht.trans_eq hend.symm
    have heqn : D n = idealState T edges (D 0) n := by
      apply transfer_injective T (edges n).1 (edges n).2
        (hedges n (Nat.lt_succ_self n))
      exact hlast.symm.trans hend
    intro k hk
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
    · exact ih (fun j hj => hedges j (Nat.lt_succ_of_lt hj))
        (fun j hj => hstep j (Nat.lt_succ_of_lt hj)) heqn k hk
    · exact hlast

end Schedule
end KLInvariance.Comparison

end OAI
