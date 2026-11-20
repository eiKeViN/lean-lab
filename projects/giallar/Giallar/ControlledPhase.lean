/-
Copyright (c) 2026 Kevin Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Zhao
-/
module

public import Giallar.Approximation
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Controlled phase deletion and a QFT approximation budget

Controlled phase gates are actual diagonal complex matrices with their L2 operator norm.
Deleting a gate of angle `θ` incurs at most `|θ|` operator error, independently of the
number of unused qubits. The error theorem accepts arbitrary unchanged unitary gates
between controlled phases, so the same result applies to Hadamards and bit reversal.

## Main results

* `norm_controlled_sub_one_eq`: the exact scalar sine expression for controlled-phase error.
* `norm_controlled_sub_one_le`: deletion error is bounded by the absolute angle.
* `qft_truncation_error_suffix`: the complete truncation error is at most `2πn / 2^b`.
* `qft_distance_count`: exactly `n - r` phase gates have distance `r`.

The QFT theorem concerns compilation relative to the given source gate list. It does not
assert that this list is a discrete Fourier transform, and needs no such assumption.
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator BigOperators

namespace Giallar.ControlledPhase

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A phase of angle `θ` on exactly the basis states selected by `mask`. -/
def phase (mask : ι → Bool) (θ : ℝ) : Matrix ι ι ℂ :=
  Matrix.diagonal (fun x => if mask x then Complex.exp (Complex.I * θ) else 1)

/-- Every diagonal phase gate is a contraction for the L2 operator norm. -/
theorem norm_phase_le_one (mask : ι → Bool) (θ : ℝ) : ‖phase mask θ‖ ≤ 1 := by
  rw [phase, Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
  intro x
  cases h : mask x <;> simp [Complex.norm_exp_I_mul_ofReal]

/-- The operator error of deleting a diagonal phase gate is bounded by its angle. -/
theorem norm_phase_sub_one_le (mask : ι → Bool) (θ : ℝ) :
    ‖phase mask θ - 1‖ ≤ |θ| := by
  rw [phase, ← Matrix.diagonal_one, Matrix.diagonal_sub, Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg (abs_nonneg θ)).mpr
  intro x
  cases h : mask x
  · simp
  · simpa [h, Real.norm_eq_abs] using (Real.norm_exp_I_mul_ofReal_sub_one_le (x := θ))

/-- When the selector is nonempty, the diagonal norm is the exact scalar phase error. -/
theorem norm_phase_sub_one_eq (mask : ι → Bool) (θ : ℝ)
    (hm : ∃ x, mask x = true) :
    ‖phase mask θ - 1‖ = ‖Complex.exp (Complex.I * θ) - 1‖ := by
  rw [phase, ← Matrix.diagonal_one, Matrix.diagonal_sub, Matrix.l2_opNorm_diagonal]
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro x
    cases hx : mask x <;> simp
  · obtain ⟨x, hx⟩ := hm
    simpa [hx] using norm_le_pi_norm
      (fun x => (if mask x then Complex.exp (Complex.I * θ) else 1) - 1) x

/-- The concrete basis selector for a controlled phase on two qubit wires. -/
def controlMask {n : ℕ} (c t : Fin n) (x : Fin n → Bool) : Bool := x c && x t

/-- A controlled phase gate, extended by the identity on all other qubits. -/
def controlled {n : ℕ} (c t : Fin n) (θ : ℝ) :
    Matrix (Fin n → Bool) (Fin n → Bool) ℂ := phase (controlMask c t) θ

/-- Controlled phase deletion has a dimension-independent operator error bound. -/
theorem norm_controlled_sub_one_le {n : ℕ} (c t : Fin n) (θ : ℝ) :
    ‖controlled c t θ - 1‖ ≤ |θ| := norm_phase_sub_one_le _ _

/-- The exact controlled-phase deletion error is the familiar sine expression. -/
theorem norm_controlled_sub_one_eq {n : ℕ} (c t : Fin n) (θ : ℝ) :
    ‖controlled c t θ - 1‖ = 2 * |Real.sin (θ / 2)| := by
  rw [controlled, norm_phase_sub_one_eq _ _ ⟨fun _ => true, by simp [controlMask]⟩,
    Complex.norm_exp_I_mul_ofReal_sub_one]
  simp

/-- Source/target operators for retaining or deleting one controlled phase. -/
def replacement (mask : ι → Bool) (θ : ℝ) (delete : Bool) :
    Matrix ι ι ℂ × Matrix ι ι ℂ :=
  (phase mask θ, if delete then 1 else phase mask θ)

/-- Both sides of a phase replacement are contractions. -/
theorem replacement_contractions [Nonempty ι] (mask : ι → Bool) (θ : ℝ)
    (delete : Bool) :
    ‖(replacement mask θ delete).1‖ ≤ 1 ∧
      ‖(replacement mask θ delete).2‖ ≤ 1 := by
  constructor
  · exact norm_phase_le_one _ _
  · cases delete <;> simp [replacement, norm_phase_le_one]

/-- Only deleted gates contribute to the local approximation budget. -/
theorem replacement_error (mask : ι → Bool) (θ : ℝ) (delete : Bool) :
    ‖(replacement mask θ delete).1 - (replacement mask θ delete).2‖ ≤
      if delete then |θ| else 0 := by
  cases delete
  · simp [replacement]
  · exact norm_phase_sub_one_le _ _

/-- A finite tail of the geometric series with ratio one half is at most twice its first term. -/
theorem geometric_half_tail (b m : ℕ) :
    (∑ r ∈ Finset.range m, (1 / 2 : ℝ) ^ (b + r)) ≤ 2 / (2 : ℝ) ^ b := by
  have h : ∀ m : ℕ, (∑ r ∈ Finset.range m, (1 / 2 : ℝ) ^ r) ≤ 2 := by
    intro m
    have he := geom_sum_mul (1 / 2 : ℝ) m
    have hp : 0 ≤ (1 / 2 : ℝ) ^ m := pow_nonneg (by norm_num) _
    nlinarith
  calc
    _ = (1 / 2 : ℝ) ^ b * ∑ r ∈ Finset.range m, (1 / 2 : ℝ) ^ r := by
      simp_rw [pow_add]
      rw [Finset.mul_sum]
    _ ≤ (1 / 2 : ℝ) ^ b * 2 :=
      mul_le_mul_of_nonneg_left (h m) (pow_nonneg (by norm_num) _)
    _ = 2 / (2 : ℝ) ^ b := by rw [one_div_pow]; ring

/-- A row of discarded QFT rotations has a geometric error budget independent of row length. -/
theorem row_angle_budget (b m : ℕ) :
    (∑ k ∈ Finset.range m,
      if b ≤ k + 1 then Real.pi / (2 : ℝ) ^ (k + 1) else 0) ≤
        2 * Real.pi / (2 : ℝ) ^ b := by
  let s := (Finset.range m).filter (fun k => b ≤ k + 1)
  have hinj : Set.InjOn (fun k => k + 1 - b) (s : Set ℕ) := by
    intro a ha c hc he
    have hba := (Finset.mem_filter.mp ha).2
    have hbc := (Finset.mem_filter.mp hc).2
    change a + 1 - b = c + 1 - b at he
    omega
  have hsub : Finset.image (fun k => k + 1 - b) s ⊆ Finset.range (m + 1) := by
    intro r hr
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hr
    have hm := Finset.mem_range.mp (Finset.mem_filter.mp hk).1
    simp only [Finset.mem_range]
    omega
  have hsum := Finset.sum_le_sum_of_injOn
    (f := fun k => Real.pi / (2 : ℝ) ^ (k + 1))
    (g := fun r => Real.pi * (1 / 2 : ℝ) ^ (b + r))
    (fun k => k + 1 - b) hinj hsub (by
      intro k hk
      have hb := (Finset.mem_filter.mp hk).2
      have he : b + (k + 1 - b) = k + 1 := by omega
      rw [he, one_div_pow]
      exact le_of_eq (by ring)) (by
      intro r hr hnot
      positivity)
  calc
    _ = ∑ k ∈ s, Real.pi / (2 : ℝ) ^ (k + 1) := by
      simp [s, Finset.sum_filter]
    _ ≤ ∑ r ∈ Finset.range (m + 1), Real.pi * (1 / 2 : ℝ) ^ (b + r) := hsum
    _ = Real.pi * ∑ r ∈ Finset.range (m + 1), (1 / 2 : ℝ) ^ (b + r) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ Real.pi * (2 / (2 : ℝ) ^ b) :=
      mul_le_mul_of_nonneg_left (geometric_half_tail b (m + 1)) Real.pi_pos.le
    _ = _ := by ring

/-- One unchanged unitary followed by controlled phases of successive QFT distances. -/
def rowPairs [Nonempty ι] {m : ℕ} (H : unitary (Matrix ι ι ℂ))
    (masks : Fin m → ι → Bool) (b : ℕ) : List (Matrix ι ι ℂ × Matrix ι ι ℂ) :=
  ((H : Matrix ι ι ℂ), (H : Matrix ι ι ℂ)) ::
    List.ofFn (fun k : Fin m => replacement (masks k)
      (Real.pi / (2 : ℝ) ^ (k.val + 1)) (decide (b ≤ k.val + 1)))

/-- Every operation in a QFT row, on both sides of deletion, is a contraction. -/
theorem rowPairs_contractions [Nonempty ι] {m : ℕ} (H : unitary (Matrix ι ι ℂ))
    (masks : Fin m → ι → Bool) (b : ℕ) :
    ∀ p ∈ rowPairs H masks b, ‖p.1‖ ≤ 1 ∧ ‖p.2‖ ≤ 1 := by
  intro p hp
  simp only [rowPairs, List.mem_cons, List.mem_ofFn] at hp
  rcases hp with rfl | ⟨k, rfl⟩
  · simp
  · exact replacement_contractions _ _ _

/-- The local-error sum in a row is bounded by a finite geometric tail. -/
theorem rowPairs_error_sum [Nonempty ι] {m : ℕ} (H : unitary (Matrix ι ι ℂ))
    (masks : Fin m → ι → Bool) (b : ℕ) :
    ((rowPairs H masks b).map (fun p => ‖p.1 - p.2‖)).sum ≤
      2 * Real.pi / (2 : ℝ) ^ b := by
  simp only [rowPairs, List.map_cons, sub_self, norm_zero, List.sum_cons, zero_add,
    List.map_ofFn, List.sum_ofFn, Function.comp_def]
  calc
    _ ≤ ∑ k : Fin m,
        if b ≤ k.val + 1 then Real.pi / (2 : ℝ) ^ (k.val + 1) else 0 := by
      apply Finset.sum_le_sum
      intro k hk
      have hp : 0 ≤ Real.pi / (2 : ℝ) ^ (k.val + 1) := by positivity
      simpa [abs_of_nonneg hp] using
        replacement_error (masks k) (Real.pi / (2 : ℝ) ^ (k.val + 1))
          (decide (b ≤ k.val + 1))
    _ ≤ _ := by
      rw [Fin.sum_univ_eq_sum_range
        (fun k => if b ≤ k + 1 then Real.pi / (2 : ℝ) ^ (k + 1) else 0) m]
      exact row_angle_budget b m

/-- The controlled-phase selector at distance `k + 1` in QFT row `j`. -/
def qftMask {n : ℕ} (j : Fin n) (k : Fin (n - j.val - 1)) :
    (Fin n → Bool) → Bool :=
  controlMask ⟨j.val + k.val + 1, by have := k.isLt; omega⟩ j

/-- Source and truncated QFT gate lists, paired before chronological evaluation.

The unitary `H j` is unchanged by compilation. Choosing each `H j` to be the Hadamard
on wire `j` gives the usual QFT skeleton, before a common final bit reversal.
-/
def qftPairs (n b : ℕ)
    (H : Fin n → unitary (Matrix (Fin n → Bool) (Fin n → Bool) ℂ)) :
    List (Matrix (Fin n → Bool) (Fin n → Bool) ℂ ×
      Matrix (Fin n → Bool) (Fin n → Bool) ℂ) :=
  (List.ofFn (fun j : Fin n => rowPairs (H j) (qftMask j) b)).flatten

/-- All concrete operations in the source/truncated QFT pair are contractions. -/
theorem qftPairs_contractions (n b : ℕ)
    (H : Fin n → unitary (Matrix (Fin n → Bool) (Fin n → Bool) ℂ)) :
    ∀ p ∈ qftPairs n b H, ‖p.1‖ ≤ 1 ∧ ‖p.2‖ ≤ 1 := by
  intro p hp
  obtain ⟨row, hr, hp⟩ := List.mem_flatten.mp hp
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hr
  exact rowPairs_contractions (H j) (qftMask j) b p hp

/-- An `n`-row QFT truncation has total local-error budget at most `2πn / 2^b`. -/
theorem qftPairs_error_sum (n b : ℕ)
    (H : Fin n → unitary (Matrix (Fin n → Bool) (Fin n → Bool) ℂ)) :
    ((qftPairs n b H).map (fun p => ‖p.1 - p.2‖)).sum ≤
      2 * Real.pi * n / (2 : ℝ) ^ b := by
  simp only [qftPairs, List.map_flatten, List.sum_flatten, List.map_ofFn,
    List.sum_ofFn, Function.comp_def]
  calc
    _ ≤ ∑ _j : Fin n, 2 * Real.pi / (2 : ℝ) ^ b := by
      apply Finset.sum_le_sum
      intro j hj
      exact rowPairs_error_sum (H j) (qftMask j) b
    _ = _ := by simp; ring

/-- Concrete QFT gate deletion has the advertised dimension-dependent operator error bound. -/
theorem qft_truncation_error (n b : ℕ)
    (H : Fin n → unitary (Matrix (Fin n → Bool) (Fin n → Bool) ℂ)) :
    ‖Giallar.eval ((qftPairs n b H).map Prod.fst) -
      Giallar.eval ((qftPairs n b H).map Prod.snd)‖ ≤
        2 * Real.pi * n / (2 : ℝ) ^ b :=
  (Giallar.norm_eval_sub_le (qftPairs n b H) (qftPairs_contractions n b H)).trans
    (qftPairs_error_sum n b H)

/-- The paired source list has `n` unchanged gates and `n(n-1)/2` controlled phases. -/
theorem qftPairs_length (n b : ℕ)
    (H : Fin n → unitary (Matrix (Fin n → Bool) (Fin n → Bool) ℂ)) :
    (qftPairs n b H).length = n + n * (n - 1) / 2 := by
  have hs : (∑ j : Fin n, (n - (j : ℕ) - 1)) = n * (n - 1) / 2 := by
    rw [Fin.sum_univ_eq_sum_range (fun j => n - j - 1) n]
    calc
      _ = ∑ j ∈ Finset.range n, (n - 1 - j) := by
        apply Finset.sum_congr rfl
        intro j hj
        omega
      _ = ∑ j ∈ Finset.range n, j := Finset.sum_range_reflect (fun j => j) n
      _ = _ := Finset.sum_range_id n
  simp only [qftPairs, List.length_flatten, List.map_ofFn, List.sum_ofFn,
    Function.comp_def, rowPairs, List.length_cons, List.length_ofFn]
  rw [Finset.sum_add_distrib, hs]
  simp [Nat.add_comm]

/-- The same error guarantee holds after any common unitary suffix, including bit reversal. -/
theorem qft_truncation_error_suffix (n b : ℕ)
    (H : Fin n → unitary (Matrix (Fin n → Bool) (Fin n → Bool) ℂ))
    (suffix : List (unitary (Matrix (Fin n → Bool) (Fin n → Bool) ℂ))) :
    ‖Giallar.eval (((qftPairs n b H).map Prod.fst) ++ suffix.map Subtype.val) -
      Giallar.eval (((qftPairs n b H).map Prod.snd) ++ suffix.map Subtype.val)‖ ≤
        2 * Real.pi * n / (2 : ℝ) ^ b := by
  rw [Giallar.eval_append, Giallar.eval_append, ← mul_sub]
  calc
    _ ≤ ‖Giallar.eval (suffix.map Subtype.val)‖ *
        ‖Giallar.eval ((qftPairs n b H).map Prod.fst) -
          Giallar.eval ((qftPairs n b H).map Prod.snd)‖ := norm_mul_le _ _
    _ ≤ ‖Giallar.eval ((qftPairs n b H).map Prod.fst) -
          Giallar.eval ((qftPairs n b H).map Prod.snd)‖ := by
      apply mul_le_of_le_one_left (norm_nonneg _)
      apply Giallar.norm_eval_le_one
      intro a ha
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ha
      simp
    _ ≤ _ := qft_truncation_error n b H

/-- The controlled-phase distances in the chronological QFT skeleton. -/
def qftDistances (n : ℕ) : List ℕ :=
  (List.ofFn (fun j : Fin n => List.ofFn (fun k : Fin (n - j.val - 1) => k.val + 1))).flatten

/-- A single row contains exactly one phase at each distance from one to its length. -/
theorem row_distance_count (m r : ℕ) (hr : 1 ≤ r) :
    (List.ofFn (fun k : Fin m => k.val + 1)).count r = if r ≤ m then 1 else 0 := by
  have hn : (List.ofFn (fun k : Fin m => k.val + 1)).Nodup := by
    apply List.nodup_ofFn.mpr
    intro a b h
    apply Fin.ext
    change a.val + 1 = b.val + 1 at h
    omega
  rw [hn.count]
  congr 1
  simp only [List.mem_ofFn]
  apply propext
  constructor
  · rintro ⟨i, hi⟩
    have := i.isLt
    omega
  · intro h
    exact ⟨⟨r - 1, by omega⟩, by change r - 1 + 1 = r; omega⟩

/-- The QFT skeleton contains exactly `n - r` controlled phases of distance `r`. -/
theorem qft_distance_count (n r : ℕ) (hr : 1 ≤ r) :
    (qftDistances n).count r = n - r := by
  simp only [qftDistances, List.count_flatten, List.map_ofFn, List.sum_ofFn,
    Function.comp_def]
  simp_rw [row_distance_count _ r hr]
  rw [Fin.sum_univ_eq_sum_range (fun j => if r ≤ n - j - 1 then 1 else 0) n]
  rw [← Finset.card_filter]
  have he : (Finset.range n).filter (fun j => r ≤ n - j - 1) = Finset.range (n - r) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [he, Finset.card_range]

end

end Giallar.ControlledPhase
