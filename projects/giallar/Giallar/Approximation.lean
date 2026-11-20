/-
Copyright (c) 2026 Kevin Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Zhao
-/
module

public import Mathlib.Analysis.CStarAlgebra.Basic
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Data.List.Forall2
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.NoncommRing

/-!
# Compositional approximation contracts

Chronological circuit evaluation multiplies the last operation on the left.
The error bound uses contraction hypotheses and therefore also applies to unitaries.

## Main results

* `norm_eval_sub_le`: the total error is bounded by the sum of local errors.
* `norm_unitary_eval_sub_le`: the unitary specialization of the bound.
-/

@[expose] public section

namespace Giallar

/-- Evaluate a chronological list of operations, with the first operation on the right. -/
def eval {A : Type*} [Monoid A] : List A → A
  | [] => 1
  | a :: l => eval l * a

@[simp] theorem eval_nil {A : Type*} [Monoid A] : eval ([] : List A) = 1 := rfl

@[simp] theorem eval_cons {A : Type*} [Monoid A] (a : A) (l : List A) :
    eval (a :: l) = eval l * a := rfl

@[simp] theorem eval_append {A : Type*} [Monoid A] (l k : List A) :
    eval (l ++ k) = eval k * eval l := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih, mul_assoc]

section Normed

variable {A : Type*} [NormedRing A] [NormOneClass A]

/-- A chronological list of contractions has operator norm at most one. -/
theorem norm_eval_le_one (l : List A) (h : ∀ a ∈ l, ‖a‖ ≤ 1) : ‖eval l‖ ≤ 1 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ha := h a (by simp)
    have hl := ih (fun b hb => h b (by simp [hb]))
    calc
      ‖eval (a :: l)‖ ≤ ‖eval l‖ * ‖a‖ := norm_mul_le _ _
      _ ≤ 1 * 1 := mul_le_mul hl ha (norm_nonneg _) zero_le_one
      _ = 1 := one_mul _

/-- Error in a pair of products of contractions is at most the sum of local errors. -/
theorem norm_eval_sub_le (l : List (A × A))
    (h : ∀ p ∈ l, ‖p.1‖ ≤ 1 ∧ ‖p.2‖ ≤ 1) :
    ‖eval (l.map Prod.fst) - eval (l.map Prod.snd)‖ ≤
      (l.map (fun p => ‖p.1 - p.2‖)).sum := by
  induction l with
  | nil => simp
  | cons p l ih =>
    have hp := h p (by simp)
    have ht : ∀ q ∈ l, ‖q.1‖ ≤ 1 ∧ ‖q.2‖ ≤ 1 := fun q hq => h q (by simp [hq])
    have hv : ‖eval (l.map Prod.snd)‖ ≤ 1 := norm_eval_le_one _ (by
      intro a ha
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ha
      exact (ht q hq).2)
    have alg : eval (l.map Prod.fst) * p.1 - eval (l.map Prod.snd) * p.2 =
        (eval (l.map Prod.fst) - eval (l.map Prod.snd)) * p.1 +
          eval (l.map Prod.snd) * (p.1 - p.2) := by noncomm_ring
    simp only [List.map_cons, eval_cons, List.sum_cons]
    rw [alg]
    calc
      _ ≤ ‖(eval (l.map Prod.fst) - eval (l.map Prod.snd)) * p.1‖ +
          ‖eval (l.map Prod.snd) * (p.1 - p.2)‖ := norm_add_le _ _
      _ ≤ ‖eval (l.map Prod.fst) - eval (l.map Prod.snd)‖ * ‖p.1‖ +
          ‖eval (l.map Prod.snd)‖ * ‖p.1 - p.2‖ :=
        add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
      _ ≤ (l.map (fun q => ‖q.1 - q.2‖)).sum + ‖p.1 - p.2‖ := by
        gcongr
        · exact (mul_le_of_le_one_right (norm_nonneg _) hp.1).trans (ih ht)
        · exact mul_le_of_le_one_left (norm_nonneg _) hv
      _ = _ := add_comm _ _

end Normed

section Unitary

variable {A : Type*} [NormedRing A] [StarRing A] [CStarRing A] [Nontrivial A]

/-- The compositional error bound for pairs of unitaries in a C-star ring. -/
theorem norm_unitary_eval_sub_le (l : List (unitary A × unitary A)) :
    ‖eval (l.map (fun p => (p.1 : A))) - eval (l.map (fun p => (p.2 : A)))‖ ≤
      (l.map (fun p => ‖(p.1 : A) - (p.2 : A)‖)).sum := by
  simpa only [List.map_map, Function.comp_def] using
    norm_eval_sub_le (l.map (fun p => ((p.1 : A), (p.2 : A)))) (by
      intro q hq
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
      simp)

end Unitary

end Giallar
