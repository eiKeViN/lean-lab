/-
Copyright (c) 2026 Kevin Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Zhao
-/
module

public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Data.List.Basic
public import Mathlib.Order.WellFounded
public import Mathlib.Tactic.Linarith

/-!
# Semantics-preserving worklist expansion

A pending task may either emit a primitive operator or expand into a bounded list of
strictly lower-ranked tasks. Operators are multiplied in execution order: the operator
of the first task acts first, hence appears on the right of the resulting product.

## Main results

* `Giallar.Worklist.step_preserves`: one processing step preserves the target operator.
* `Giallar.Worklist.step_potential_lt`: bounded expansion strictly decreases a natural potential.
* `Giallar.Worklist.steps_bound`: every finite processing trace has an explicit length bound.
* `Giallar.Worklist.exists_terminal`: progress and the potential imply termination.
* `Giallar.Worklist.terminal_correct`: terminal output equals the initial target operator.

The rules specify local compiler obligations rather than assuming correctness of a whole
compiler. The monoid may in particular be a monoid of quantum circuit operators.
-/

@[expose] public section

namespace Giallar.Worklist

variable {Task M : Type*} [Monoid M]

/-- The operator of a sequence, with the first task acting first. -/
def eval (sem : Task → M) : List Task → M
  | [] => 1
  | t :: ts => eval sem ts * sem t

@[simp] theorem eval_nil (sem : Task → M) : eval sem [] = 1 := rfl

@[simp] theorem eval_cons (sem : Task → M) (t : Task) (ts : List Task) :
    eval sem (t :: ts) = eval sem ts * sem t := rfl

@[simp] theorem eval_append (sem : Task → M) (xs ys : List Task) :
    eval sem (xs ++ ys) = eval sem ys * eval sem xs := by
  induction xs with
  | nil => simp
  | cons t ts ih => simp only [List.cons_append, eval_cons, ih, mul_assoc]

/-- A compiler state records pending tasks and the operator already emitted. -/
structure State (Task M : Type*) where
  /-- Tasks in execution order. -/
  pending : List Task
  /-- Operator already emitted, acting before the pending tasks. -/
  emitted : M

/-- The full target operator represented by a processing state. -/
def meaning (sem : Task → M) (s : State Task M) : M :=
  eval sem s.pending * s.emitted

/-- A local expansion provides bounded, lower-ranked tasks and preserves operator semantics. -/
structure Expansion (sem : Task → M) (rank : Task → ℕ) (b : ℕ) (t : Task) where
  /-- The replacement tasks, in execution order. -/
  children : List Task
  /-- The maximum number of children is fixed independently of the task. -/
  length_le : children.length ≤ b
  /-- Every replacement task has a strictly smaller rank. -/
  rank_lt : ∀ u ∈ children, rank u < rank t
  /-- The replacement sequence implements the task operator. -/
  sound : eval sem children = sem t

/-- One processing step either emits a primitive task or expands the first pending task. -/
inductive Step (sem : Task → M) (rank : Task → ℕ) (b : ℕ) (primitive : Task → Prop) :
    State Task M → State Task M → Prop
  | emit (t : Task) (ts : List Task) (w : M) (h : primitive t) :
      Step sem rank b primitive ⟨t :: ts, w⟩ ⟨ts, sem t * w⟩
  | expand (t : Task) (ts : List Task) (w : M) (e : Expansion sem rank b t) :
      Step sem rank b primitive ⟨t :: ts, w⟩ ⟨e.children ++ ts, w⟩

/-- One local step preserves the operator represented by the state. -/
theorem step_preserves {sem : Task → M} {rank : Task → ℕ} {b : ℕ}
    {primitive : Task → Prop} {s s' : State Task M}
    (h : Step sem rank b primitive s s') : meaning sem s' = meaning sem s := by
  cases h with
  | emit t ts w hp => simp [meaning, mul_assoc]
  | expand t ts w e => simp [meaning, e.sound]

/-- The total rank weight of a task list. -/
def potential (rank : Task → ℕ) (b : ℕ) : List Task → ℕ
  | [] => 0
  | t :: ts => (b + 1) ^ rank t + potential rank b ts

@[simp] theorem potential_nil (rank : Task → ℕ) (b : ℕ) :
    potential rank b [] = 0 := rfl

@[simp] theorem potential_cons (rank : Task → ℕ) (b : ℕ) (t : Task) (ts : List Task) :
    potential rank b (t :: ts) = (b + 1) ^ rank t + potential rank b ts := rfl

/-- The recursive potential is the sum of the rank weights specified in the mathematical model. -/
theorem potential_eq_sum (rank : Task → ℕ) (b : ℕ) (ts : List Task) :
    potential rank b ts = (ts.map fun t => (b + 1) ^ rank t).sum := by
  induction ts with
  | nil => simp
  | cons t ts ih => simp [potential, ih]

@[simp] theorem potential_append (rank : Task → ℕ) (b : ℕ) (xs ys : List Task) :
    potential rank b (xs ++ ys) = potential rank b xs + potential rank b ys := by
  induction xs with
  | nil => simp
  | cons t ts ih => simp only [List.cons_append, potential_cons, ih, Nat.add_assoc]

/-- Uniform rank bounds give a length times maximum-weight bound. -/
theorem potential_le_length_mul (rank : Task → ℕ) (b h : ℕ) (ts : List Task)
    (hr : ∀ t ∈ ts, rank t ≤ h) :
    potential rank b ts ≤ ts.length * (b + 1) ^ h := by
  revert hr
  induction ts with
  | nil => intro hr; simp
  | cons t ts ih =>
      intro hr
      have ht : (b + 1) ^ rank t ≤ (b + 1) ^ h :=
        Nat.pow_le_pow_right (by omega) (hr t (by simp))
      have hs := ih (fun u hu => hr u (by simp [hu]))
      simp only [potential_cons, List.length_cons]
      nlinarith

/-- Boundedly many tasks of smaller rank weigh strictly less than their parent. -/
theorem expansion_potential_lt {sem : Task → M} {rank : Task → ℕ} {b : ℕ}
    {t : Task} (e : Expansion sem rank b t) :
    potential rank b e.children < (b + 1) ^ rank t := by
  cases h : rank t with
  | zero =>
      have he : e.children = [] := by
        cases hc : e.children with
        | nil => rfl
        | cons u us =>
            have := e.rank_lt u (by simp [hc])
            omega
      simp [he]
  | succ k =>
      have hr : ∀ u ∈ e.children, rank u ≤ k := by
        intro u hu
        have := e.rank_lt u hu
        omega
      have hw := potential_le_length_mul rank b k e.children hr
      have hl := Nat.mul_le_mul_right ((b + 1) ^ k) e.length_le
      have hp : 0 < (b + 1) ^ k := pow_pos (by omega) _
      rw [pow_succ]
      nlinarith

/-- Every processing step strictly decreases the pending-list potential. -/
theorem step_potential_lt {sem : Task → M} {rank : Task → ℕ} {b : ℕ}
    {primitive : Task → Prop} {s s' : State Task M}
    (h : Step sem rank b primitive s s') :
    potential rank b s'.pending < potential rank b s.pending := by
  cases h with
  | emit t ts w hp =>
      simp only [potential_cons]
      have : 0 < (b + 1) ^ rank t := pow_pos (by omega) _
      omega
  | expand t ts w e =>
      simp only [potential_append, potential_cons]
      exact Nat.add_lt_add_right (expansion_potential_lt e) _

/-- The reverse processing relation is well founded. -/
theorem step_wellFounded (sem : Task → M) (rank : Task → ℕ) (b : ℕ)
    (primitive : Task → Prop) :
    WellFounded (fun s' s => Step sem rank b primitive s s') := by
  exact (measure (fun s : State Task M => potential rank b s.pending)).wf.mono
    (fun _ _ h => step_potential_lt h)

/-- A finite processing trace records its exact number of steps. -/
inductive Steps (sem : Task → M) (rank : Task → ℕ) (b : ℕ) (primitive : Task → Prop) :
    State Task M → ℕ → State Task M → Prop
  | refl (s : State Task M) : Steps sem rank b primitive s 0 s
  | cons {s s' s'' : State Task M} {n : ℕ}
      (head : Step sem rank b primitive s s')
      (tail : Steps sem rank b primitive s' n s'') :
      Steps sem rank b primitive s (n + 1) s''

/-- A trace preserves the whole target operator. -/
theorem steps_preserves {sem : Task → M} {rank : Task → ℕ} {b : ℕ}
    {primitive : Task → Prop} {s s' : State Task M} {n : ℕ}
    (h : Steps sem rank b primitive s n s') : meaning sem s' = meaning sem s := by
  induction h with
  | refl => rfl
  | cons head tail ih => exact ih.trans (step_preserves head)

/-- The initial potential bounds the number of processing steps, including the final step. -/
theorem steps_bound {sem : Task → M} {rank : Task → ℕ} {b : ℕ}
    {primitive : Task → Prop} {s s' : State Task M} {n : ℕ}
    (h : Steps sem rank b primitive s n s') :
    potential rank b s'.pending + n ≤ potential rank b s.pending := by
  induction h with
  | refl => simp
  | cons head tail ih =>
      have hd := step_potential_lt head
      omega

/-- A task-level progress obligation suffices to advance every nonempty state. -/
theorem progress_of_tasks (sem : Task → M) (rank : Task → ℕ) (b : ℕ)
    (primitive : Task → Prop)
    (progress : ∀ t, primitive t ∨ Nonempty (Expansion sem rank b t))
    (s : State Task M) (hne : s.pending ≠ []) :
    ∃ s', Step sem rank b primitive s s' := by
  rcases s with ⟨pending, emitted⟩
  cases pending with
  | nil => exact (hne rfl).elim
  | cons t ts =>
      rcases progress t with hp | he
      · exact ⟨_, Step.emit t ts emitted hp⟩
      · rcases he with ⟨e⟩
        exact ⟨_, Step.expand t ts emitted e⟩

/-- Progress and strictly decreasing potential imply a terminal trace within the explicit bound. -/
theorem exists_terminal (sem : Task → M) (rank : Task → ℕ) (b : ℕ)
    (primitive : Task → Prop)
    (progress : ∀ t, primitive t ∨ Nonempty (Expansion sem rank b t))
    (s : State Task M) :
    ∃ n s', Steps sem rank b primitive s n s' ∧ s'.pending = [] ∧
      n ≤ potential rank b s.pending := by
  induction s using (step_wellFounded sem rank b primitive).induction with
  | h s ih =>
      by_cases he : s.pending = []
      · exact ⟨0, s, Steps.refl s, he, Nat.zero_le _⟩
      · obtain ⟨next, hn⟩ := progress_of_tasks sem rank b primitive progress s he
        obtain ⟨n, final, trace, hf, hb⟩ := ih next hn
        refine ⟨n + 1, final, Steps.cons hn trace, hf, ?_⟩
        have hd := step_potential_lt hn
        omega

/-- A completed trace emits precisely the operator of the initial state. -/
theorem terminal_correct {sem : Task → M} {rank : Task → ℕ} {b : ℕ}
    {primitive : Task → Prop} {s s' : State Task M} {n : ℕ}
    (trace : Steps sem rank b primitive s n s') (terminal : s'.pending = []) :
    s'.emitted = meaning sem s := by
  have h := steps_preserves trace
  simpa [meaning, terminal] using h

/-- Total correctness from an initially empty output, including the explicit processing bound. -/
theorem total_correctness (sem : Task → M) (rank : Task → ℕ) (b : ℕ)
    (primitive : Task → Prop)
    (progress : ∀ t, primitive t ∨ Nonempty (Expansion sem rank b t))
    (tasks : List Task) :
    ∃ n s', Steps sem rank b primitive ⟨tasks, 1⟩ n s' ∧ s'.pending = [] ∧
      s'.emitted = eval sem tasks ∧ n ≤ potential rank b tasks := by
  obtain ⟨n, final, trace, hf, hb⟩ :=
    exists_terminal sem rank b primitive progress ⟨tasks, 1⟩
  refine ⟨n, final, trace, hf, ?_, hb⟩
  simpa [meaning] using terminal_correct trace hf

/-- Binary expansion of a power into a primitive unit and a smaller residual power. -/
def powerExpansion (a : M) (k : ℕ) : Expansion (fun n : ℕ => a ^ n) id 2 (k + 2) where
  children := [1, k + 1]
  length_le := by simp
  rank_lt := by
    intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl <;> simp only [id_eq] <;> omega
  sound := by simp [eval, pow_succ, mul_assoc]

/-- A nontrivial local progress example: only zero and unit powers may be emitted. -/
theorem power_progress (a : M) (n : ℕ) :
    n ≤ 1 ∨ Nonempty (Expansion (fun k : ℕ => a ^ k) id 2 n) := by
  cases n with
  | zero => exact Or.inl (by omega)
  | succ n =>
      cases n with
      | zero => exact Or.inl (by omega)
      | succ k => exact Or.inr ⟨powerExpansion a k⟩

/-- Expanding a power into primitive unit factors terminates and preserves its value. -/
theorem power_tasks_terminate (a : M) (n : ℕ) :
    ∃ steps final,
      Steps (fun k : ℕ => a ^ k) id 2 (fun k => k ≤ 1) ⟨[n], 1⟩ steps final ∧
      final.pending = [] ∧ final.emitted = a ^ n ∧ steps ≤ 3 ^ n := by
  simpa [potential, eval] using
    total_correctness (fun k : ℕ => a ^ k) id 2 (fun k => k ≤ 1) (power_progress a) [n]

end Giallar.Worklist
