/-
Copyright (c) 2026 Kevin Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Zhao
-/
module

public import Giallar.RealScheduling
public import Mathlib.Data.Finset.Sort
public import Mathlib.Order.Extension.Linear
public import Mathlib.Order.RelClasses

/-!
# Topological numbering and earliest schedules for arbitrary finite strict orders

The standard `LinearExtension` of a partial order, followed by the sorted enumeration of a
finite linear order, provides a bijective topological numbering. Consequently callers need
not supply a pre-existing numbering when applying the earliest-schedule construction.

## Main results

* `exists_strictMono_rank`: a finite partial order admits an increasing bijective numbering.
* `exists_topological_rank`: the relation version for an arbitrary finite strict partial order.
* `exists_least_schedule`: every finite strict partial order admits a pointwise least schedule.
* `exists_least_resource_schedule`: ordered resource users give the same resource guarantee.
-/

@[expose] public section

open scoped NNReal

namespace Giallar.TopologicalOrder

/-- A finite partial order has a bijective numbering increasing on its strict comparisons. -/
theorem exists_strictMono_rank (E : Type*) [Fintype E] [po : PartialOrder E] :
    ∃ rank : E ≃ Fin (Fintype.card E), StrictMono rank := by
  classical
  let e : E ≃ LinearExtension E := Equiv.refl E
  let : Fintype (LinearExtension E) := Fintype.ofEquiv E e
  let sorted : Fin (Fintype.card E) ≃o LinearExtension E :=
    Fintype.orderIsoFinOfCardEq _ (Fintype.card_congr e).symm
  refine ⟨e.trans sorted.symm.toEquiv, ?_⟩
  intro a b hab
  apply sorted.symm.strictMono
  have hle := (@toLinearExtension E po).monotone hab.le
  have hne : (@toLinearExtension E po) a ≠ (@toLinearExtension E po) b := hab.ne
  exact lt_of_le_of_ne hle hne

/-- Every finite strict partial order admits a bijective topological rank, with no assumed
linearization or enumeration supplied by the caller. -/
theorem exists_topological_rank (E : Type*) [Fintype E] (r : E → E → Prop)
    [IsStrictOrder E r] :
    ∃ rank : E ≃ Fin (Fintype.card E), ∀ a b, r a b → rank a < rank b := by
  let := partialOrderOfSO r
  obtain ⟨rank, hrank⟩ := exists_strictMono_rank E
  exact ⟨rank, hrank⟩

/-- Equivalently, an arbitrary finite strict partial order has a topologically ordered
bijection from its finite index range. -/
theorem exists_topological_enumeration (E : Type*) [Fintype E] (r : E → E → Prop)
    [IsStrictOrder E r] :
    ∃ enumerate : Fin (Fintype.card E) ≃ E,
      ∀ i j, r (enumerate i) (enumerate j) → i < j := by
  obtain ⟨rank, hrank⟩ := exists_topological_rank E r
  refine ⟨rank.symm, ?_⟩
  intro i j hij
  simpa only [Equiv.apply_symm_apply] using hrank _ _ hij

/-- Extend a finite relation to natural indices without adding events outside its range. -/
def indexedRelation {E : Type*} {n : ℕ} (enumerate : Fin n ≃ E)
    (r : E → E → Prop) (i j : ℕ) : Prop :=
  ∃ (hi : i < n) (hj : j < n), r (enumerate ⟨i, hi⟩) (enumerate ⟨j, hj⟩)

/-- Extend finite nonnegative durations by zero outside the event range. -/
def indexedDuration {E : Type*} {n : ℕ} (enumerate : Fin n ≃ E)
    (duration : E → ℝ≥0) (i : ℕ) : ℝ≥0 :=
  if hi : i < n then duration (enumerate ⟨i, hi⟩) else 0

/-- The finite-relation extension agrees with the original relation on valid indices. -/
@[simp]
theorem indexedRelation_fin {E : Type*} {n : ℕ} (enumerate : Fin n ≃ E)
    (r : E → E → Prop) (i j : Fin n) :
    indexedRelation enumerate r i j ↔ r (enumerate i) (enumerate j) := by
  simp [indexedRelation, i.isLt, j.isLt]

/-- The extended duration agrees with the original duration at every valid index. -/
@[simp]
theorem indexedDuration_fin {E : Type*} {n : ℕ} (enumerate : Fin n ≃ E)
    (duration : E → ℝ≥0) (i : Fin n) :
    indexedDuration enumerate duration i = duration (enumerate i) := by
  simp [indexedDuration, i.isLt]

/-- A finite strict partial order admits a pointwise least nonnegative real-time schedule,
without any caller-supplied topological numbering. -/
theorem exists_least_schedule (E : Type*) [Finite E] (r : E → E → Prop)
    [IsStrictOrder E r] (duration : E → ℝ≥0) :
    ∃ start : E → ℝ≥0,
      (∀ a b, r a b → start a + duration a ≤ start b) ∧
      ∀ t : E → ℝ≥0, (∀ a b, r a b → t a + duration a ≤ t b) →
        ∀ a, start a ≤ t a := by
  classical
  let := Fintype.ofFinite E
  obtain ⟨enumerate, he⟩ := exists_topological_enumeration E r
  let R := indexedRelation enumerate r
  let D := indexedDuration enumerate duration
  let start : E → ℝ≥0 := fun a => RealScheduling.earliest R D (enumerate.symm a)
  refine ⟨start, ?_, ?_⟩
  · intro a b hab
    have hlt : enumerate.symm a < enumerate.symm b := by
      apply he
      simpa only [Equiv.apply_symm_apply] using hab
    have hr : R (enumerate.symm a) (enumerate.symm b) := by
      simp only [R, indexedRelation_fin, Equiv.apply_symm_apply]
      exact hab
    have h := RealScheduling.finish_le_earliest R D hlt hr
    simpa only [D, indexedDuration_fin, Equiv.apply_symm_apply] using h
  · intro t ht a
    have hf : ∀ i j : Fin (Fintype.card E), R i j →
        t (enumerate i) + D i ≤ t (enumerate j) := by
      intro i j hij
      simpa only [D, indexedDuration_fin] using ht _ _ ((indexedRelation_fin _ _ _ _).mp hij)
    have h := RealScheduling.earliest_le_finite R D (fun i => t (enumerate i)) hf
      (enumerate.symm a).isLt
    change RealScheduling.earliest R D (enumerate.symm a) ≤
      t (enumerate (enumerate.symm a)) at h
    simpa only [Equiv.apply_symm_apply] using h

/-- If each shared-resource pair is already ordered, the least precedence schedule is also
resource-feasible and pointwise no later than every precedence-feasible competitor. -/
theorem exists_least_resource_schedule (E K : Type*) [Finite E]
    (r : E → E → Prop) [IsStrictOrder E r] (duration : E → ℝ≥0)
    (resources : E → Finset K)
    (hr : ∀ a b, a ≠ b → ¬ Disjoint (resources a) (resources b) → r a b ∨ r b a) :
    ∃ start : E → ℝ≥0,
      (∀ a b, r a b → start a + duration a ≤ start b) ∧
      (∀ a b, a ≠ b → ¬ Disjoint (resources a) (resources b) →
        start a + duration a ≤ start b ∨ start b + duration b ≤ start a) ∧
      ∀ t : E → ℝ≥0, (∀ a b, r a b → t a + duration a ≤ t b) →
        ∀ a, start a ≤ t a := by
  obtain ⟨start, hstart, hleast⟩ := exists_least_schedule E r duration
  refine ⟨start, hstart, ?_, hleast⟩
  intro a b hab hres
  exact (hr a b hab hres).imp (hstart a b) (hstart b a)

/-- Pointwise earlier starts give a no-larger finite makespan, including the empty case. -/
theorem makespan_le_of_pointwise {E : Type*} [Fintype E]
    (duration start later : E → ℝ≥0) (h : ∀ a, start a ≤ later a) :
    Finset.univ.sup (fun a => start a + duration a) ≤
      Finset.univ.sup (fun a => later a + duration a) := by
  apply Finset.sup_le_iff.mpr
  intro a ha
  exact (add_le_add (h a) le_rfl).trans (Finset.le_sup
    (f := fun a => later a + duration a) ha)

/-- The arbitrary-poset construction also minimizes makespan among all feasible schedules. -/
theorem exists_minimum_makespan_schedule (E : Type*) [Fintype E]
    (r : E → E → Prop) [IsStrictOrder E r] (duration : E → ℝ≥0) :
    ∃ start : E → ℝ≥0,
      (∀ a b, r a b → start a + duration a ≤ start b) ∧
      ∀ later : E → ℝ≥0, (∀ a b, r a b → later a + duration a ≤ later b) →
        Finset.univ.sup (fun a => start a + duration a) ≤
          Finset.univ.sup (fun a => later a + duration a) := by
  obtain ⟨start, hstart, hleast⟩ := exists_least_schedule E r duration
  exact ⟨start, hstart, fun later hlater =>
    makespan_le_of_pointwise duration start later (hleast later hlater)⟩

end Giallar.TopologicalOrder
