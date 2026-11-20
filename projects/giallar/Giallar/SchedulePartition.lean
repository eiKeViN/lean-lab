/-
Copyright (c) 2026 Kevin Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Zhao
-/
module

public import Giallar.Scheduling
public import Mathlib.Data.List.Sort

/-!
# Finite partitions of pulse segments

Grouping a finite list by a complete duplicate-free list of keys preserves its elements and sorts
it by key. These combinatorial facts connect the actual tick/event segmentation to the operator
semantics without assuming equality of the resulting operators.
-/

@[expose] public section

namespace Giallar.PulseSchedule

/-- The lists of elements with each key, in the given key order. -/
def partitionBy {K F : Type*} [DecidableEq K] (key : F → K) (keys : List K)
    (xs : List F) : List (List F) :=
  keys.map fun k => xs.filter (fun x => key x = k)

/-- A complete duplicate-free partition is a permutation of the input list. -/
theorem partitionBy_flatten_perm {K F : Type*} [DecidableEq K] (key : F → K)
    (keys : List K) (xs : List F) (hk : keys.Nodup)
    (hcover : ∀ x ∈ xs, key x ∈ keys) : (partitionBy key keys xs).flatten.Perm xs := by
  induction keys generalizing xs with
  | nil =>
    have : xs = [] := by
      by_contra h
      obtain ⟨x, l, rfl⟩ := List.exists_cons_of_ne_nil h
      simpa using hcover x (by simp)
    subst xs
    simp [partitionBy]
  | cons k ks ih =>
    obtain ⟨hkn, hks⟩ := List.nodup_cons.mp hk
    let ys := xs.filter fun x => key x ≠ k
    have hcov : ∀ x ∈ ys, key x ∈ ks := by
      intro x hx
      have hm := List.mem_filter.mp hx
      rcases List.mem_cons.mp (hcover x hm.1) with h | h
      · exact False.elim (by simpa [h] using hm.2)
      · exact h
    have hfilters : partitionBy key ks xs = partitionBy key ks ys := by
      apply List.map_congr_left
      intro j hj
      simp only [ys, List.filter_filter]
      apply List.filter_congr
      intro x hx
      have hjk : j ≠ k := by
        intro h
        subst j
        exact hkn hj
      by_cases h : key x = j
      · simp [h, hjk]
      · simp [h]
    simp only [partitionBy, List.map_cons, List.flatten_cons]
    change ((xs.filter fun x => key x = k) ++ (partitionBy key ks xs).flatten).Perm xs
    rw [hfilters]
    exact ((List.Perm.refl _).append (ih ys hks hcov)).trans
      (by simpa [ys] using List.filter_append_perm (fun x => decide (key x = k)) xs)

private theorem pairwise_of_forall_mem {F : Type*} (r : F → F → Prop) (xs : List F)
    (h : ∀ x ∈ xs, ∀ y ∈ xs, r x y) : xs.Pairwise r := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    apply List.pairwise_cons.mpr
    exact ⟨fun y hy => h x (by simp) y (by simp [hy]),
      ih (fun a ha b hb => h a (by simp [ha]) b (by simp [hb]))⟩

/-- Ordering partition keys orders the flattened elements by their keys. -/
theorem partitionBy_pairwise {K F : Type*} [DecidableEq K] (key : F → K)
    (keys : List K) (xs : List F) (r : K → K → Prop)
    (hrefl : ∀ k, r k k) (hkeys : keys.Pairwise r) :
    (partitionBy key keys xs).flatten.Pairwise (fun x y => r (key x) (key y)) := by
  apply List.pairwise_flatten.mpr
  constructor
  · intro ys hys
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hys
    apply pairwise_of_forall_mem
    intro a ha b hb
    have ha' : key a = k := by simpa using (List.mem_filter.mp ha).2
    have hb' : key b = k := by simpa using (List.mem_filter.mp hb).2
    simpa [ha', hb'] using hrefl k
  · apply List.pairwise_map.mpr
    apply hkeys.imp
    intro k l hkl a ha b hb
    have ha' : key a = k := by simpa using (List.mem_filter.mp ha).2
    have hb' : key b = l := by simpa using (List.mem_filter.mp hb).2
    simpa [ha', hb'] using hkl

end Giallar.PulseSchedule
