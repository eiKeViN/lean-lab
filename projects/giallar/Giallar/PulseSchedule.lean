/-
Copyright (c) 2026 Kevin Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Zhao
-/
module

public import Giallar.Scheduling
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Rectangular-pulse segments and circuit semantics

The matrix exponential semantics is proved compatible with segment refinement, combination of
simultaneous commuting pulses, and a permutation of segments respecting event dependencies.
The finite segmentation interface records the actual algebraic generator of each segment; it does
not postulate equality of the resulting evolutions.

No Hermiticity assumption is needed for these exponential identities. Physical Hamiltonians are
Hermitian, and `evolution` uses the generator `-I • H`, with units chosen so that `ℏ = 1`.

## Main results

- `exp_list_sum`: combine any list of commuting simultaneous generators.
- `evolution_add`: split one rectangular pulse into adjacent time intervals.
- `segmented_evolution_eq`: temporal and event-grouped segmentations have equal evolution.

## References

The accompanying `Specification.md`, section E3, describes the rectangular-pulse model.
-/

@[expose] public section

namespace Giallar
namespace PulseSchedule

open NormedSpace
open scoped Matrix.Norms.L2Operator

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A finite-dimensional Hamiltonian matrix. -/
abbrev Operator (ι : Type*) := Matrix ι ι ℂ

noncomputable local instance : NormedAlgebra ℚ (Operator ι) :=
  .restrictScalars ℚ ℂ (Operator ι)

/-- Schrödinger evolution under a constant Hamiltonian for a real duration. -/
noncomputable def evolution (H : Operator ι) (t : ℝ) : Operator ι :=
  exp ((t : ℂ) • (-Complex.I • H))

omit [DecidableEq ι] in
/-- A matrix commuting with every list member commutes with their sum. -/
theorem commute_list_sum (A : Operator ι) (l : List (Operator ι))
    (h : ∀ B ∈ l, Commute A B) : Commute A l.sum := by
  induction l with
  | nil => simp
  | cons B l ih =>
    simp only [List.sum_cons]
    exact (h B (by simp)).add_right (ih (fun C hC => h C (by simp [hC])))

/-- The exponential of a commuting sum is the ordered product of the exponentials. -/
theorem exp_list_sum (l : List (Operator ι)) (h : l.Pairwise Commute) :
    exp l.sum = (l.map exp).prod := by
  induction l with
  | nil => simp
  | cons A l ih =>
    obtain ⟨ha, ht⟩ := List.pairwise_cons.mp h
    simp only [List.sum_cons, List.map_cons, List.prod_cons]
    rw [exp_add_of_commute (commute_list_sum A l ha), ih ht]

/-- Adjacent pieces of a constant rectangular pulse combine by adding durations. -/
theorem evolution_add (H : Operator ι) (s t : ℝ) :
    evolution H (s + t) = evolution H s * evolution H t := by
  unfold evolution
  rw [Complex.ofReal_add, add_smul]
  exact exp_add_of_commute (((Commute.refl (-Complex.I • H)).smul_left (s : ℂ)).smul_right
    (t : ℂ))

/-- A rectangular pulse is unchanged by any finite subdivision of its duration. -/
theorem evolution_sum (H : Operator ι) (l : List ℝ) :
    evolution H l.sum = (l.map (evolution H)).prod := by
  induction l with
  | nil => simp [evolution]
  | cons s l ih => simp [evolution_add, ih]

/-- The evolution of a sequence of constant intervals. Each interval stores the generator
contributions active during that interval, already multiplied by the interval duration. -/
noncomputable def segmentedEvolution (blocks : List (List (Operator ι))) : Operator ι :=
  (blocks.map (fun b => exp b.sum)).prod

/-- Expanding simultaneous commuting pulses gives the product of all individual segments. -/
theorem segmentedEvolution_eq_flatten (blocks : List (List (Operator ι)))
    (hc : ∀ b ∈ blocks, b.Pairwise Commute) :
    segmentedEvolution blocks = (blocks.flatten.map exp).prod := by
  induction blocks with
  | nil => simp [segmentedEvolution]
  | cons b bs ih =>
    simp only [segmentedEvolution, List.map_cons, List.prod_cons, List.flatten_cons,
      List.map_append, List.prod_append]
    rw [exp_list_sum b (hc b (by simp)),
      show ((bs.map fun b => exp b.sum).prod) = (bs.flatten.map exp).prod from
        ih (fun c hc' => hc c (by simp [hc']))]

/-- Finite segment certificates suffice to compare a temporal execution with an event-grouped
execution. The certificate compares segment identities, not their matrix products. -/
theorem segmented_evolution_eq {F : Type*} (r : F → F → Prop)
    (hirr : ∀ a, ¬ r a a) (generator : F → Operator ι)
    (hcomm : ∀ a b, ¬ r a b → ¬ r b a → Commute (generator a) (generator b))
    (temporal grouped : List (List F))
    (hp : temporal.flatten.Perm grouped.flatten)
    (ht : Scheduling.Respects r temporal.flatten)
    (hg : Scheduling.Respects r grouped.flatten)
    (hct : ∀ b ∈ temporal, (b.map generator).Pairwise Commute)
    (hcg : ∀ b ∈ grouped, (b.map generator).Pairwise Commute) :
    segmentedEvolution (temporal.map (List.map generator)) =
      segmentedEvolution (grouped.map (List.map generator)) := by
  rw [segmentedEvolution_eq_flatten _ (by
      intro b hb
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hb
      exact hct c hc),
    segmentedEvolution_eq_flatten _ (by
      intro b hb
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hb
      exact hcg c hc)]
  simp only [← List.map_flatten, List.map_map]
  apply Scheduling.linearExtension_prod_eq r hirr (fun a => exp (generator a))
    (fun a b hab hba => (hcomm a b hab hba).exp) hp ht hg

/-- Chronological interval composition places the earliest factor on the right. -/
noncomputable def chronologicalEvolution (blocks : List (List (Operator ι))) : Operator ι :=
  ((blocks.map (fun b => exp b.sum)).reverse).prod

/-- A commuting simultaneous block can also be expanded in reverse order. -/
theorem exp_list_sum_reverse (l : List (Operator ι)) (h : l.Pairwise Commute) :
    exp l.sum = (l.reverse.map exp).prod := by
  have hr : l.reverse.Pairwise Commute :=
    List.pairwise_reverse.mpr (h.imp fun hab => hab.symm)
  simpa only [List.sum_reverse] using exp_list_sum l.reverse hr

/-- Chronological interval semantics expands to chronological fragment semantics. -/
theorem chronologicalEvolution_eq_flatten (blocks : List (List (Operator ι)))
    (hc : ∀ b ∈ blocks, b.Pairwise Commute) :
    chronologicalEvolution blocks = (blocks.flatten.reverse.map exp).prod := by
  induction blocks with
  | nil => simp [chronologicalEvolution]
  | cons b bs ih =>
    simp only [chronologicalEvolution, List.map_cons, List.reverse_cons, List.prod_append,
      List.prod_singleton, List.flatten_cons, List.reverse_append, List.map_append]
    rw [show ((bs.map fun b => exp b.sum).reverse).prod =
        (bs.flatten.reverse.map exp).prod from ih (fun c hc' => hc c (by simp [hc'])),
      exp_list_sum_reverse b (hc b (by simp))]

/-- Temporal and event-grouped segment certificates agree in chronological convention. -/
theorem chronological_segmented_evolution_eq {F : Type*} (r : F → F → Prop)
    (hirr : ∀ a, ¬ r a a) (generator : F → Operator ι)
    (hcomm : ∀ a b, ¬ r a b → ¬ r b a → Commute (generator a) (generator b))
    (temporal grouped : List (List F))
    (hp : temporal.flatten.Perm grouped.flatten)
    (ht : Scheduling.Respects r temporal.flatten)
    (hg : Scheduling.Respects r grouped.flatten)
    (hct : ∀ b ∈ temporal, (b.map generator).Pairwise Commute)
    (hcg : ∀ b ∈ grouped, (b.map generator).Pairwise Commute) :
    chronologicalEvolution (temporal.map (List.map generator)) =
      chronologicalEvolution (grouped.map (List.map generator)) := by
  rw [chronologicalEvolution_eq_flatten _ (by
      intro b hb
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hb
      exact hct c hc),
    chronologicalEvolution_eq_flatten _ (by
      intro b hb
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hb
      exact hcg c hc)]
  simp only [← List.map_flatten, ← List.map_reverse, List.map_map]
  exact Scheduling.linearExtension_reverse_prod_eq r hirr (fun a => exp (generator a))
    (fun a b hab hba => (hcomm a b hab hba).exp) hp ht hg

/-- Generator contribution of one pulse fragment. -/
noncomputable def fragmentGenerator {E F : Type*} (H : E → Operator ι)
    (event : F → E) (length : F → ℝ) (f : F) : Operator ι :=
  (length f : ℂ) • (-Complex.I • H (event f))

omit [Fintype ι] [DecidableEq ι] in
/-- A homogeneous group of fragments sums to the generator of one complete event. -/
theorem fragmentGenerator_sum {E F : Type*} (H : E → Operator ι)
    (event : F → E) (length : F → ℝ) (e : E) (l : List F)
    (he : ∀ f ∈ l, event f = e) :
    (l.map (fragmentGenerator H event length)).sum =
      (((l.map length).sum : ℝ) : ℂ) • (-Complex.I • H e) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, Complex.ofReal_add, add_smul]
    rw [ih (fun f hf => he f (by simp [hf]))]
    simp [fragmentGenerator, he a (by simp)]

/-- A group of pieces of one event realizes the event's full rectangular pulse. -/
theorem eventGroup_evolution {E F : Type*} (H : E → Operator ι)
    (event : F → E) (length : F → ℝ) (e : E) (l : List F) (d : ℝ)
    (he : ∀ f ∈ l, event f = e) (hd : (l.map length).sum = d) :
    exp (l.map (fragmentGenerator H event length)).sum = evolution (H e) d := by
  rw [fragmentGenerator_sum H event length e l he, hd]
  rfl

/-- Grouping a segment certificate by event produces the target list of pulse gates. -/
theorem grouped_evolution_eq {E F : Type*} (H : E → Operator ι)
    (event : F → E) (length : F → ℝ) (duration : E → ℝ)
    (groups : List (E × List F))
    (he : ∀ g ∈ groups, ∀ f ∈ g.2, event f = g.1)
    (hd : ∀ g ∈ groups, (g.2.map length).sum = duration g.1) :
    segmentedEvolution (groups.map fun g => g.2.map (fragmentGenerator H event length)) =
      (groups.map fun g => evolution (H g.1) (duration g.1)).prod := by
  unfold segmentedEvolution
  congr 1
  simp only [List.map_map]
  apply List.map_congr_left
  intro g hg
  exact eventGroup_evolution H event length g.1 g.2 (duration g.1) (he g hg) (hd g hg)

end PulseSchedule
end Giallar
