/-
Copyright (c) 2026 Kevin Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Zhao
-/
module

public import Giallar.Approximation
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.Order.Compact

/-!
# Approximation up to an attained global phase

The phase distance minimizes `‖U - z • V‖` over the complex unit circle. Compactness gives an
actual minimizing phase; callers never need to supply a witness as an extra assumption.
Chronological products compose their selected phases multiplicatively.

## Main results

* `exists_phase_min`: the unit circle contains a minimizing phase.
* `phaseDistance_isLeast`: the selected value really is the minimum of all phase errors.
* `phaseDistance_eval_le`: product phase error is at most the sum of local phase errors.
-/

@[expose] public section

namespace Giallar

section Minimum

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]

/-- The error function on the complex unit circle attains a minimum. -/
theorem exists_phase_min (U V : A) :
    ∃ z : ℂ, ‖z‖ = 1 ∧ ∀ w : ℂ, ‖w‖ = 1 → ‖U - z • V‖ ≤ ‖U - w • V‖ := by
  have hne : (Metric.sphere (0 : ℂ) 1).Nonempty := ⟨1, by simp⟩
  have hcont : Continuous (fun z : ℂ => ‖U - z • V‖) :=
    (continuous_const.sub (continuous_id.smul continuous_const)).norm
  obtain ⟨z, hz, hmin⟩ :=
    (isCompact_sphere (0 : ℂ) 1).exists_isMinOn hne hcont.continuousOn
  refine ⟨z, by simpa using hz, fun w hw => ?_⟩
  exact hmin (by simpa using hw)

/-- A minimizing global phase, selected from the compact complex unit circle. -/
noncomputable def optimalPhase (U V : A) : ℂ := Classical.choose (exists_phase_min U V)

/-- The attained minimum operator error after ignoring one global phase. -/
noncomputable def phaseDistance (U V : A) : ℝ := ‖U - optimalPhase U V • V‖

@[simp]
theorem norm_optimalPhase (U V : A) : ‖optimalPhase U V‖ = 1 :=
  (Classical.choose_spec (exists_phase_min U V)).1

/-- The selected error is bounded by the error at every unit-modulus phase. -/
theorem phaseDistance_le (U V : A) (z : ℂ) (hz : ‖z‖ = 1) :
    phaseDistance U V ≤ ‖U - z • V‖ :=
  (Classical.choose_spec (exists_phase_min U V)).2 z hz

/-- The phase distance is exactly the minimum of the nonempty set of phase errors. -/
theorem phaseDistance_isLeast (U V : A) :
    IsLeast ((fun z : ℂ => ‖U - z • V‖) '' {z : ℂ | ‖z‖ = 1})
      (phaseDistance U V) := by
  refine ⟨⟨optimalPhase U V, norm_optimalPhase U V, rfl⟩, ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  exact phaseDistance_le U V z hz

/-- Phase distance is nonnegative. -/
theorem phaseDistance_nonneg (U V : A) : 0 ≤ phaseDistance U V := norm_nonneg _

/-- Choosing phase one bounds phase distance by ordinary operator distance. -/
theorem phaseDistance_le_norm_sub (U V : A) : phaseDistance U V ≤ ‖U - V‖ := by
  simpa using phaseDistance_le U V 1 (by simp)

@[simp]
theorem phaseDistance_self (U : A) : phaseDistance U U = 0 := by
  apply le_antisymm
  · simpa using phaseDistance_le_norm_sub U U
  · exact phaseDistance_nonneg U U

end Minimum

section Products

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]

/-- Scalars can be factored out of a chronological product, without commuting operators. -/
theorem eval_smul (l : List (ℂ × A)) :
    eval (l.map fun p => p.1 • p.2) = (l.map Prod.fst).prod • eval (l.map Prod.snd) := by
  induction l with
  | nil => simp
  | cons p l ih =>
    simp only [List.map_cons, eval_cons, List.prod_cons, ih, smul_mul_smul]
    rw [mul_comm ((l.map Prod.fst).prod) p.1]

/-- The product of the independently minimizing local phases. -/
noncomputable def productPhase (l : List (A × A)) : ℂ :=
  (l.map fun p => optimalPhase p.1 p.2).prod

@[simp]
theorem norm_productPhase (l : List (A × A)) : ‖productPhase l‖ = 1 := by
  simp [productPhase]

variable [NormOneClass A]

/-- Product phase error is bounded by the sum of local errors for arbitrary contractions. -/
theorem phaseDistance_eval_le (l : List (A × A))
    (h : ∀ p ∈ l, ‖p.1‖ ≤ 1 ∧ ‖p.2‖ ≤ 1) :
    phaseDistance (eval (l.map Prod.fst)) (eval (l.map Prod.snd)) ≤
      (l.map fun p => phaseDistance p.1 p.2).sum := by
  have hadj : ∀ q ∈ l.map (fun p => (p.1, optimalPhase p.1 p.2 • p.2)),
      ‖q.1‖ ≤ 1 ∧ ‖q.2‖ ≤ 1 := by
    intro q hq
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
    simpa only [norm_smul, norm_optimalPhase, one_mul] using h p hp
  have hlocal := norm_eval_sub_le _ hadj
  have hfactor := eval_smul (l.map fun p => (optimalPhase p.1 p.2, p.2))
  simp only [List.map_map, Function.comp_def] at hfactor hlocal
  rw [hfactor] at hlocal
  exact (phaseDistance_le _ _ (productPhase l) (norm_productPhase l)).trans hlocal

end Products

section Unitary

variable {A : Type*} [NormedRing A] [StarRing A] [CStarRing A] [Nontrivial A]
  [NormedAlgebra ℂ A]

/-- The phase-distance composition theorem for unitary circuits. -/
theorem phaseDistance_unitary_eval_le (l : List (unitary A × unitary A)) :
    phaseDistance (eval (l.map fun p => (p.1 : A)))
        (eval (l.map fun p => (p.2 : A))) ≤
      (l.map fun p => phaseDistance (p.1 : A) (p.2 : A)).sum := by
  simpa only [List.map_map, Function.comp_def] using
    phaseDistance_eval_le (l.map fun p => ((p.1 : A), (p.2 : A))) (by
      intro q hq
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
      simp)

end Unitary

end Giallar
