/-
Copyright (c) 2026 Kevin Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Zhao
-/
module

public import Giallar.Approximation
public import Mathlib.Analysis.CStarAlgebra.Exponential
public import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Tactic.NoncommRing

/-!
# Perturbation of Hamiltonian evolution

For skew-adjoint generators the exponential factors are unitary. A product derivative
and the mean value inequality give a sharp linear perturbation bound without a
commutativity assumption on the two generators.
-/

@[expose] public section

open NormedSpace

namespace Giallar

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [StarRing A]
  [StarModule ℝ A] [NormedAlgebra ℚ A] [CStarRing A] [CompleteSpace A] [Nontrivial A]

omit [Nontrivial A] in
/-- A real multiple of a skew-adjoint generator has unitary exponential. -/
theorem exp_smul_mem_unitary (a : A) (ha : star a = -a) (t : ℝ) :
    exp (t • a) ∈ unitary A := by
  apply exp_mem_unitary_of_mem_skewAdjoint
  simp [skewAdjoint.mem_iff, star_smul, ha]

omit [Nontrivial A] in
/-- The difference of two evolutions is bounded by time times generator distance. -/
theorem norm_exp_smul_sub_le (a b : A) (ha : star a = -a) (hb : star b = -b)
    {t : ℝ} (ht : 0 ≤ t) :
    ‖exp (t • a) - exp (t • b)‖ ≤ t * ‖a - b‖ := by
  let f : ℝ → A := fun s => exp ((t - s) • a) * exp (s • b)
  let f' : ℝ → A := fun s => exp ((t - s) • a) * (b - a) * exp (s • b)
  have hd (s : ℝ) : HasDerivAt f (f' s) s := by
    have hleft := HasDerivAt.scomp s (hasDerivAt_exp_smul_const a (t - s))
      ((hasDerivAt_const s t).sub (hasDerivAt_id s))
    have hright := hasDerivAt_exp_smul_const' b s
    convert hleft.mul hright using 1 <;> dsimp [f, f'] <;>
      (try simp only [zero_sub, neg_smul, one_smul]) <;> noncomm_ring
  have hnorm (s : ℝ) : ‖f' s‖ ≤ ‖a - b‖ := by
    dsimp [f']
    rw [CStarRing.norm_mul_mem_unitary _ (exp_smul_mem_unitary b hb s),
      CStarRing.norm_mem_unitary_mul _ (exp_smul_mem_unitary a ha (t - s)), norm_sub_rev]
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := f) (f' := f') (s := Set.Icc 0 t) (x := 0) (y := t)
    (fun s hs => (hd s).hasDerivWithinAt) (fun s hs => hnorm s)
    (convex_Icc (0 : ℝ) t) (by simp [ht]) (by simp [ht])
  simpa [f, norm_sub_rev, Real.norm_eq_abs, abs_of_nonneg ht, mul_comm] using h

/-- Error bounds for chronological products of perturbed skew-adjoint evolutions. -/
theorem norm_evolution_sub_le (l : List (ℝ × A × A))
    (h : ∀ p ∈ l, 0 ≤ p.1 ∧ star p.2.1 = -p.2.1 ∧ star p.2.2 = -p.2.2) :
    ‖eval (l.map (fun p => exp (p.1 • p.2.1))) -
      eval (l.map (fun p => exp (p.1 • p.2.2)))‖ ≤
        (l.map (fun p => p.1 * ‖p.2.1 - p.2.2‖)).sum := by
  have hbase := norm_eval_sub_le
    (l.map (fun p => (exp (p.1 • p.2.1), exp (p.1 • p.2.2)))) (by
      intro q hq
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
      exact ⟨(CStarRing.norm_of_mem_unitary
        (exp_smul_mem_unitary _ (h p hp).2.1 _)).le,
        (CStarRing.norm_of_mem_unitary (exp_smul_mem_unitary _ (h p hp).2.2 _)).le⟩)
  simp only [List.map_map, Function.comp_def] at hbase
  refine hbase.trans (List.sum_le_sum ?_)
  intro p hp
  exact norm_exp_smul_sub_le _ _ (h p hp).2.1 (h p hp).2.2 (h p hp).1

end Giallar
