module
public import Mathlib
public import ForMathlib.GroupTheory.Coxeter.Parabolic.Support
public import ForMathlib.GroupTheory.Coxeter.Realization.Tits

public section

/-! Semantic home: ForMathlib.GroupTheory.Coxeter.Realization.Positivity. Source spans: Tits:10, Tits:11.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.TitsSpace
open CoxeterSystem Polynomial Polynomial.Chebyshev
universe u v
variable {I : Type u} [klPreservedInstance5 : Fintype I] (M : CoxeterMatrix I)
variable {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

@[expose] def rootCoeff (i j : I) (n : ℤ) : ℝ :=
  (S ℝ n).eval (2 * Real.cos (Real.pi / M i j))

include klPreservedInstance5 in
@[simp] theorem rootCoeff_zero (i j : I) : rootCoeff M i j 0 = 1 := by
  have _ := klPreservedInstance5
  simp [rootCoeff]
include klPreservedInstance5 in
@[simp] theorem rootCoeff_neg_one (i j : I) : rootCoeff M i j (-1) = 0 := by
  have _ := klPreservedInstance5
  simp [rootCoeff]

include klPreservedInstance5 in
theorem rootCoeff_succ (i j : I) (n : ℤ) :
    rootCoeff M i j (n + 1) =
      (2 * Real.cos (Real.pi / M i j)) * rootCoeff M i j n - rootCoeff M i j (n-1) := by
  have _ := klPreservedInstance5
  simp [rootCoeff, S_add_one]

include klPreservedInstance5 in
@[simp] theorem gram_diag (i : I) : gram M i i = 2 := by
  have _ := klPreservedInstance5
  simp [gram]

/-- Exact rank-two root formula, including the infinite pairing. -/
theorem alternating_root (i j : I) (n : ℕ) :
    action M cs (cs.wordProd (alternatingWord i j n)) (root i) =
      if Even n then
        rootCoeff M i j n • root i + rootCoeff M i j ((n : ℤ)-1) • root j
      else rootCoeff M i j ((n : ℤ)-1) • root i + rootCoeff M i j n • root j := by
  induction n with
  | zero => simp [alternatingWord]
  | succ n ih =>
    rw [alternatingWord_succ', cs.wordProd_cons, map_mul, LinearEquiv.mul_apply, ih]
    have hrec := rootCoeff_succ M i j (n : ℤ)
    have hsymm : gram M j i = gram M i j := by simp [gram, M.symmetric j i]
    by_cases hn : Even n
    · simp only [hn, ite_true, Nat.even_add_one, not_true_eq_false, ite_false]
      rw [action_simple]
      simp only [map_add, map_smul, normal_root, gram_diag, hsymm]
      push_cast
      rw [show (n : ℤ) + 1 - 1 = n by omega, hrec]
      simp only [gram]
      module
    · simp only [hn, ite_false, Nat.even_add_one, not_false_eq_true, ite_true]
      rw [action_simple]
      simp only [map_add, map_smul, normal_root, gram_diag]
      push_cast
      rw [show (n : ℤ) + 1 - 1 = n by omega, hrec]
      simp only [gram]
      module

/-- For a reduced alternating word followed by the other generator, both
rank-two coefficients are nonnegative. -/
theorem rootCoeff_nonneg (i j : I) {n : ℤ} (hn : -1 ≤ n)
    (hm : M i j = 0 ∨ n + 1 ≤ (M i j : ℤ)) (hij : i ≠ j) :
    0 ≤ rootCoeff M i j n := by
  rcases hm with hm | hm
  · simp only [rootCoeff, hm, Nat.cast_zero, div_zero, Real.cos_zero, mul_one, S_eval_two]
    exact_mod_cast (by omega : (0 : ℤ) ≤ n + 1)
  · by_cases hn0 : n = -1
    · simp [hn0]
    have hn1 : 0 < n + 1 := by omega
    have hMpos : (0 : ℝ) < M i j := by exact_mod_cast (by omega : 0 < M i j)
    have hM2 : 2 ≤ M i j := by
      have := M.off_diagonal i j hij
      omega
    let θ : ℝ := Real.pi / M i j
    have hθpos : 0 < θ := div_pos Real.pi_pos hMpos
    have hθlt : θ < Real.pi := by
      dsimp [θ]
      apply (div_lt_iff₀ hMpos).2
      have : (2 : ℝ) ≤ M i j := by exact_mod_cast hM2
      nlinarith [Real.pi_pos]
    have hsin := Real.sin_pos_of_pos_of_lt_pi hθpos hθlt
    have heq := S_two_mul_real_cos θ n
    have hargpos : 0 ≤ ((n : ℝ) + 1) * θ := by
      have : (0 : ℝ) < (n : ℝ) + 1 := by exact_mod_cast hn1
      positivity
    have hargle : ((n : ℝ) + 1) * θ ≤ Real.pi := by
      dsimp [θ]
      rw [← mul_div_assoc]
      apply (div_le_iff₀ hMpos).2
      have : (n : ℝ) + 1 ≤ M i j := by exact_mod_cast hm
      nlinarith [Real.pi_pos]
    have hs := Real.sin_nonneg_of_nonneg_of_le_pi hargpos hargle
    change 0 ≤ (S ℝ n).eval (2 * Real.cos θ)
    nlinarith [heq]
end
end KLInvariance.TitsSpace
end


section
namespace KLInvariance.TitsSpace
open CoxeterSystem
universe u v
variable {I : Type u} [klPreservedInstance6 : Fintype I] (M : CoxeterMatrix I)
variable {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

include klPreservedInstance6 in
@[simp] theorem root_nonneg (i k : I) : 0 ≤ root i k := by
  have _ := klPreservedInstance6
  classical
  simp only [root, Pi.single_apply]
  split_ifs <;> norm_num

/-- Positivity of a rank-two reduced tail after an already positive prefix. -/
theorem pair_image_nonneg (u : W) {i j : I} (hij : i ≠ j)
    (hi : ∀ k, 0 ≤ action M cs u (root i) k)
    (hj : ∀ k, 0 ≤ action M cs u (root j) k)
    {ω : List I} (hJ : ∀ k ∈ ω, k = i ∨ k = j)
    (hred : cs.IsReduced (ω ++ [i])) :
    ∀ k, 0 ≤ action M cs (u * cs.wordProd ω) (root i) k := by
  have heq := ParabolicSupport.reduced_pair_eq_alternating cs hij hJ hred
  have hbound := ParabolicSupport.alternating_length_bound cs hij hJ hred
  have hn : 0 ≤ rootCoeff M i j (ω.length : ℤ) :=
    rootCoeff_nonneg M i j (by omega) (by rcases hbound with h|h; exact Or.inl h; right; omega) hij
  have hn' : 0 ≤ rootCoeff M i j ((ω.length : ℤ)-1) :=
    rootCoeff_nonneg M i j (by omega) (by rcases hbound with h|h; exact Or.inl h; right; omega) hij
  intro k
  rw [map_mul, LinearEquiv.mul_apply, heq, alternating_root]
  split_ifs
  all_goals
    simp only [map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg (by assumption) (by exact hi k))
      (mul_nonneg (by assumption) (by first | exact hi k | exact hj k))

/-- The genuine Tits root-sign theorem for ascents, proved from exchange,
minimal parabolic cosets and the rank-two trigonometric formulas. -/
theorem action_root_nonneg_of_ascent (w : W) (i : I)
    (hasc : cs.length (w * cs.simple i) = cs.length w + 1) :
    ∀ k, 0 ≤ action M cs w (root i) k := by
  suffices ∀ n : ℕ, ∀ w : W, cs.length w = n → ∀ i : I,
      cs.length (w * cs.simple i) = cs.length w + 1 →
      ∀ k, 0 ≤ action M cs w (root i) k by
    exact this (cs.length w) w rfl i hasc
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro w hwlen i hasc
    by_cases hw : w = 1
    · subst w
      simp
    obtain ⟨j, hj⟩ := cs.exists_rightDescent_of_ne_one hw
    change cs.length (w * cs.simple j) < cs.length w at hj
    have hij : i ≠ j := by rintro rfl; omega
    obtain ⟨u, v, hv, huv, hlen, huasc, hmul⟩ :=
      ParabolicSupport.exists_length_additive_decomposition cs ({i, j} : Set I) w
    have himem : i ∈ ({i, j} : Set I) := by simp
    have hjmem : j ∈ ({i, j} : Set I) := by simp
    have hult : cs.length u < n := by
      have h := hmul j hjmem
      omega
    have hui := ih (cs.length u) hult u rfl i (huasc i himem)
    have huj := ih (cs.length u) hult u rfl j (huasc j hjmem)
    obtain ⟨ω, hJ, hω, hprod⟩ := ParabolicSupport.exists_reduced_word cs ({i,j} : Set I) hv
    have hvi : cs.length (v * cs.simple i) = cs.length v + 1 := by
      have h := hmul i himem
      omega
    have hωi : cs.IsReduced (ω ++ [i]) := by
      change cs.length (cs.wordProd (ω ++ [i])) = (ω ++ [i]).length
      simp only [cs.wordProd_append, cs.wordProd_singleton, hprod, List.length_append,
        List.length_singleton]
      rw [hvi, ← hprod, hω.eq]
    have hJ' : ∀ k ∈ ω, k = i ∨ k = j := by simpa using hJ
    rw [huv, ← hprod]
    exact pair_image_nonneg M cs u hij hui huj hJ' hωi

@[simp] theorem action_simple_root (i : I) : action M cs (cs.simple i) (root i) = -root i := by
  rw [action_simple, normal_root, gram_diag]
  module

/-- Descents carry a simple root into the negative cone. -/
theorem action_root_nonpos_of_descent (w : W) (i : I)
    (hdesc : cs.length (w * cs.simple i) < cs.length w) :
    ∀ k, action M cs w (root i) k ≤ 0 := by
  have hasc : cs.length ((w * cs.simple i) * cs.simple i) = cs.length (w * cs.simple i) + 1 := by
    rcases cs.length_mul_simple w i with h|h
    · omega
    · simpa [mul_assoc] using h.symm
  have h := action_root_nonneg_of_ascent M cs (w * cs.simple i) i hasc
  simpa only [map_mul, LinearEquiv.mul_apply, action_simple_root, map_neg,
    Pi.neg_apply, neg_nonneg] using h

/-- Faithfulness of the actual ordinary Tits action, not an added axiom. -/
theorem action_injective : Function.Injective (action M cs) := by
  apply (MonoidHom.ker_eq_bot_iff _).1
  apply (Subgroup.eq_bot_iff_forall _).2
  intro w hw
  by_contra hne
  obtain ⟨i, hi⟩ := cs.exists_rightDescent_of_ne_one hne
  have h := action_root_nonpos_of_descent M cs w i hi i
  have hw' : action M cs w = 1 := hw
  rw [hw'] at h
  norm_num [root] at h
end
end KLInvariance.TitsSpace
end

end OAI
