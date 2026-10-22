module
public import Mathlib
public import ForMathlib.GroupTheory.Coxeter.Realization.Positivity

public section

/-! Semantic home: ForMathlib.GroupTheory.Coxeter.Realization.Faithful. Source spans: Tits:13, Tits:14.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.TitsSpace
open Module
universe u v
variable {I : Type u} [Fintype I] (M : CoxeterMatrix I)
variable {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

/-- Faithfulness persists in the actual nondegenerate extension. -/
theorem extendedAction_injective : Function.Injective (extendedAction M cs) := by
  intro w z h
  apply action_injective M cs
  ext v i
  have hv := congrArg (fun g : Extended M ≃ₗ[ℝ] Extended M => (g (v, 0)).1 i) h
  simpa only [extendedAction_restrict] using hv

@[simp] theorem extendedForm_root_self (i : I) :
    extendedForm M (extendedRoot M i) (extendedRoot M i) = 2 := by
  rw [extendedForm_roots, M.diagonal]
  norm_num

@[simp] theorem extendedAction_simple_eq (i : I) :
    extendedAction M cs (cs.simple i) = Module.reflection (extendedForm_root_self M i) := by
  apply LinearEquiv.ext
  intro v
  rw [extendedAction_simple, Module.reflection_apply]

/-- A rank-one element of the actual extended action is an involution. -/
theorem involution_of_moving_rank_one (w : W)
    (hr : Module.finrank ℝ (LinearMap.range
      ((extendedAction M cs w).toLinearMap - LinearMap.id)) = 1) : w⁻¹ = w := by
  obtain ⟨e, he, hform⟩ := Realization.orthogonal_finrank_one
    (extendedForm M) (extendedForm_spec M).1 (extendedForm_spec M).2.1
    (extendedAction M cs w) (extendedAction_preserves M cs w) hr
  have he2 : ((2 / extendedForm M e e) • extendedForm M e) e = 2 := by
    simp only [LinearMap.smul_apply, smul_eq_mul]
    field_simp
  have hw2 : w * w = 1 := by
    apply extendedAction_injective M cs
    apply LinearEquiv.ext
    intro v
    simp only [map_mul, map_one, LinearEquiv.mul_apply, hform]
    change _ = v
    exact Module.involutive_preReflection he2 v
  exact inv_eq_of_mul_eq_one_left hw2

/-- Reflection faithfulness, the difficult converse, proved by length descent.
This avoids assuming the finite-subgroup theorem cited in the manuscript. -/
theorem isReflection_of_moving_rank_one (w : W)
    (hr : Module.finrank ℝ (LinearMap.range
      ((extendedAction M cs w).toLinearMap - LinearMap.id)) = 1) :
    cs.IsReflection w := by
  suffices ∀ n : ℕ, ∀ w : W, cs.length w = n →
      Module.finrank ℝ (LinearMap.range
        ((extendedAction M cs w).toLinearMap - LinearMap.id)) = 1 →
      cs.IsReflection w from this (cs.length w) w rfl hr
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro w hlen hr
    have hwne : w ≠ 1 := by
      intro h
      subst w
      have heq : (extendedAction M cs 1).toLinearMap - LinearMap.id = 0 := by
        apply LinearMap.ext
        intro v
        change (extendedAction M cs 1) v - v = 0
        rw [map_one]
        change v - v = 0
        abel
      rw [heq, LinearMap.range_zero, finrank_bot] at hr
      omega
    have hwinv := involution_of_moving_rank_one M cs w hr
    obtain ⟨i, hi⟩ := cs.exists_rightDescent_of_ne_one hwne
    change cs.length (w * cs.simple i) < cs.length w at hi
    have hleft : cs.length (cs.simple i * w) < cs.length w := by
      have h := cs.length_inv (w * cs.simple i)
      simp only [mul_inv_rev, cs.inv_simple, hwinv] at h
      omega
    by_cases hcomm : cs.simple i * w = w * cs.simple i
    · have hcomm' : extendedAction M cs w * Module.reflection (extendedForm_root_self M i) =
          Module.reflection (extendedForm_root_self M i) * extendedAction M cs w := by
        rw [← extendedAction_simple_eq M cs i, ← map_mul, ← map_mul, hcomm]
      let f : Module.Dual ℝ (Extended M) := (LinearMap.proj i).comp
        (LinearMap.fst ℝ (I → ℝ) (Module.Dual ℝ (LinearMap.ker (form M))))
      have hf : f (extendedRoot M i) = 1 := by simp [f, extendedRoot, root]
      have hfg : f (extendedAction M cs w (extendedRoot M i)) ≤ 0 := by
        have hn := action_root_nonpos_of_descent M cs w i hi i
        simpa only [f, LinearMap.comp_apply, extendedRoot, extendedAction_restrict,
          LinearMap.fst_apply, LinearMap.proj_apply] using hn
      have hneg := Realization.negates_of_commutes_nonpos (extendedForm M)
        (extendedAction M cs w) (extendedAction_preserves M cs w)
        (extendedRoot M i) (extendedForm_root_self M i) hcomm' f hf hfg
      have heq : extendedAction M cs w = extendedAction M cs (cs.simple i) := by
        apply LinearEquiv.ext
        intro v
        rw [extendedAction_simple]
        exact Realization.rank_one_eq_reflection_of_negates (extendedForm M)
          (extendedAction M cs w) (extendedAction_preserves M cs w) hr
          (extendedRoot M i) (extendedForm_root_self M i) hneg v
      rw [extendedAction_injective M cs heq]
      exact cs.isReflection_simple i
    · let z := cs.simple i * w * cs.simple i
      have hzlt : cs.length z < n := by
        have hz := (right_descent_simple_mul_iff cs i i w hcomm).2 hi
        dsimp [z]
        omega
      have hzrank : Module.finrank ℝ (LinearMap.range
          ((extendedAction M cs z).toLinearMap - LinearMap.id)) = 1 := by
        have hc := Realization.finrank_moving_conj (extendedAction M cs w)
          (extendedAction M cs (cs.simple i))
        have hgi : (extendedAction M cs (cs.simple i))⁻¹ = extendedAction M cs (cs.simple i) := by
          rw [← map_inv, cs.inv_simple]
        have heq : extendedAction M cs z =
            extendedAction M cs (cs.simple i) * extendedAction M cs w *
              (extendedAction M cs (cs.simple i))⁻¹ := by
          dsimp [z]
          rw [map_mul, map_mul, hgi]
        rw [heq]
        exact hc.trans hr
      have hz := ih (cs.length z) hzlt z rfl hzrank
      have hc := hz.conj (w := cs.simple i)
      simpa [z, mul_assoc] using hc

end
end KLInvariance.TitsSpace
end


section
namespace KLInvariance.TitsSpace
open Module
universe u v
variable {I : Type u} [Fintype I] (M : CoxeterMatrix I)
variable {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

/-- The other direction of reflection faithfulness for the actual action. -/
theorem moving_rank_one_of_isReflection (w : W) (hw : cs.IsReflection w) :
    Module.finrank ℝ (LinearMap.range
      ((extendedAction M cs w).toLinearMap - LinearMap.id)) = 1 := by
  obtain ⟨z, i, rfl⟩ := hw
  have hc := Realization.finrank_moving_conj (extendedAction M cs (cs.simple i))
    (extendedAction M cs z)
  have heq : extendedAction M cs (z * cs.simple i * z⁻¹) =
      extendedAction M cs z * extendedAction M cs (cs.simple i) *
        (extendedAction M cs z)⁻¹ := by rw [map_mul, map_mul, map_inv]
  rw [heq, hc, extendedAction_simple_eq]
  exact Realization.finrank_reflection_sub_id _ _ _

theorem reflectionFaithful (w : W) :
    Module.finrank ℝ (LinearMap.range
      ((extendedAction M cs w).toLinearMap - LinearMap.id)) = 1 ↔ cs.IsReflection w :=
  ⟨isReflection_of_moving_rank_one M cs w, moving_rank_one_of_isReflection M cs w⟩

@[simp] theorem dominant_action_root (w : W) (i : I) :
    dominant M (extendedAction M cs w (extendedRoot M i)) =
      ∑ k, action M cs w (root i) k := by
  simp [extendedRoot, extendedAction_restrict, dominant]

/-- Strict dominant sign, not merely closed-cone positivity. -/
theorem dominant_pos_iff_ascent (w : W) (i : I) :
    0 < dominant M (extendedAction M cs w (extendedRoot M i)) ↔
      cs.length w < cs.length (w * cs.simple i) := by
  classical
  rw [dominant_action_root]
  rcases cs.length_mul_simple w i with h | h
  · have ha := action_root_nonneg_of_ascent M cs w i h
    have hv : action M cs w (root i) ≠ 0 := by
      apply (action M cs w).map_ne_zero_iff.mpr
      intro hz
      have hz' := congrFun hz i
      simp [root] at hz'
    have hex : ∃ k, 0 < action M cs w (root i) k := by
      by_contra! hn
      apply hv
      funext k
      exact le_antisymm (hn k) (ha k)
    have hs : 0 < ∑ k, action M cs w (root i) k := by
      apply (Finset.sum_pos_iff_of_nonneg (fun k _ => ha k)).mpr
      obtain ⟨k, hk⟩ := hex
      exact ⟨k, Finset.mem_univ _, hk⟩
    exact iff_of_true hs (by omega)
  · have hn := action_root_nonpos_of_descent M cs w i (by omega)
    have hs : ∑ k, action M cs w (root i) k ≤ 0 := Finset.sum_nonpos (fun k _ => hn k)
    exact iff_of_false (by linarith) (by omega)

/-- The strictly dominant linear form in the convention `(w ρ)(αᵢ)=ρ(w⁻¹αᵢ)`
has exactly the source manuscript's left-ascent sign. -/
theorem dominant_dual_pos_iff_left_ascent (w : W) (i : I) :
    0 < dominant M (extendedAction M cs w⁻¹ (extendedRoot M i)) ↔
      cs.length w < cs.length (cs.simple i * w) := by
  rw [dominant_pos_iff_ascent, cs.length_inv]
  have h : cs.length (w⁻¹ * cs.simple i) = cs.length (cs.simple i * w) := by
    rw [← cs.length_inv (cs.simple i * w)]
    simp
  rw [h]

end
end KLInvariance.TitsSpace
end

end OAI
