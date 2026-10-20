import Mathlib
import OAI.GroupTheory.Coxeter.Realization.Positivity

/-! Semantic home: OAI.GroupTheory.Coxeter.Realization.Cotangent. Source spans: Tits:15.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.Cotangent
open Module
universe u v
variable {I : Type u} (M : CoxeterMatrix I)
noncomputable section

def root (i : I) : I → ℝ := fun j => -2 * Real.cos (Real.pi / M i j)

lemma normal_root (i : I) : (LinearMap.proj i : (I → ℝ) →ₗ[ℝ] ℝ) (root M i) = 2 := by
  simp [root]

def simple (i : I) : (I → ℝ) ≃ₗ[ℝ] (I → ℝ) := Module.reflection (normal_root M i)

theorem simple_liftable : M.IsLiftable (simple M) := by
  intro i j
  by_cases hij : i = j
  · subst j
    rw [M.diagonal, pow_one]
    apply LinearEquiv.ext
    intro v
    exact Module.involutive_reflection (normal_root M i) v
  by_cases hm0 : M i j = 0
  · rw [hm0, pow_zero]
  have hm2 : 2 ≤ M i j := by
    have := M.off_diagonal i j hij
    omega
  apply Realization.geometric_reflection_relation (normal_root M i) (normal_root M j)
    (M i j) hm2
  · simp [root, M.symmetric j i]
  · rfl

def action {W : Type v} [Group W] (cs : CoxeterSystem M W) :
    W →* ((I → ℝ) ≃ₗ[ℝ] (I → ℝ)) := cs.lift ⟨simple M, simple_liftable M⟩

@[simp] theorem action_simple {W : Type v} [Group W] (cs : CoxeterSystem M W)
    (i : I) (l : I → ℝ) :
    action M cs (cs.simple i) l = l - l i • root M i := by
  rw [action, cs.lift_apply_simple]
  rfl

section Finite
variable [Fintype I] {W : Type v} [Group W] (cs : CoxeterSystem M W)

lemma dot_root (l : I → ℝ) (i : I) : l ⬝ᵥ TitsSpace.root i = l i := by
  classical
  simp [TitsSpace.root, dotProduct, Pi.single_apply]

lemma root_dot (i : I) (v : I → ℝ) :
    root M i ⬝ᵥ v = TitsSpace.normal M i v := by
  simp [root, TitsSpace.normal, TitsSpace.gram, dotProduct]

lemma simple_pairing (i : I) (l v : I → ℝ) :
    (action M cs (cs.simple i) l) ⬝ᵥ (TitsSpace.action M cs (cs.simple i) v) =
      l ⬝ᵥ v := by
  rw [action_simple, TitsSpace.action_simple]
  simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul,
    dot_root, root_dot]
  have hd : root M i i = 2 := by simp [root]
  rw [hd]
  simp only [smul_eq_mul]
  ring

theorem pairing (w : W) (l v : I → ℝ) :
    (action M cs w l) ⬝ᵥ (TitsSpace.action M cs w v) = l ⬝ᵥ v := by
  obtain ⟨ω, rfl⟩ := cs.wordProd_surjective w
  induction ω generalizing l v with
  | nil => simp
  | cons i ω ih =>
    rw [cs.wordProd_cons, map_mul, map_mul, LinearEquiv.mul_apply,
      LinearEquiv.mul_apply, simple_pairing, ih]

theorem action_injective : Function.Injective (action M cs) := by
  apply (injective_iff_map_eq_one _).2
  intro w hw
  apply TitsSpace.action_injective M cs
  rw [map_one]
  apply LinearEquiv.ext
  intro v
  apply dotProduct_eq
  intro l
  have h := pairing M cs w l v
  rw [hw] at h
  simpa [dotProduct_comm] using h
end Finite
end
end KLInvariance.Cotangent
end

end OAI
