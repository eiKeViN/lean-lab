import Mathlib
import ForMathlib.LinearAlgebra.Reflection.Bilinear

/-! Semantic home: ForMathlib.GroupTheory.Coxeter.Realization.Geometric. Source spans: Tits:4.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.Realization
open Module
universe u v z
variable {I : Type u} {W : Type v} [Group W] {M : CoxeterMatrix I}
variable (cs : CoxeterSystem M W)
variable {V : Type z} [AddCommGroup V] [Module ℝ V]
variable (B : LinearMap.BilinForm ℝ V) (α : I → V)
variable (hα : ∀ i j, B (α i) (α j) = -2 * Real.cos (Real.pi / M i j))

include hα

lemma simple_normal_value (i : I) : B (α i) (α i) = 2 := by
  rw [hα]
  simp

noncomputable def geometricSimple (i : I) : V ≃ₗ[ℝ] V :=
  Module.reflection (simple_normal_value B α hα i)

theorem geometricSimple_liftable : M.IsLiftable (geometricSimple B α hα) := by
  intro i j
  by_cases hij : i = j
  · subst j
    rw [M.diagonal, pow_one]
    ext v
    exact Module.involutive_reflection (simple_normal_value B α hα i) v
  by_cases hm0 : M i j = 0
  · rw [hm0, pow_zero]
  have hm2 : 2 ≤ M i j := by
    have := M.off_diagonal i j hij
    omega
  exact geometric_reflection_relation (simple_normal_value B α hα i)
    (simple_normal_value B α hα j) (M i j) hm2 (hα i j)
    (by rw [hα j i, M.symmetric j i])

/-- The genuine geometric reflection action. Each relation has been proved;
this definition does not presuppose a faithful representation. -/
noncomputable def geometricAction : W →* (V ≃ₗ[ℝ] V) :=
  cs.lift ⟨geometricSimple B α hα, geometricSimple_liftable B α hα⟩

@[simp] theorem geometricAction_simple (i : I) :
    geometricAction cs B α hα (cs.simple i) = geometricSimple B α hα i :=
  cs.lift_apply_simple (geometricSimple_liftable B α hα) i

theorem geometricSimple_preserves (hs : B.IsSymm) (i : I) (v w : V) :
    B (geometricSimple B α hα i v) (geometricSimple B α hα i w) = B v w := by
  simp only [geometricSimple, Module.reflection_apply, map_sub, map_smul,
    LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
  rw [hs.eq v (α i), simple_normal_value B α hα i]
  ring

theorem geometricAction_preserves (hs : B.IsSymm) (w : W) (v z : V) :
    B (geometricAction cs B α hα w v) (geometricAction cs B α hα w z) = B v z := by
  obtain ⟨ω, rfl⟩ := cs.wordProd_surjective w
  induction ω with
  | nil => simp
  | cons i ω ih =>
    rw [cs.wordProd_cons, map_mul]
    simp only [LinearEquiv.mul_apply, geometricAction_simple]
    rw [geometricSimple_preserves B α hα hs, ih]

end KLInvariance.Realization
end

end OAI
