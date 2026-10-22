module
public import Mathlib
public import ForMathlib.GroupTheory.Coxeter.Realization.Geometric
public import ForMathlib.LinearAlgebra.BilinearForm.NondegenerateExtension

public section

/-! Semantic home: ForMathlib.GroupTheory.Coxeter.Realization.Tits. Source spans: Tits:5, Tits:7.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.TitsSpace
open Module
universe u v
variable {I : Type u} [Fintype I] (M : CoxeterMatrix I)
noncomputable section


@[expose] def gram (i j : I) : ℝ := -2 * Real.cos (Real.pi / M i j)

@[expose] def root (i : I) : I → ℝ := by
  classical
  exact Pi.single i 1

@[expose] def normal (i : I) : Module.Dual ℝ (I → ℝ) :=
  ∑ j, gram M i j • LinearMap.proj j

@[expose] def form : LinearMap.BilinForm ℝ (I → ℝ) :=
  ∑ i, (LinearMap.proj i).smulRight (normal M i)

@[simp] theorem normal_root (i j : I) : normal M i (root j) = gram M i j := by
  classical
  simp only [normal, root, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.proj_apply, smul_eq_mul]
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hbj
    simp [hbj]
  · simp

@[simp] theorem form_root (i : I) (v : I → ℝ) : form M (root i) v = normal M i v := by
  classical
  simp [form, root, LinearMap.sum_apply]

theorem form_symm : (form M).IsSymm := by
  constructor
  intro v w
  simp only [form, normal, LinearMap.sum_apply, LinearMap.smulRight_apply,
    LinearMap.smul_apply, LinearMap.proj_apply, smul_eq_mul]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [show gram M j i = gram M i j by simp only [gram, M.symmetric j i]]
  ring

theorem form_roots (i j : I) : form M (root i) (root j) =
    -2 * Real.cos (Real.pi / M i j) := by simp [gram]

theorem root_linearIndependent : LinearIndependent ℝ (root (I := I)) := by
  classical
  have heq : (root (I := I)) = (Pi.basisFun ℝ I : I → I → ℝ) := by
    funext i
    simp [root, Pi.basisFun_apply]
  rw [heq]
  exact (Pi.basisFun ℝ I).linearIndependent

/-- A concrete action on the ordinary geometric root space over ℝ. Its
faithfulness and the root-sign theorem are still required for the main proof. -/
@[expose] def action {W : Type v} [Group W] (cs : CoxeterSystem M W) :
    W →* ((I → ℝ) ≃ₗ[ℝ] (I → ℝ)) :=
  Realization.geometricAction cs (form M) root (form_roots M)

@[simp] theorem action_simple {W : Type v} [Group W] (cs : CoxeterSystem M W)
    (i : I) (v : I → ℝ) :
    action M cs (cs.simple i) v = v - normal M i v • root i := by
  simp [action, Realization.geometricAction_simple, Realization.geometricSimple,
    Module.reflection_apply]

theorem action_preserves {W : Type v} [Group W] (cs : CoxeterSystem M W)
    (w : W) (v z : I → ℝ) : form M (action M cs w v) (action M cs w z) = form M v z :=
  Realization.geometricAction_preserves cs (form M) root (form_roots M) (form_symm M) w v z
end
end KLInvariance.TitsSpace
end


section
namespace KLInvariance.TitsSpace
open Module
universe u v
variable {I : Type u} [Fintype I] (M : CoxeterMatrix I)
noncomputable section

abbrev Extended := Realization.Extension (form M)

@[expose] def extendedForm : LinearMap.BilinForm ℝ (Extended M) :=
  Classical.choose (Realization.exists_minimal_nondegenerate_extension (form M) (form_symm M))

theorem extendedForm_spec : (extendedForm M).IsSymm ∧ (extendedForm M).Nondegenerate ∧
    ∀ v w, extendedForm M (v, 0) (w, 0) = form M v w :=
  Classical.choose_spec (Realization.exists_minimal_nondegenerate_extension (form M) (form_symm M))

@[expose] def extendedRoot (i : I) : Extended M := (root i, 0)

@[simp] theorem extendedForm_roots (i j : I) :
    extendedForm M (extendedRoot M i) (extendedRoot M j) =
      -2 * Real.cos (Real.pi / M i j) := by
  rw [extendedRoot, extendedRoot, (extendedForm_spec M).2.2, form_roots]

theorem extendedRoot_linearIndependent : LinearIndependent ℝ (extendedRoot M) := by
  exact (root_linearIndependent (I := I)).map'
    (LinearMap.inl ℝ (I → ℝ) (Module.Dual ℝ (LinearMap.ker (form M))))
    (LinearMap.ker_eq_bot.mpr LinearMap.inl_injective)

/-- Both roots and coroots are independent in the actual minimal extension. -/
theorem extendedNormal_linearIndependent :
    LinearIndependent ℝ (fun i => extendedForm M (extendedRoot M i)) :=
  (extendedRoot_linearIndependent M).map' (extendedForm M) (extendedForm_spec M).2.1.ker_eq_bot

@[expose] def extendedAction {W : Type v} [Group W] (cs : CoxeterSystem M W) :
    W →* (Extended M ≃ₗ[ℝ] Extended M) :=
  Realization.geometricAction cs (extendedForm M) (extendedRoot M) (extendedForm_roots M)

theorem extendedAction_preserves {W : Type v} [Group W] (cs : CoxeterSystem M W)
    (w : W) (v z : Extended M) :
    extendedForm M (extendedAction M cs w v) (extendedAction M cs w z) = extendedForm M v z :=
  Realization.geometricAction_preserves cs (extendedForm M) (extendedRoot M)
    (extendedForm_roots M) (extendedForm_spec M).1 w v z

@[simp] theorem extendedAction_simple {W : Type v} [Group W] (cs : CoxeterSystem M W)
    (i : I) (v : Extended M) :
    extendedAction M cs (cs.simple i) v =
      v - extendedForm M (extendedRoot M i) v • extendedRoot M i := by
  simp only [extendedAction, Realization.geometricAction_simple,
    Realization.geometricSimple, Module.reflection_apply]

/-- The extended action genuinely restricts to the ordinary geometric action.
Injectivity of that latter action is an outstanding obligation, not a hypothesis
hidden in the construction of this extension. -/
theorem extendedAction_restrict {W : Type v} [Group W] (cs : CoxeterSystem M W)
    (w : W) (v : I → ℝ) :
    extendedAction M cs w (v, 0) = (action M cs w v, 0) := by
  obtain ⟨ω, rfl⟩ := cs.wordProd_surjective w
  induction ω generalizing v with
  | nil => simp
  | cons i ω ih =>
    rw [cs.wordProd_cons, map_mul, map_mul]
    simp only [LinearEquiv.mul_apply, ih, extendedAction_simple, action_simple]
    change (action M cs (cs.wordProd ω) v, 0) -
      extendedForm M (root i, 0) (action M cs (cs.wordProd ω) v, 0) • (root i, 0) = _
    rw [(extendedForm_spec M).2.2, form_root]
    ext <;> simp

theorem extended_finrank : Module.finrank ℝ (Extended M) =
    Fintype.card I + Module.finrank ℝ (LinearMap.ker (form M)) := by
  rw [Realization.extension_finrank, Module.finrank_pi]


@[expose] def dominant : Module.Dual ℝ (Extended M) :=
  (∑ i : I, LinearMap.proj i).comp
    (LinearMap.fst ℝ (I → ℝ) (Module.Dual ℝ (LinearMap.ker (form M))))

@[simp] theorem dominant_root (i : I) : dominant M (extendedRoot M i) = 1 := by
  classical
  simp [dominant, extendedRoot, root]

end
end KLInvariance.TitsSpace
end

end OAI
