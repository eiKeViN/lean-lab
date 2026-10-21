import Mathlib

/-! Semantic home: ForMathlib.LinearAlgebra.BilinearForm.NondegenerateExtension. Source spans: Tits:6.
See migration.json and MIGRATION.md for exact provenance.
Nondegenerate extension of a real symmetric bilinear form by the dual of its radical, with the minimal dimension bound. No reflection group is assumed. -/

namespace OAI

section
namespace KLInvariance.Realization
universe u
variable {V : Type u} [AddCommGroup V] [Module ℝ V]


abbrev Extension (B : LinearMap.BilinForm ℝ V) := V × Module.Dual ℝ (LinearMap.ker B)

noncomputable def extensionForm (B : LinearMap.BilinForm ℝ V)
    (p : V →ₗ[ℝ] LinearMap.ker B) : LinearMap.BilinForm ℝ (Extension B) where
  toFun x :=
    { toFun := fun y => B x.1 y.1 + x.2 (p y.1) + y.2 (p x.1)
      map_add' := by intro y z; simp [map_add]; ring
      map_smul' := by intro t y; simp [map_smul]; ring }
  map_add' := by
    intro x y
    apply LinearMap.ext
    intro z
    change B (x.1 + y.1) z.1 + (x.2 + y.2) (p z.1) + z.2 (p (x.1 + y.1)) = _
    simp [map_add]
    ring
  map_smul' := by
    intro t x
    apply LinearMap.ext
    intro z
    change B (t • x.1) z.1 + (t • x.2) (p z.1) + z.2 (p (t • x.1)) = _
    simp [map_smul]
    ring

@[simp] theorem extensionForm_apply (B : LinearMap.BilinForm ℝ V)
    (p : V →ₗ[ℝ] LinearMap.ker B) (x y : Extension B) :
    extensionForm B p x y = B x.1 y.1 + x.2 (p y.1) + y.2 (p x.1) := rfl

@[simp] theorem extensionForm_inl (B : LinearMap.BilinForm ℝ V)
    (p : V →ₗ[ℝ] LinearMap.ker B) (v w : V) :
    extensionForm B p (v, 0) (w, 0) = B v w := by simp

theorem extensionForm_symm (B : LinearMap.BilinForm ℝ V) (hB : B.IsSymm)
    (p : V →ₗ[ℝ] LinearMap.ker B) : (extensionForm B p).IsSymm := by
  constructor
  intro x y
  simp only [extensionForm_apply]
  rw [hB.eq x.1 y.1]
  ring

theorem extensionForm_nondegenerate (B : LinearMap.BilinForm ℝ V)
    (hB : B.IsSymm) (p : V →ₗ[ℝ] LinearMap.ker B)
    (hp : ∀ k : LinearMap.ker B, p k.val = k) : (extensionForm B p).Nondegenerate := by
  have hf : ∀ x : Extension B, (∀ y, extensionForm B p x y = 0) → x = 0 := by
    rintro ⟨v, φ⟩ hx
    have hpv : p v = 0 := by
      apply (Module.forall_dual_apply_eq_zero_iff ℝ (p v)).mp
      intro ψ
      simpa using hx (0, ψ)
    have hφ : φ = 0 := by
      ext k
      have hbk : B k.val = 0 := k.property
      have hvk : B v k.val = 0 := by
        rw [hB.eq v k.val, hbk]
        rfl
      simpa [hvk, hp k, hpv] using hx (k.val, 0)
    have hbv : v ∈ LinearMap.ker B := by
      change B v = 0
      ext w
      simpa [hφ, hpv] using hx (w, 0)
    have hv : v = 0 := by
      have h := hp ⟨v, hbv⟩
      rw [hpv] at h
      exact (congrArg Subtype.val h).symm
    simp [hv, hφ]
  exact ⟨hf, fun x hx => hf x (fun y => by
    rw [(extensionForm_symm B hB p).eq]
    exact hx y)⟩

theorem exists_minimal_nondegenerate_extension (B : LinearMap.BilinForm ℝ V)
    (hB : B.IsSymm) :
    ∃ C : LinearMap.BilinForm ℝ (Extension B), C.IsSymm ∧ C.Nondegenerate ∧
      ∀ v w, C (v, 0) (w, 0) = B v w := by
  obtain ⟨Q, hQ⟩ := (LinearMap.ker B).exists_isCompl
  let p := (LinearMap.ker B).projectionOnto Q hQ
  exact ⟨extensionForm B p, extensionForm_symm B hB p,
    extensionForm_nondegenerate B hB p (Submodule.projectionOnto_apply_left hQ),
    extensionForm_inl B p⟩

theorem extension_finrank [FiniteDimensional ℝ V] (B : LinearMap.BilinForm ℝ V) :
    Module.finrank ℝ (Extension B) = Module.finrank ℝ V + Module.finrank ℝ (LinearMap.ker B) := by
  rw [Module.finrank_prod, Subspace.dual_finrank_eq]


theorem extension_dimension_minimal [FiniteDimensional ℝ V]
    {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    (B : LinearMap.BilinForm ℝ V) (C : LinearMap.BilinForm ℝ E)
    (hC : C.Nondegenerate) (i : V →ₗ[ℝ] E) (hi : Function.Injective i)
    (hform : ∀ v w, C (i v) (i w) = B v w) :
    Module.finrank ℝ V + Module.finrank ℝ (LinearMap.ker B) ≤ Module.finrank ℝ E := by
  let f : LinearMap.ker B →ₗ[ℝ] E := i.comp (LinearMap.ker B).subtype
  have hf : Function.Injective f := hi.comp Subtype.val_injective
  have hsub : LinearMap.range i ≤ C.orthogonal (LinearMap.range f) := by
    rintro _ ⟨v, rfl⟩
    apply LinearMap.BilinForm.mem_orthogonal_iff.mpr
    rintro _ ⟨k, rfl⟩
    change C (i k.val) (i v) = 0
    rw [hform, show B k.val = 0 from k.property]
    rfl
  have hd := Submodule.finrank_mono hsub
  rw [LinearMap.finrank_range_of_inj hi, LinearMap.BilinForm.finrank_orthogonal hC,
    LinearMap.finrank_range_of_inj hf] at hd
  have hk : Module.finrank ℝ (LinearMap.ker B) ≤ Module.finrank ℝ E := by
    rw [← LinearMap.finrank_range_of_inj hf]
    exact Submodule.finrank_le _
  omega

end KLInvariance.Realization
end

end OAI
