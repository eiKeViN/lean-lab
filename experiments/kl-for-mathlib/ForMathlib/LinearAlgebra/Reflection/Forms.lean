import Mathlib

/-! Semantic home: ForMathlib.LinearAlgebra.Reflection.Forms. Source spans: Tits:12, Tits:2, Tits:3, Tits:6.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.Realization
open Module
variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Rank of the moving subspace is unchanged by conjugacy. -/
theorem finrank_moving_conj (g h : V ≃ₗ[ℝ] V) :
    Module.finrank ℝ (LinearMap.range ((h * g * h⁻¹).toLinearMap - LinearMap.id)) =
      Module.finrank ℝ (LinearMap.range (g.toLinearMap - LinearMap.id)) := by
  have heq : (h * g * h⁻¹).toLinearMap - LinearMap.id =
      h.toLinearMap.comp ((g.toLinearMap - LinearMap.id).comp h.symm.toLinearMap) := by
    ext v
    simp
  rw [heq, LinearMap.range_comp, LinearMap.range_comp_of_range_eq_top _ h.symm.range,
    h.finrank_map_eq]

/-- An orthogonal rank-one map negating a norm-two vector is its exact reflection. -/
theorem rank_one_eq_reflection_of_negates [FiniteDimensional ℝ V]
    (B : LinearMap.BilinForm ℝ V) (g : V ≃ₗ[ℝ] V)
    (hg : ∀ v w, B (g v) (g w) = B v w)
    (hr : Module.finrank ℝ (LinearMap.range (g.toLinearMap - LinearMap.id)) = 1)
    (e : V) (he : B e e = 2) (hge : g e = -e) :
    ∀ v, g v = Module.preReflection e (B e) v := by
  let d : V →ₗ[ℝ] V := g.toLinearMap - LinearMap.id
  have he0 : e ≠ 0 := by intro h; simp [h] at he
  have hemem : e ∈ LinearMap.range d := by
    refine ⟨(- (1 / 2 : ℝ)) • e, ?_⟩
    change g (- (1 / 2 : ℝ) • e) - (- (1 / 2 : ℝ) • e) = e
    rw [map_smul, hge]
    module
  have hspan : Submodule.span ℝ {e} = LinearMap.range d := by
    apply Submodule.eq_of_le_of_finrank_eq
    · exact Submodule.span_le.mpr (by simpa using hemem)
    · rw [finrank_span_singleton he0]
      exact hr.symm
  intro v
  have hv : d v ∈ Submodule.span ℝ {e} := by rw [hspan]; exact LinearMap.mem_range_self _ v
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hv
  have hgform : g v = v + c • e := by
    change c • e = g v - v at hc
    rw [hc]
    abel
  have hB := hg e v
  rw [hge, hgform] at hB
  simp only [map_neg, LinearMap.neg_apply, map_add, map_smul, he, smul_eq_mul] at hB
  have hc' : c = - B e v := by linarith
  rw [hgform, hc', Module.preReflection_apply, neg_smul, sub_eq_add_neg]

/-- Commutation with a reflection makes its negative eigenspace invariant;
a nonpositive coordinate selects the negative, rather than positive, sign. -/
theorem negates_of_commutes_nonpos
    (B : LinearMap.BilinForm ℝ V) (g : V ≃ₗ[ℝ] V)
    (hg : ∀ v w, B (g v) (g w) = B v w)
    (e : V) (he : B e e = 2)
    (hcomm : g * Module.reflection he = Module.reflection he * g)
    (f : Module.Dual ℝ V) (hfe : f e = 1) (hfg : f (g e) ≤ 0) :
    g e = -e := by
  have h := LinearEquiv.congr_fun hcomm e
  simp only [LinearEquiv.mul_apply, Module.reflection_apply_self, map_neg,
    Module.reflection_apply] at h
  let c : ℝ := B e (g e) / 2
  have hge : g e = c • e := by
    dsimp [c]
    linear_combination (norm := module) (- (1 / 2 : ℝ)) • h
  have hc : c ≤ 0 := by simpa [hge, hfe] using hfg
  have hnorm := hg e e
  rw [hge] at hnorm
  simp only [map_smul, LinearMap.smul_apply, he, smul_eq_mul] at hnorm
  have hc' : c = -1 := by nlinarith [sq_nonneg (c + 1)]
  rw [hge, hc', neg_one_smul]
/-- The moving subspace of a genuine reflection is exactly its root line. -/
theorem range_reflection_sub_id (e : V) (f : Module.Dual ℝ V) (h : f e = 2) :
    LinearMap.range ((Module.reflection h).toLinearMap - LinearMap.id) =
      Submodule.span ℝ {e} := by
  apply le_antisymm
  · rintro z ⟨v, rfl⟩
    apply Submodule.mem_span_singleton.mpr
    refine ⟨-f v, ?_⟩
    simp only [LinearMap.sub_apply, LinearEquiv.coe_coe, LinearMap.id_apply,
      Module.reflection_apply, neg_smul]
    abel
  · apply Submodule.span_le.mpr
    intro z hz
    have hz' : z = e := Set.mem_singleton_iff.mp hz
    rw [hz']
    refine ⟨(- (1 / 2 : ℝ)) • e, ?_⟩
    simp only [LinearMap.sub_apply, LinearEquiv.coe_coe, LinearMap.id_apply,
      Module.reflection_apply, map_smul, h]
    module

theorem finrank_reflection_sub_id (e : V) (f : Module.Dual ℝ V) (h : f e = 2) :
    Module.finrank ℝ (LinearMap.range
      ((Module.reflection h).toLinearMap - LinearMap.id)) = 1 := by
  rw [range_reflection_sub_id]
  apply finrank_span_singleton
  intro he
  simp [he] at h

end KLInvariance.Realization
end


section
namespace KLInvariance.Realization
open Module
variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- An actual rank-one perturbation that preserves a nondegenerate symmetric
form is an orthogonal reflection, not a unipotent transvection. -/
theorem orthogonal_rank_one_form
    (B : LinearMap.BilinForm ℝ V) (hs : B.IsSymm) (hn : B.Nondegenerate)
    (u : V) (hu : u ≠ 0) (f : Module.Dual ℝ V) (hf : f ≠ 0)
    (hg : ∀ v w, B (v + f v • u) (w + f w • u) = B v w) :
    f u = -2 ∧ B u u ≠ 0 ∧
      ∀ v, v + f v • u = Module.preReflection u ((2 / B u u) • B u) v := by
  obtain ⟨v, hv⟩ : ∃ v, f v = 1 := by
    have hex : ∃ w, f w ≠ 0 := by
      by_contra! h
      exact hf (LinearMap.ext h)
    obtain ⟨w, hw⟩ := hex
    exact ⟨(f w)⁻¹ • w, by simp [hw]⟩
  have hz (z : V) (h : f z = 0) : B u z = 0 := by
    have h' := hg v z
    simpa [hv, h, map_add] using h'
  have hprop (z : V) : B u z = f z * B u v := by
    have h := hz (z - f z • v) (by simp [hv])
    exact sub_eq_zero.mp (by simpa [map_sub, map_smul] using h)
  have hc : B u v ≠ 0 := by
    intro h
    apply hu
    exact hn.1 u (fun z => by rw [hprop z, h, mul_zero])
  have hself := hg v v
  simp only [hv, one_smul, map_add, LinearMap.add_apply] at hself
  rw [hs.eq v u] at hself
  have hfu : f u = -2 := by
    rw [hprop u] at hself
    apply (mul_right_cancel₀ hc)
    linarith
  have hne : B u u ≠ 0 := by
    rw [hprop u, hfu]
    exact mul_ne_zero (by norm_num) hc
  refine ⟨hfu, hne, fun z => ?_⟩
  rw [Module.preReflection_apply]
  have heq : ((2 / B u u) • B u) z = -f z := by
    simp only [LinearMap.smul_apply, smul_eq_mul]
    rw [hprop z, hprop u, hfu]
    field_simp [hc]
  rw [heq, neg_smul, sub_neg_eq_add]

/-- This is the rank-one assertion in `bg:realization` stated without a chosen
rank-one normal form. Its conclusion uses the library's actual reflection. -/
theorem orthogonal_finrank_one
    (B : LinearMap.BilinForm ℝ V) (hs : B.IsSymm) (hn : B.Nondegenerate)
    (g : V ≃ₗ[ℝ] V) (hg : ∀ v w, B (g v) (g w) = B v w)
    (hr : Module.finrank ℝ (LinearMap.range (g.toLinearMap - LinearMap.id)) = 1) :
    ∃ u : V, B u u ≠ 0 ∧
      ∀ v, g v = Module.preReflection u ((2 / B u u) • B u) v := by
  let d : V →ₗ[ℝ] V := g.toLinearMap - LinearMap.id
  obtain ⟨e⟩ := nonempty_linearEquiv_of_finrank_eq_one hr
  let u : V := (e 1).val
  let f : Module.Dual ℝ V := e.symm.toLinearMap.comp d.rangeRestrict
  have hu : u ≠ 0 := by
    intro h
    have : e 1 = 0 := Subtype.ext h
    have := e.injective (this.trans e.map_zero.symm)
    norm_num at this
  have hform (v : V) : f v • u = d v := by
    change f v • (e 1).val = d v
    have h := congrArg Subtype.val (e.apply_symm_apply (d.rangeRestrict v))
    have he : e (f v) = f v • e 1 := by
      rw [← map_smul, smul_eq_mul, mul_one]
    rw [show e.symm (d.rangeRestrict v) = f v from rfl, he] at h
    exact h
  have hf : f ≠ 0 := by
    intro h
    obtain ⟨v, hv⟩ := (e 1).property
    have hh := hform v
    rw [h, LinearMap.zero_apply, zero_smul, hv] at hh
    exact hu hh.symm
  have hgform (v : V) : g v = v + f v • u := by
    rw [hform]
    change g v = v + (g v - v)
    abel
  obtain ⟨_, hnonzero, hreflection⟩ := orthogonal_rank_one_form B hs hn u hu f hf
    (fun v w => by rw [← hgform, ← hgform]; exact hg v w)
  exact ⟨u, hnonzero, fun v => (hgform v).trans (hreflection v)⟩
end KLInvariance.Realization
end


section
namespace KLInvariance.Realization
open Module Polynomial.Chebyshev
variable {V : Type*} [AddCommGroup V] [Module ℝ V]

private theorem reflection_pow_even_eq_one
    {α β : V} {f g : Module.Dual ℝ V} (hf : f α = 2) (hg : g β = 2)
    (k : ℕ) (hS : (S ℝ ((k : ℤ) - 1)).eval (f β * g α - 2) = 0) :
    (Module.reflection hf * Module.reflection hg) ^ (2 * k) = 1 := by
  ext v
  rw [Module.reflection_mul_reflection_pow_apply hf hg]
  have h₁ : ((↑(2 * k) : ℤ) - 2) / 2 = (k : ℤ) - 1 := by omega
  have h₂ : ((↑(2 * k) : ℤ) - 1) / 2 = (k : ℤ) - 1 := by omega
  rw [h₁, h₂, hS]
  simp

private theorem reflection_pow_odd_eq_one
    {α β : V} {f g : Module.Dual ℝ V} (hf : f α = 2) (hg : g β = 2)
    (k : ℕ)
    (hS : (S ℝ (k : ℤ)).eval (f β * g α - 2) +
      (S ℝ ((k : ℤ) - 1)).eval (f β * g α - 2) = 0) :
    (Module.reflection hf * Module.reflection hg) ^ (2 * k + 1) = 1 := by
  ext v
  rw [Module.reflection_mul_reflection_pow_apply hf hg]
  have h₀ : (↑(2 * k + 1) : ℤ) / 2 = (k : ℤ) := by omega
  have h₁ : ((↑(2 * k + 1) : ℤ) - 2) / 2 = (k : ℤ) - 1 := by omega
  have h₂ : ((↑(2 * k + 1) : ℤ) - 1) / 2 = (k : ℤ) := by omega
  have h₃ : ((↑(2 * k + 1) : ℤ) - 3) / 2 = (k : ℤ) - 1 := by omega
  rw [h₀, h₁, h₂, h₃, hS]
  simp

/-- If the two simple roots have the exact Tits pairing, the corresponding
linear equivalences satisfy their finite Coxeter relation on the entire
ambient space, not just on the root plane. -/
theorem geometric_reflection_relation
    {α β : V} {f g : Module.Dual ℝ V} (hf : f α = 2) (hg : g β = 2)
    (m : ℕ) (hm : 2 ≤ m)
    (hfg : f β = -2 * Real.cos (Real.pi / m))
    (hgf : g α = -2 * Real.cos (Real.pi / m)) :
    (Module.reflection hf * Module.reflection hg) ^ m = 1 := by
  by_cases hm2 : m = 2
  · subst m
    have hfg0 : f β = 0 := by simpa using hfg
    have hgf0 : g α = 0 := by simpa using hgf
    ext v
    change ((Module.reflection hf * Module.reflection hg) ^ 2) v = v
    simp only [pow_two, LinearEquiv.mul_apply, Module.reflection_apply,
      map_sub, map_smul, hf, hg, hfg0, hgf0, ]
    module
  have hm3 : 2 < m := by omega
  have hmR : (2 : ℝ) < m := by exact_mod_cast hm3
  let θ : ℝ := Real.pi / m
  have hθ : (m : ℝ) * θ = Real.pi := by dsimp [θ]; field_simp
  have hθpos : 0 < θ := div_pos Real.pi_pos (by positivity)
  have hθlt : 2 * θ < Real.pi := by
    dsimp [θ]
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ (show (0 : ℝ) < m by positivity)).2
    nlinarith [Real.pi_pos]
  have hsin : Real.sin (2 * θ) ≠ 0 :=
    ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by positivity) hθlt)
  have ht : f β * g α - 2 = 2 * Real.cos (2 * θ) := by
    rw [hfg, hgf, Real.cos_two_mul]
    dsimp [θ]
    ring
  rcases Nat.even_or_odd m with he | ho
  · obtain ⟨k, hk⟩ := he
    have hm' : m = 2 * k := by omega
    clear hk
    subst m
    apply reflection_pow_even_eq_one hf hg k
    rw [ht]
    have h := S_two_mul_real_cos (2 * θ) ((k : ℤ) - 1)
    have ha : (((k : ℤ) - 1 : ℤ) + 1 : ℝ) * (2 * θ) = Real.pi := by
      push_cast
      push_cast at hθ
      nlinarith [hθ]
    rw [ha, Real.sin_pi] at h
    exact (mul_eq_zero.mp h).resolve_right hsin
  · obtain ⟨k, hk⟩ := ho
    have hm' : m = 2 * k + 1 := by omega
    clear hk
    subst m
    apply reflection_pow_odd_eq_one hf hg k
    rw [ht]
    have h₁ := S_two_mul_real_cos (2 * θ) (k : ℤ)
    have h₂ := S_two_mul_real_cos (2 * θ) ((k : ℤ) - 1)
    have ha : ((k : ℤ) + 1 : ℝ) * (2 * θ) = Real.pi + θ := by
      push_cast
      push_cast at hθ
      nlinarith [hθ]
    have hb : (((k : ℤ) - 1 : ℤ) + 1 : ℝ) * (2 * θ) = Real.pi - θ := by
      push_cast
      push_cast at hθ
      nlinarith [hθ]
    rw [ha] at h₁
    simp only [Real.sin_add, Real.sin_pi, Real.cos_pi, zero_mul, neg_one_mul,
      zero_add] at h₁
    rw [hb, Real.sin_pi_sub] at h₂
    apply (mul_eq_zero.mp (show
      ((S ℝ (k : ℤ)).eval (2 * Real.cos (2 * θ)) +
      (S ℝ ((k : ℤ) - 1)).eval (2 * Real.cos (2 * θ))) *
      Real.sin (2 * θ) = 0 by nlinarith [h₁, h₂])).resolve_right hsin
end KLInvariance.Realization
end


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
