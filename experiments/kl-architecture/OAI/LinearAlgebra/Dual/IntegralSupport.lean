import Mathlib

/-! Semantic home: OAI.LinearAlgebra.Dual.IntegralSupport. Source spans: Support:9, EdgeLocalization:21.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.IntegralSupport

universe ur uv um
variable {R : Type ur} [CommRing R]
  {V : Type uv} [DecidableEq V] {A : V → Type um} [∀ x, AddCommGroup (A x)] [∀ x, Module R (A x)]
  (M : Submodule R (∀ x, A x))

noncomputable def projection (x : V) : M →ₗ[R] A x := (LinearMap.proj x).comp M.subtype

def supported (x : V) : Submodule R M where
  carrier := {m | ∀ y, y ≠ x → m.val y = 0}
  zero_mem' := by intro y hy; rfl
  add_mem' := by intro m n hm hn y hy; exact congrArg₂ (· + ·) (hm y hy) (hn y hy) |>.trans (zero_add _)
  smul_mem' := by intro r m hm y hy; exact congrArg (r • ·) (hm y hy) |>.trans (smul_zero r)

variable (p : R)
  (hcut : ∀ x (m : M), (p • Pi.single x (m.val x)) ∈ M)

noncomputable def cut (x : V) : M →ₗ[R] M := by
  exact ((p • (LinearMap.single R A x).comp (LinearMap.proj x)).domRestrict M).codRestrict M (hcut x)

@[simp] theorem cut_apply (x : V) (m : M) : (cut M p hcut x m).val = p • Pi.single x (m.val x) := rfl

@[simp] theorem cut_self (x : V) (m : M) : (cut M p hcut x m).val x = p • m.val x := by
  simp [cut_apply]

 theorem cut_other (x y : V) (h : y ≠ x) (m : M) : (cut M p hcut x m).val y = 0 := by
  simp [cut_apply,h]

 theorem cut_of_supported (x : V) (m : M) (h : m ∈ supported M x) :
    cut M p hcut x m = p • m := by
  apply Subtype.ext
  funext y
  by_cases hy : y=x
  · subst y; exact cut_self M p hcut x m
  · rw [cut_other M p hcut x y hy]
    change 0 = p • m.val y
    rw [h y hy,smul_zero]

 theorem cut_eq_zero (x : V) (m : M) (h : projection M x m = 0) : cut M p hcut x m = 0 := by
  apply Subtype.ext
  change p • Pi.single x (m.val x) = 0
  change m.val x = 0 at h
  simp [h]

variable [IsDomain R] [∀ x, Module.IsTorsionFree R (A x)] (hp : p ≠ 0)
  (d : M ≃ₗ[R] Module.Dual R M)
  (hbalanced : ∀ x m n, d (cut M p hcut x m) n = d m (cut M p hcut x n))

include hp hbalanced in
/-- The exact integral annihilator, not merely its generic vector space. -/
 theorem supported_iff_annihilates (x : V) (m : M) :
    m ∈ supported M x ↔ ∀ n : M, projection M x n = 0 → d m n = 0 := by
  constructor
  · intro hm n hn
    have hh := hbalanced x m n
    rw [cut_of_supported M p hcut x m hm,cut_eq_zero M p hcut x n hn] at hh
    simpa only [map_smul,LinearMap.smul_apply,map_zero,smul_eq_zero_iff_right hp] using hh
  · intro hm y hy
    have hc : cut M p hcut y m = 0 := by
      apply d.injective
      apply LinearMap.ext
      intro n
      rw [hbalanced]
      simpa only [map_zero,LinearMap.zero_apply] using
        hm (cut M p hcut y n) (cut_other M p hcut y x (Ne.symm hy) n)
    have hv := congrArg (fun s : M => s.val y) hc
    simpa only [cut_self,Submodule.coe_zero,Pi.zero_apply,smul_eq_zero_iff_right hp] using hv

/-- Precomposition with a surjective stalk projection gives the integral
single-support module. No field extension was used anywhere in this map. -/
noncomputable def dualToSupport (x : V) : Module.Dual R (A x) →ₗ[R] supported M x :=
  (d.symm.toLinearMap.comp (projection M x).dualMap).codRestrict (supported M x) (by
    intro lam
    apply (supported_iff_annihilates M p hcut hp d hbalanced x _).mpr
    intro n hn
    simp only [LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.apply_symm_apply,
      LinearMap.dualMap_apply]
    change lam (projection M x n) = 0
    rw [hn,map_zero])

 theorem dualToSupport_bijective (x : V) (hπ : Function.Surjective (projection M x)) :
    Function.Bijective (dualToSupport M p hcut hp d hbalanced x) := by
  constructor
  · intro lam mu he
    apply LinearMap.dualMap_injective_of_surjective hπ
    apply d.symm.injective
    exact congrArg Subtype.val he
  · intro m
    have hm : d m.val ∈ (LinearMap.ker (projection M x)).dualAnnihilator := by
      rw [Submodule.mem_dualAnnihilator]
      intro n hn
      exact (supported_iff_annihilates M p hcut hp d hbalanced x m.val).mp m.property n hn
    rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker_of_surjective _ hπ] at hm
    obtain ⟨lam,hlam⟩ := hm
    refine ⟨lam,?_⟩
    apply Subtype.ext
    change d.symm ((projection M x).dualMap lam) = m.val
    rw [hlam,LinearEquiv.symm_apply_apply]

noncomputable def supportEquivDual (x : V) (hπ : Function.Surjective (projection M x)) :
    supported M x ≃ₗ[R] Module.Dual R (A x) :=
  (LinearEquiv.ofBijective (dualToSupport M p hcut hp d hbalanced x)
    (dualToSupport_bijective M p hcut hp d hbalanced x hπ)).symm

end KLInvariance.IntegralSupport
end


section
namespace KLInvariance.IntegralSupport
universe ur uv um
variable {R : Type ur} [CommRing R] {V : Type uv} [DecidableEq V]
  {A : V → Type um} [∀ x, AddCommGroup (A x)] [∀ x, Module R (A x)]
  (M : Submodule R (∀ x, A x)) (p : R)
  (hcut : ∀ x (m : M), (p • Pi.single x (m.val x)) ∈ M)
  [IsDomain R] [∀ x, Module.IsTorsionFree R (A x)] (hp : p≠0)
  (d : M ≃ₗ[R] Module.Dual R M)
  (hbalanced : ∀ x m n, d (cut M p hcut x m) n=d m (cut M p hcut x n))
  (x : V) (hπ : Function.Surjective (projection M x))
noncomputable section

 theorem supportEquivDual_pairing (m : supported M x) (n : M) :
    supportEquivDual M p hcut hp d hbalanced x hπ m (projection M x n)=d m.val n := by
  let e := supportEquivDual M p hcut hp d hbalanced x hπ
  have he := congrArg (fun s : supported M x => d s.val n) (e.symm_apply_apply m)
  change d (d.symm ((projection M x).dualMap (e m))) n=d m.val n at he
  rw [LinearEquiv.apply_symm_apply] at he
  exact he

end
end KLInvariance.IntegralSupport
end

end OAI
