module
public import Mathlib

public section

/-! Semantic home: ForMathlib.Algebra.Module.Graded.Components. Source spans: ModuleAlgebra:4, ModuleAlgebra:6.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.Graded

variable {k A M : Type*} [CommRing k] [CommRing A] [Algebra k A]
  [AddCommGroup M] [Module k M] [Module A M] [klPreservedInstance4 : IsScalarTower k A M]

@[expose] noncomputable def component (𝓜 : ℤ → Submodule k M)
    [DirectSum.Decomposition 𝓜] (n : ℤ) : M →ₗ[k] M where
  toFun m := DirectSum.decompose 𝓜 m n
  map_add' x y := by simp [DirectSum.decompose_add]
  map_smul' r m := by simp [DirectSum.decompose_smul, DirectSum.smul_apply]

@[expose] def positiveIdeal (𝓐 : ℤ → Submodule k A) : Ideal A :=
  Ideal.span {a | ∃ n : ℤ, 0 < n ∧ a ∈ 𝓐 n}

include klPreservedInstance4 in
/-- A bounded-below internally graded module which equals its positive-ideal
multiple is zero.  This is the exact graded Nakayama vanishing step used to
remove the complementary kernel in the source's free-cover construction. -/
theorem subsingleton_of_positiveIdeal_smul_eq_top
    (𝓐 : ℤ → Submodule k A) (𝓜 : ℤ → Submodule k M)
    [DirectSum.Decomposition 𝓜] [SetLike.GradedSMul 𝓐 𝓜]
    (d₀ : ℤ) (hbound : ∀ j < d₀, 𝓜 j = ⊥)
    (hgen : positiveIdeal 𝓐 • (⊤ : Submodule A M) = ⊤) :
    Subsingleton M := by
  have _ := klPreservedInstance4
  classical
  have hlow : ∀ j < d₀, ∀ m ∈ 𝓜 j, m = 0 := by
    intro j hj m hm
    simpa [hbound j hj] using hm
  have hind : ∀ n : ℕ, ∀ m ∈ 𝓜 (d₀ + n), m = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      let p := component 𝓜 (d₀ + n)
      have hpadd (x y : M) : p (x + y) = p x + p y := map_add p x y
      have hpzero : p 0 = 0 := map_zero p
      have hsmul (i : ℤ) (hi : 0 < i) (a : A) (ha : a ∈ 𝓐 i) :
          ∀ m : M, p (a • m) = 0 := by
        intro m
        refine DirectSum.Decomposition.inductionOn 𝓜 ?_ ?_ ?_ m
        · simp
        · intro j m
          by_cases hj : j < d₀ + n
          · have hm : (m : M) = 0 := by
              by_cases hj₀ : j < d₀
              · exact hlow j hj₀ m m.property
              · have heq : d₀ + (j - d₀).toNat = j := by omega
                exact ih (j - d₀).toNat (by omega) m (heq.symm ▸ m.property)
            simp [hm]
          · have hdeg : i + j ≠ d₀ + n := by omega
            have ham : a • (m : M) ∈ 𝓜 (i + j) :=
              SetLike.GradedSMul.smul_mem ha m.property
            exact DirectSum.decompose_of_mem_ne 𝓜 ham hdeg
        · intro x y hx hy
          simp only [smul_add, hpadd, hx, hy, add_zero]
      let K : Ideal A :=
        { carrier := {a | ∀ m : M, p (a • m) = 0}
          zero_mem' := by simp
          add_mem' := by
            intro a b ha hb m
            rw [add_smul, hpadd, ha m, hb m, add_zero]
          smul_mem' := by
            intro r a ha m
            change p ((r * a) • m) = 0
            rw [mul_comm r a, mul_smul]
            exact ha (r • m) }
      have hIK : positiveIdeal 𝓐 ≤ K := by
        apply Ideal.span_le.mpr
        rintro a ⟨i, hi, ha⟩
        exact hsmul i hi a ha
      have hp : ∀ m : M, p m = 0 := by
        intro m
        have hm : m ∈ positiveIdeal 𝓐 • (⊤ : Submodule A M) := by
          rw [hgen]
          trivial
        refine Submodule.smul_induction_on hm ?_ ?_
        · intro a ha x _
          exact hIK ha x
        · intro x y hx hy
          rw [hpadd, hx, hy, add_zero]
      intro m hm
      have hcomp : p m = m :=
        DirectSum.decompose_of_mem_same 𝓜 hm
      exact hcomp.symm.trans (hp m)
  have homogeneous_zero (j : ℤ) (m : M) (hm : m ∈ 𝓜 j) : m = 0 := by
    by_cases hj : j < d₀
    · exact hlow j hj m hm
    · have heq : d₀ + (j - d₀).toNat = j := by omega
      exact hind (j - d₀).toNat m (heq.symm ▸ hm)
  have all_zero : ∀ m : M, m = 0 :=
    DirectSum.Decomposition.inductionOn 𝓜 rfl
      (fun m => homogeneous_zero _ m m.property)
      (fun x y hx hy => by rw [hx, hy, add_zero])
  exact ⟨fun x y => (all_zero x).trans (all_zero y).symm⟩

end KLInvariance.Graded
end


section
namespace KLInvariance.Graded
open scoped Pointwise
variable {A F P : Type*} [CommRing A]
  [AddCommGroup F] [Module A F] [AddCommGroup P] [Module A P]

/-- If a split cover is minimal modulo I, its complementary kernel equals
its own I-multiple. This is the exact input to the graded Nakayama step. -/
theorem positive_smul_kernel_of_minimal_split
    (I : Ideal A) (f : F →ₗ[A] P) (s : P →ₗ[A] F)
    (hs : f.comp s = LinearMap.id)
    (hmin : LinearMap.ker f ≤ I • (⊤ : Submodule A F)) :
    I • (⊤ : Submodule A (LinearMap.ker f)) = ⊤ := by
  have hs' (y : P) : f (s y) = y := LinearMap.congr_fun hs y
  let k : F →ₗ[A] LinearMap.ker f :=
    { toFun := fun x => ⟨x - s (f x), by simp [LinearMap.mem_ker, hs']⟩
      map_add' := fun x y => Subtype.ext (by simp; abel)
      map_smul' := fun r x => Subtype.ext (by simp [smul_sub]) }
  apply le_antisymm le_top
  intro x _
  have hx : (x : F) ∈ I • (⊤ : Submodule A F) := hmin x.property
  have hkx : k (x : F) = x := by
    apply Subtype.ext
    simp [k]
  rw [← hkx]
  refine Submodule.smul_induction_on hx ?_ ?_
  · intro r hr y _
    rw [map_smul]
    exact Submodule.smul_mem_smul hr (Submodule.mem_top : k y ∈ (⊤ : Submodule A _))
  · intro y z hy hz
    rw [map_add]
    exact Submodule.add_mem _ hy hz

/-- Minimality makes a split free cover an isomorphism in the bounded-below
graded situation. Its kernel is not assumed to vanish. -/
theorem bijective_of_graded_minimal_split
    {k : Type*} [CommRing k] [Algebra k A]
    (𝓐 : ℤ → Submodule k A) (f : F →ₗ[A] P) (s : P →ₗ[A] F)
    (hs : f.comp s = LinearMap.id)
    (hmin : LinearMap.ker f ≤ positiveIdeal 𝓐 • (⊤ : Submodule A F))
    [Module k (LinearMap.ker f)] [IsScalarTower k A (LinearMap.ker f)]
    (𝓚 : ℤ → Submodule k (LinearMap.ker f))
    [DirectSum.Decomposition 𝓚] [SetLike.GradedSMul 𝓐 𝓚]
    (d₀ : ℤ) (hbound : ∀ j < d₀, 𝓚 j = ⊥) : Function.Bijective f := by
  let := subsingleton_of_positiveIdeal_smul_eq_top 𝓐 𝓚 d₀ hbound
    (positive_smul_kernel_of_minimal_split (positiveIdeal 𝓐) f s hs hmin)
  constructor
  · apply LinearMap.ker_eq_bot.mp
    refine le_antisymm ?_ bot_le
    intro x hx
    exact congrArg Subtype.val (Subsingleton.elim (⟨x, hx⟩ : LinearMap.ker f) 0)
  · intro y
    exact ⟨s y, LinearMap.congr_fun hs y⟩

end KLInvariance.Graded
end

end OAI
