import Mathlib

/-! Semantic home: ForMathlib.Algebra.Module.Free.ScalarDivisibility. Source spans: BottSamelson:14.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.FiniteFreeScalar
universe ur um un ui
variable {R : Type ur} [CommRing R]
  {M : Type um} [AddCommGroup M] [Module R M]
  {ι : Type ui} [Fintype ι] (b : Module.Basis ι R M)


 theorem exists_smul_iff (r : R) (m : M) :
    (∃ n, r • n = m) ↔ ∀ i, r ∣ b.equivFun m i := by
  classical
  constructor
  · rintro ⟨n,rfl⟩ i
    exact ⟨b.equivFun n i, by simp⟩
  · intro h
    choose n hn using h
    refine ⟨b.equivFun.symm n,b.equivFun.injective ?_⟩
    ext i
    simp only [map_smul,LinearEquiv.apply_symm_apply,Pi.smul_apply,smul_eq_mul]
    exact (hn i).symm

include b in
 theorem exists_prod_smul [DecompositionMonoid R] {J : Type*} (s : Finset J) (r : J → R)
    (hrel : (s : Set J).Pairwise (Function.onFun IsRelPrime r)) (m : M)
    (h : ∀ j ∈ s, ∃ n, r j • n = m) : ∃ n, (∏ j ∈ s, r j) • n = m := by
  apply (exists_smul_iff b _ m).mpr
  intro i
  apply Finset.prod_dvd_of_isRelPrime hrel
  intro j hj
  exact (exists_smul_iff b _ _).mp (h j hj) i

include b in


 theorem scalar_quotient_regular
    {N : Type un} [AddCommGroup N] [Module R N]
    (q : M →ₗ[R] N) (hq : Function.Surjective q)
    (a r : R) (ha : Prime a) (hr : ¬ a ∣ r)
    (hker : ∀ m, q m = 0 ↔ ∃ n, m=a • n) :
    Function.Injective (fun v : N => r • v) := by
  suffices hh : ∀ v : N, r • v = 0 → v = 0 by
    intro v w hvw
    change r • v = r • w at hvw
    have hv : r • (v-w) = 0 := by rw [smul_sub,hvw,sub_self]
    exact sub_eq_zero.mp (hh _ hv)
  intro v hv
  obtain ⟨m,rfl⟩ := hq v
  have h0 : q (r • m) = 0 := by simpa only [map_smul] using hv
  obtain ⟨n,hn⟩ := (hker _).mp h0
  have hdiv : ∀ i, a ∣ b.equivFun m i := by
    intro i
    have hc := congrArg (fun z => b.equivFun z i) hn
    simp only [map_smul,Pi.smul_apply,smul_eq_mul] at hc
    apply (ha.dvd_mul.mp ?_).resolve_left hr
    exact ⟨b.equivFun n i,hc⟩
  obtain ⟨z,hz⟩ := (exists_smul_iff b a m).mpr hdiv
  exact (hker m).mpr ⟨z,hz.symm⟩

end KLInvariance.FiniteFreeScalar
end

end OAI
