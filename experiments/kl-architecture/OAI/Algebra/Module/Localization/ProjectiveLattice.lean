import Mathlib

/-! Semantic home: OAI.Algebra.Module.Localization.ProjectiveLattice. Source spans: IntegralPairings:26.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.ProjectiveLattice
variable {R : Type*} [CommRing R] [klPreservedInstance15 : IsDomain R] [klPreservedInstance16 : UniqueFactorizationMonoid R]

 omit [IsDomain R] [UniqueFactorizationMonoid R] in
 theorem finsupp_divide {ι : Type*} (r : R) (f : ι →₀ R)
    (h : ∀ i, r ∣ f i) : ∃ g : ι →₀ R, r • g = f := by
  classical
  let g : ι →₀ R := ∑ i ∈ f.support, Finsupp.single i (Classical.choose (h i))
  refine ⟨g, ?_⟩
  dsimp [g]
  rw [Finset.smul_sum]
  have heq : (∑ i ∈ f.support, r • Finsupp.single i (Classical.choose (h i))) =
      ∑ i ∈ f.support, Finsupp.single i (f i) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finsupp.smul_single, smul_eq_mul, ← Classical.choose_spec (h i)]
  rw [heq]
  exact Finsupp.sum_single f

include klPreservedInstance15 klPreservedInstance16 in
 theorem prime_divide_of_relation {P : Type*} [AddCommGroup P] [Module R P]
    [Module.Projective R P] (p a c : R) (hp : Prime p) (ha : ¬p ∣ a)
    (m n : P) (h : a • m=(p*c) • n) : ∃ z : P, p • z=m := by
  have _ := klPreservedInstance15
  have _ := klPreservedInstance16
  obtain ⟨s,hs⟩ := Module.Projective.out (R := R) (P := P)
  have hdvd : ∀ i, p ∣ s m i := by
    intro i
    have he := congrArg (fun z : P => s z i) h
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul] at he
    have hm : p ∣ a*s m i := by
      rw [he]
      exact dvd_mul_of_dvd_left (dvd_mul_right p c) _
    exact (hp.dvd_mul.mp hm).resolve_left ha
  obtain ⟨z,hz⟩ := finsupp_divide p (s m) hdvd
  refine ⟨Finsupp.linearCombination R id z,?_⟩
  rw [← map_smul,hz,hs]

 theorem mem_of_prime_local_membership
    {E : Type*} [AddCommGroup E] [Module R E] [Module.IsTorsionFree R E]
    (M : Submodule R E) [Module.Projective R M] (x : E)
    (hgeneric : ∃ c : R, c ≠ 0 ∧ c • x ∈ M)
    (hlocal : ∀ p : R, Prime p → ∃ a : R, ¬p ∣ a ∧ a • x ∈ M) : x ∈ M := by
  obtain ⟨c,hcz,hcx⟩ := hgeneric
  suffices ∀ c : R, c≠0 → c • x ∈ M → x ∈ M from this c hcz hcx
  intro c
  induction c using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => simp
  | h₂ c hc =>
    intro _ hcx
    obtain ⟨u,rfl⟩ := hc
    simpa using M.smul_mem (↑u⁻¹ : R) hcx
  | h₃ c p hcz hp ih =>
    intro _ hpcx
    obtain ⟨a,hpa,hax⟩ := hlocal p hp
    let m : M := ⟨(p*c) • x,hpcx⟩
    let n : M := ⟨a • x,hax⟩
    have he : a • m=(p*c) • n := by
      apply Subtype.ext
      exact smul_comm a (p*c) x
    obtain ⟨z,hz⟩ := prime_divide_of_relation p a c hp hpa m n he
    have hcx : c • x=(z : E) := by
      apply smul_right_injective E hp.ne_zero
      have hv := congrArg Subtype.val hz
      change p • (z : E)=(p*c) • x at hv
      simpa only [mul_smul] using hv.symm
    exact ih hcz (hcx ▸ z.property)

end KLInvariance.ProjectiveLattice
end

end OAI
