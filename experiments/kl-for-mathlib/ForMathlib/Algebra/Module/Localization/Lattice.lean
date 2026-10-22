module
public import Mathlib

public section

/-! Semantic home: ForMathlib.Algebra.Module.Localization.Lattice. Source spans: ModuleAlgebra:1.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.EdgeLattice

variable {R : Type*} [CommRing R] [klPreservedInstance2 : IsDomain R] [klPreservedInstance3 : UniqueFactorizationMonoid R]

include klPreservedInstance2 klPreservedInstance3 in
private theorem finsupp_divide {ι : Type*} (r : R) (f : ι →₀ R)
    (h : ∀ i, r ∣ f i) : ∃ g : ι →₀ R, r • g = f := by
  have _ := klPreservedInstance2
  have _ := klPreservedInstance3
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

/-- In a free module, divisibility can be checked on a basis. -/
private theorem basis_divide {E : Type*} [AddCommGroup E] [Module R E]
    {ι : Type*} (b : Module.Basis ι R E) (p : R) (m : E)
    (h : ∀ i, p ∣ b.repr m i) : ∃ n : E, p • n = m := by
  obtain ⟨f, hf⟩ := finsupp_divide p (b.repr m) h
  refine ⟨b.repr.symm f, b.repr.injective ?_⟩
  simpa only [map_smul, b.repr.apply_symm_apply] using hf

/-- Scalar-denominator formulation of the height-one intersection property.
A generic-span witness and local denominators away from each prime element
force membership in a free target, with no reflexivity hypothesis on a source. -/
theorem mem_of_prime_local_membership
    {E : Type*} [AddCommGroup E] [Module R E] [Module.IsTorsionFree R E]
    (M : Submodule R E) [Module.Free R M] (x : E)
    (hgeneric : ∃ c : R, c ≠ 0 ∧ c • x ∈ M)
    (hlocal : ∀ p : R, Prime p → ∃ a : R, ¬p ∣ a ∧ a • x ∈ M) : x ∈ M := by
  classical
  obtain ⟨c, hcz, hcx⟩ := hgeneric
  suffices ∀ c : R, c ≠ 0 → c • x ∈ M → x ∈ M from this c hcz hcx
  intro c
  induction c using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => simp
  | h₂ c hc =>
    intro _ hcx
    obtain ⟨u, rfl⟩ := hc
    simpa using M.smul_mem (↑u⁻¹ : R) hcx
  | h₃ c p hcz hp ih =>
    intro _ hpcx
    obtain ⟨a, hpa, hax⟩ := hlocal p hp
    let m : M := ⟨(p * c) • x, hpcx⟩
    let n : M := ⟨a • x, hax⟩
    have heq : a • m = (p * c) • n := by
      apply Subtype.ext
      change a • ((p * c) • x) = (p * c) • (a • x)
      exact smul_comm a (p * c) x
    let b := Module.Free.chooseBasis R M
    have hdvd : ∀ i, p ∣ b.repr m i := by
      intro i
      have hcoord := congrArg (fun z : M => b.repr z i) heq
      simp only [map_smul, Finsupp.smul_apply, smul_eq_mul] at hcoord
      have hmul : p ∣ a * b.repr m i := by
        rw [hcoord]
        exact dvd_mul_of_dvd_left (dvd_mul_right p c) _
      exact (hp.dvd_mul.mp hmul).resolve_left hpa
    obtain ⟨m', hm'⟩ := basis_divide b p m hdvd
    have hcx : c • x = (m' : E) := by
      apply smul_right_injective E hp.ne_zero
      have hval := congrArg (fun z : M => (z : E)) hm'
      change p • (m' : E) = (p * c) • x at hval
      simpa only [mul_smul] using hval.symm
    exact ih hcz (hcx ▸ m'.property)

include klPreservedInstance2 klPreservedInstance3 in
/-- A localization membership can be written with a scalar denominator outside
its prime, without requiring a choice of basis in the ambient module. -/
theorem exists_denominator_of_localized_mem
    {E : Type*} [AddCommGroup E] [Module R E]
    (M : Submodule R E) (P : Ideal R) [P.IsPrime] (x : E)
    (hx : LocalizedModule.mk x (1 : P.primeCompl) ∈ M.localized P.primeCompl) :
    ∃ a : R, a ∉ P ∧ a • x ∈ M := by
  have _ := klPreservedInstance2
  have _ := klPreservedInstance3
  obtain ⟨m, hm, s, hs⟩ := hx
  rw [← IsLocalizedModule.mk_eq_mk'] at hs
  obtain ⟨t, ht⟩ := LocalizedModule.mk_eq.mp hs
  refine ⟨(t : R) * s, (t * s).property, ?_⟩
  have hh := M.smul_mem (t : R) hm
  simp only [Submonoid.smul_def, one_smul] at ht
  rw [ht] at hh
  simpa only [mul_smul] using hh


theorem mem_iff_localized_at_height_one
    [IsNoetherianRing R]
    {E : Type*} [AddCommGroup E] [Module R E] [Module.IsTorsionFree R E]
    (M : Submodule R E) [Module.Free R M]
    (hgeneric : ∀ x : E, ∃ c : R, c ≠ 0 ∧ c • x ∈ M) (x : E) :
    x ∈ M ↔ ∀ (P : Ideal R) [P.IsPrime], P.height = 1 →
      LocalizedModule.mk x (1 : P.primeCompl) ∈ M.localized P.primeCompl := by
  constructor
  · intro hx P _ _
    exact ⟨x, hx, 1, by simp⟩
  · intro hx
    apply mem_of_prime_local_membership M x (hgeneric x)
    intro p hp
    let P := Ideal.span ({p} : Set R)
    have : P.IsPrime := Ideal.isPrime_span_singleton_of_prime hp
    have hheight : P.height = 1 :=
      Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
        (mem_nonZeroDivisors_iff_ne_zero.mpr hp.ne_zero) hp.not_isUnit
    obtain ⟨a, ha, hax⟩ := exists_denominator_of_localized_mem M P x (hx P hheight)
    exact ⟨a, by simpa only [P, Ideal.mem_span_singleton] using ha, hax⟩

/-- Equality with the intersection of preimages of all height-one localizations.
It includes the field case: an empty height-one intersection is the full module. -/
theorem eq_iInf_height_one_localizations
    [IsNoetherianRing R]
    {E : Type*} [AddCommGroup E] [Module R E] [Module.IsTorsionFree R E]
    (M : Submodule R E) [Module.Free R M]
    (hgeneric : ∀ x : E, ∃ c : R, c ≠ 0 ∧ c • x ∈ M) :
    M = ⨅ (P : PrimeSpectrum R) (_ : P.asIdeal.height = 1),
      ((M.localized P.asIdeal.primeCompl).restrictScalars R).comap
        (LocalizedModule.mkLinearMap P.asIdeal.primeCompl E) := by
  ext x
  simp only [Submodule.mem_iInf, Submodule.mem_comap, Submodule.restrictScalars_mem,
    LocalizedModule.mkLinearMap_apply]
  rw [mem_iff_localized_at_height_one M hgeneric x]
  constructor
  · intro h P hp
    exact h P.asIdeal hp
  · intro h P hP hp
    exact h ⟨P, hP⟩ hp

end KLInvariance.EdgeLattice
end

end OAI
