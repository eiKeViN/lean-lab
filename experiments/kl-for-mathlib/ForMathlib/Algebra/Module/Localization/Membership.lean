module
public import Mathlib

public section

/-! Semantic home: ForMathlib.Algebra.Module.Localization.Membership. Source spans: TerminalKernels:17.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.TensorLocalMembership
open TensorProduct
universe ur us um
variable {R : Type ur} [CommRing R] (S : Type us) [CommRing S] [Algebra R S]
  {M : Type um} [AddCommGroup M] [Module R M]
  (P : Submonoid R) [IsLocalization P S]
noncomputable section

 theorem baseChange_eq_localized (L : Submodule R M) :
    L.baseChange S = L.localized' S P (TensorProduct.mk R S M 1) := by
  rw [Submodule.baseChange_eq_span,Submodule.localized'_eq_span]
  rfl

 theorem denominator (L : Submodule R M) (x : M)
    (hx : 1 ⊗ₜ[R] x ∈ L.baseChange S) :
    ∃ a : P, (a:R) • x ∈ L := by
  rw [baseChange_eq_localized S P L] at hx
  obtain ⟨m,hm,s,hs⟩ := hx
  have he := (IsLocalizedModule.mk'_eq_iff).mp hs
  change (TensorProduct.mk R S M 1) m = (s:R) • (TensorProduct.mk R S M 1) x at he
  rw [← map_smul] at he
  obtain ⟨t,ht⟩ := (IsLocalizedModule.eq_iff_exists P (TensorProduct.mk R S M 1)).mp he
  refine ⟨t*s,?_⟩
  have hh := L.smul_mem (t:R) hm
  change (t:R) • m ∈ L at hh
  change (t:R) • m = (t:R) • ((s:R) • x) at ht
  simpa only [Submonoid.coe_mul,mul_smul,← ht] using hh

end
end KLInvariance.TensorLocalMembership
end

end OAI
