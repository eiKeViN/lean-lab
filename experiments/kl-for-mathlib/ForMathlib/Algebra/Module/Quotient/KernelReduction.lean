module
public import Mathlib.RingTheory.QuotSMulTop
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.RingTheory.Regular.Free

public section

/-! Semantic home: ForMathlib.Algebra.Module.Quotient.KernelReduction. Source spans: ModuleAlgebra:5.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.EdgeImage
open scoped Pointwise

variable {A B D : Type*} [CommRing A]
  [AddCommGroup B] [Module A B] [AddCommGroup D] [Module A D]

/-- The simultaneous vanishing conditions are saturated with respect to α
when multiplication by α is injective on their target. -/
theorem kernel_saturated (f : B →ₗ[A] D) (α : A)
    (hα : Function.Injective (fun x : D => α • x)) (b : B) :
    α • b ∈ LinearMap.ker f ↔ b ∈ LinearMap.ker f := by
  simp only [LinearMap.mem_ker, map_smul]
  constructor
  · intro h
    apply hα
    simpa using h
  · intro h
    simp [h]

/-- Reducing the saturated kernel modulo α introduces no additional
relations. This is the injectivity behind L/αL ≃ J. -/
theorem reduced_kernel_injective (f : B →ₗ[A] D) (α : A)
    (hα : Function.Injective (fun x : D => α • x)) :
    Function.Injective (QuotSMulTop.map α (LinearMap.ker f).subtype) := by
  apply (LinearMap.ker_eq_bot).mp
  apply le_antisymm _ bot_le
  intro x hx
  change x = 0
  obtain ⟨b, rfl⟩ := Submodule.mkQ_surjective _ x
  have hb : (b : B) ∈ α • (⊤ : Submodule A B) := by
    apply (Submodule.Quotient.mk_eq_zero _).mp
    exact hx
  obtain ⟨c, _, hc⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hb
  have hfc : c ∈ LinearMap.ker f :=
    (kernel_saturated f α hα c).mp (hc.symm ▸ b.property)
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  apply (Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr
  exact ⟨⟨c, hfc⟩, trivial, Subtype.ext hc⟩

/-- The inclusion after reduction, viewed over the actual factor ring. -/
@[expose] def reducedInclusion (f : B →ₗ[A] D) (α : A) :
    QuotSMulTop α (LinearMap.ker f) →ₗ[A ⧸ Ideal.span {α}] QuotSMulTop α B :=
  (QuotSMulTop.map α (LinearMap.ker f).subtype).extendScalarsOfSurjective
    Ideal.Quotient.mk_surjective

/-- Freeness of the later-edge kernel proves freeness of its actual edge
image over A/(α), not merely generic freeness. -/
theorem range_reducedInclusion_free (f : B →ₗ[A] D) (α : A)
    (hα : Function.Injective (fun x : D => α • x))
    [Module.Free A (LinearMap.ker f)] :
    Module.Free (A ⧸ Ideal.span {α}) (LinearMap.range (reducedInclusion f α)) := by
  let e := LinearEquiv.ofInjective (reducedInclusion f α)
    (reduced_kernel_injective f α hα)
  exact Module.Free.of_equiv e

end KLInvariance.EdgeImage
end

end OAI
