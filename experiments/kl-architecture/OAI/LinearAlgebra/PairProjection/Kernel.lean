import Mathlib
import OAI.LinearAlgebra.PairProjection.Basic

/-! Semantic home: OAI.LinearAlgebra.PairProjection.Kernel. Source spans: Frobenius:26.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.PairProjection
universe u v w z
variable {R : Type u} [CommRing R]
  {M : Type v} [AddCommGroup M] [Module R M]
  {X : Type w} [AddCommGroup X] [Module R X]
  {Y : Type z} [AddCommGroup Y] [Module R Y]
  (f : M →ₗ[R] X) (g : M →ₗ[R] Y)

 theorem kernel_upper (y : Y) : upper f g y=0 ↔ ∃ m : M, f m=0 ∧ g m=y := by
  have he : upper f g y=0 ↔ lower f g 0=upper f g y := by
    rw [map_zero, eq_comm]
  rw [he, compatible_iff]

 theorem upper_kernel_of_divisibility (α : R)
    (hker : ∀ m : M, f m=0 → ∃ n : Y, g m=α • n)
    (hann : ∀ z : Edge f g, α • z=0) (y : Y) :
    upper f g y=0 ↔ ∃ n : Y, y=α • n := by
  constructor
  · intro h
    obtain ⟨m,hm,rfl⟩ := (kernel_upper f g y).mp h
    exact hker m hm
  · rintro ⟨n,rfl⟩
    rw [map_smul]
    exact hann _

end KLInvariance.PairProjection
end

end OAI
