module
public import Mathlib.RingTheory.Flat.Basic

public section

/-! Semantic home: ForMathlib.Algebra.Module.Flat.Kernel. Source spans: TerminalKernels:6.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.FlatSubmodule
open TensorProduct
universe ur us um un
variable {R : Type ur} [CommRing R] (S : Type us) [CommRing S] [Algebra R S]
  {M : Type um} [AddCommGroup M] [Module R M]
  {N : Type un} [AddCommGroup N] [Module R N]

 theorem baseChange_ker [Module.Flat R S] (f : M →ₗ[R] N) :
    (LinearMap.ker f).baseChange S = LinearMap.ker (f.baseChange S) := by
  ext z
  exact (Module.Flat.lTensor_exact S f.exact_subtype_ker_map z).symm

 theorem baseChange_map (p : Submodule R M) (f : M →ₗ[R] N) :
    (p.map f).baseChange S = (p.baseChange S).map (f.baseChange S) := by
  apply le_antisymm
  · rintro z ⟨k,rfl⟩
    induction k using TensorProduct.inductionOn with
    | tmul s x =>
      obtain ⟨m,hm,hx⟩ := x.property
      refine ⟨s ⊗ₜ m,Submodule.tmul_mem_baseChange_of_mem s hm,?_⟩
      change s ⊗ₜ[R] f m = s ⊗ₜ[R] (x : N)
      rw [hx]
    | add x y hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy
  · rintro z ⟨w,⟨k,hk⟩,rfl⟩
    subst w
    induction k using TensorProduct.inductionOn with
    | tmul s x =>
      exact Submodule.tmul_mem_baseChange_of_mem s (show f x ∈ p.map f from ⟨x,x.property,rfl⟩)
    | add x y hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy

end KLInvariance.FlatSubmodule
end

end OAI
