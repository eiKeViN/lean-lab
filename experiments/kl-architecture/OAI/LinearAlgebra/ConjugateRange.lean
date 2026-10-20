import Mathlib

/-! Semantic home: OAI.LinearAlgebra.ConjugateRange. Source spans: BalancedPairings:16.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace ConjugateRange
open Module
universe ur um un
variable {R : Type ur} [CommRing R]
  {M : Type um} [AddCommGroup M] [Module R M]
  {N : Type un} [AddCommGroup N] [Module R N]
  (e : M ≃ₗ[R] N) (f : End R N)
noncomputable section

 def conjugate : End R M := e.symm.toLinearMap.comp (f.comp e.toLinearMap)

 def map : LinearMap.range f →ₗ[R] LinearMap.range (conjugate e f) :=
  (e.symm.toLinearMap.domRestrict f.range).codRestrict _ (by
    rintro ⟨_,n,rfl⟩
    refine ⟨e.symm n,?_⟩
    change e.symm (f (e (e.symm n)))=e.symm (f n)
    rw [LinearEquiv.apply_symm_apply])

 theorem map_bijective : Function.Bijective (map e f) := by
  constructor
  · intro m n h
    apply Subtype.ext
    apply e.symm.injective
    exact congrArg Subtype.val h
  · rintro ⟨_,m,rfl⟩
    refine ⟨⟨f (e m),e m,rfl⟩,?_⟩
    rfl

 def equiv : LinearMap.range f ≃ₗ[R] LinearMap.range (conjugate e f) :=
  LinearEquiv.ofBijective (map e f) (map_bijective e f)

 theorem equiv_apply (n : LinearMap.range f) : (equiv e f n).val=e.symm n.val := rfl

end
end ConjugateRange
end

end OAI
