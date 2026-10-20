import Mathlib
import OAI.Algebra.Module.Graded.Generators
import OAI.LinearAlgebra.Dual.Adjoint

/-! Semantic home: OAI.Algebra.Module.Graded.Adjoint. Source spans: IntegralPairings:31, IntegralPairings:32.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.Graded
open Module
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {M : Type um} [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]
  (𝓐 : ℤ → Submodule k A) (𝓜 : ℤ → Submodule k M)
  [DirectSum.Decomposition 𝓐] [DirectSum.Decomposition 𝓜]
noncomputable section

omit [IsScalarTower k A M] in
 theorem perfect_inverse_of_homogeneous_functional
    (p : M ≃ₗ[A] Dual A M) (l : ℤ)
    (hp : ∀ i j (m n : M), m ∈ 𝓜 i → n ∈ 𝓜 j → p m n ∈ 𝓐 (i+j-l))
    (r : ℤ) (lam : Dual A M)
    (hlam : ∀ j (n : M), n ∈ 𝓜 j → lam n ∈ 𝓐 (j+r)) :
    p.symm lam ∈ 𝓜 (r+l) := by
  have hc : component 𝓜 (r+l) (p.symm lam) = p.symm lam := by
    apply p.injective
    apply LinearMap.ext
    intro y
    refine DirectSum.Decomposition.inductionOn 𝓜 ?_ ?_ ?_ y
    · simp
    · intro j v
      let f : M →ₗ[A] A :=
        { toFun := fun w => p w (v : M)
          map_add' := by intros; simp
          map_smul' := by intros; simp }
      have hh : ∀ i w, w ∈ 𝓜 i → f w ∈ 𝓐 (i+(j-l)) := by
        intro i w hw
        simpa only [f,LinearMap.coe_mk,AddHom.coe_mk,add_sub_assoc] using hp i j w v hw v.property
      have he := map_component 𝓜 𝓐 f (j-l) hh (j+r) (p.symm lam)
      have hi : j+r-(j-l)=r+l := by omega
      rw [hi] at he
      have hf : f (p.symm lam)=lam v := by
        dsimp only [f,LinearMap.coe_mk,AddHom.coe_mk]
        rw [LinearEquiv.apply_symm_apply]
      rw [hf] at he
      have hsame : component 𝓐 (j+r) (lam v)=lam v :=
        DirectSum.decompose_of_mem_same 𝓐 (hlam j v v.property)
      rw [hsame] at he
      change f (component 𝓜 (r+l) (p.symm lam)) = p (p.symm lam) v
      rw [LinearEquiv.apply_symm_apply]
      exact he.symm
    · intro x y hx hy
      simp only [map_add,hx,hy]
  rw [← hc]
  exact (DirectSum.decompose 𝓜 (p.symm lam) (r+l)).property

end
end KLInvariance.Graded
end


section
namespace KLInvariance.Graded
open Module
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {M : Type um} [AddCommGroup M] [Module k M] [Module A M]
  (𝓐 : ℤ → Submodule k A) (𝓜 : ℤ → Submodule k M)
  [DirectSum.Decomposition 𝓐] [DirectSum.Decomposition 𝓜]
noncomputable section

 theorem adjoint_homogeneous
    (p : M ≃ₗ[A] Dual A M) (l : ℤ)
    (hp : ∀ i j (m n : M), m ∈ 𝓜 i → n ∈ 𝓜 j → p m n ∈ 𝓐 (i+j-l))
    (f : End A M) (hf : ∀ n m, m ∈ 𝓜 n → f m ∈ 𝓜 n)
    (n : ℤ) (m : M) (hm : m ∈ 𝓜 n) : PerfectAdjoint.adjoint p f m ∈ 𝓜 n := by
  have h := perfect_inverse_of_homogeneous_functional 𝓐 𝓜 p l hp (n-l)
    (f.dualMap (p m)) (by
      intro j v hv
      have hv' := hp n j m (f v) hm (hf j v hv)
      have he : n+j-l=j+(n-l) := by omega
      change p m (f v) ∈ 𝓐 (j+(n-l))
      rw [← he]
      exact hv')
  simpa only [sub_add_cancel,PerfectAdjoint.adjoint,LinearMap.comp_apply,LinearEquiv.coe_coe] using h

end
end KLInvariance.Graded
end

end OAI
