module
public import Mathlib
public import ForMathlib.Algebra.Module.Graded.HomogeneousDual

public section

/-! Semantic home: ForMathlib.Algebra.Module.Graded.RegularScalar. Source spans: EdgeLocalization:20.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.Graded
open Module
universe uk ua um ui
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  (𝓐 : ℤ → Submodule k A) [DirectSum.Decomposition 𝓐] [SetLike.GradedMonoid 𝓐]
  (hneg : ∀ n < 0, 𝓐 n = ⊥)

 include hneg in
 theorem homogeneous_positive_nonzero {n : ℤ} {a : A}
    (ha : a∈𝓐 n) (hp : a∈positiveIdeal 𝓐) (hn : a≠0) : 0<n := by
  by_contra hh
  have hnle : n≤0 := le_of_not_gt hh
  by_cases hz : n=0
  · subst n
    rw [positiveIdeal_eq_augmentation_ker 𝓐 hneg] at hp
    have hc : component 𝓐 0 a=0 := hp
    have he : component 𝓐 0 a=a := DirectSum.decompose_of_mem_same 𝓐 ha
    exact hn (he.symm.trans hc)
  · have hlt : n<0 := lt_of_le_of_ne hnle hz
    rw [hneg n hlt,Submodule.mem_bot] at ha
    exact hn ha

variable {M : Type um} [AddCommGroup M] [Module A M]

omit [DirectSum.Decomposition 𝓐] [SetLike.GradedMonoid 𝓐] in
 theorem dual_mem_ideal (J : Ideal A) (f : Dual A M) {m : M}
    (hm : m∈J • (⊤ : Submodule A M)) : f m∈J := by
  refine Submodule.smul_induction_on hm ?_ ?_
  · intro a ha v _
    rw [map_smul]
    exact J.mul_mem_right (f v) ha
  · intro u v hu hv
    rw [map_add]
    exact J.add_mem hu hv

variable [Module k M] [IsScalarTower k A M]
  (𝓜 : ℤ → Submodule k M) [DirectSum.Decomposition 𝓜] [SetLike.GradedSMul 𝓐 𝓜]
  {ι : Type ui} [Fintype ι] [DecidableEq ι] (b : Basis ι A M) (d : ι → ℤ)
  (hb : ∀ i, b i∈𝓜 (d i)) (D : ℤ) (Q : Dual A M →ₗ[A] M)

 include hneg hb in
 omit [IsScalarTower k A M] in
 theorem local_diagonal_strict_degree
    (hq : ∀ i, Q (b.dualBasis i)∈𝓜 (D-d i))
    (hmin : LinearMap.range Q ≤ positiveIdeal 𝓐 • (⊤ : Submodule A M))
    (i : ι) (hne : b.dualBasis i (Q (b.dualBasis i))≠0) : 2*d i<D := by
  have hc : b.dualBasis i (Q (b.dualBasis i))∈𝓐 (D-d i+(-d i)) :=
    dualBasis_homogeneous 𝓐 𝓜 b d hb i _ _ (hq i)
  have hp : b.dualBasis i (Q (b.dualBasis i))∈positiveIdeal 𝓐 :=
    dual_mem_ideal (positiveIdeal 𝓐) (b.dualBasis i) (hmin ⟨b.dualBasis i,rfl⟩)
  have hh := homogeneous_positive_nonzero 𝓐 hneg hc hp hne
  omega

end KLInvariance.Graded
end

end OAI
