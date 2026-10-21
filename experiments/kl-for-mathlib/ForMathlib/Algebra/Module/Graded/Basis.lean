import Mathlib
import ForMathlib.Algebra.Module.Graded.Generators

/-! Semantic home: ForMathlib.Algebra.Module.Graded.Basis. Source spans: Frobenius:14.
See migration.json and MIGRATION.md for exact provenance.
Grading transported through a weighted basis, including the degree of a bilinear pairing on homogeneous basis vectors. -/

namespace OAI

section
namespace KLInvariance.Graded
open Module
universe uk ua um ui
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  (𝓐 : ℤ → Submodule k A) [DirectSum.Decomposition 𝓐]
  [SetLike.GradedMonoid 𝓐]
  {N : Type um} [AddCommGroup N] [Module A N] [Module k N] [IsScalarTower k A N]
  {ι : Type ui} [Fintype ι] (b : Basis ι A N) (d : ι → ℤ)
noncomputable section

 def basisPiece (n : ℤ) : Submodule k N :=
  (shiftedPiece 𝓐 d n).comap (b.equivFun.restrictScalars k).toLinearMap

omit [DirectSum.Decomposition 𝓐] [SetLike.GradedMonoid 𝓐] in
 theorem mem_basisPiece (n : ℤ) (m : N) :
    m ∈ basisPiece 𝓐 b d n ↔ ∀ i, b.repr m i ∈ 𝓐 (n-d i) := Iff.rfl

 instance basisPiece_decomposition : DirectSum.Decomposition (basisPiece 𝓐 b d) := by
  let _ : DirectSum.Decomposition (shiftedPiece 𝓐 d) := (shifted_isInternal 𝓐 d).chooseDecomposition
  apply DirectSum.IsInternal.chooseDecomposition
  have he : basisPiece 𝓐 b d = fun n => (shiftedPiece 𝓐 d n).map
      (b.equivFun.restrictScalars k).symm.toLinearMap := by
    funext n
    exact Submodule.comap_equiv_eq_map_symm _ _
  rw [he]
  apply image_isInternal (shiftedPiece 𝓐 d)
    (b.equivFun.restrictScalars k).symm.toLinearMap
    (b.equivFun.restrictScalars k).symm.surjective
  intro n m hm
  have hz : m=0 := (b.equivFun.restrictScalars k).symm.injective (by simpa using hm)
  subst m
  simp

 instance basisPiece_graded : SetLike.GradedSMul 𝓐 (basisPiece 𝓐 b d) where
  smul_mem := by
    intro n m a x ha hx i
    change b.repr (a • x) i ∈ 𝓐 ((n+m)-d i)
    rw [map_smul,Finsupp.smul_apply,smul_eq_mul]
    change ∀ i, b.repr x i ∈ 𝓐 (m-d i) at hx
    have h := SetLike.GradedMul.mul_mem ha (hx i)
    simpa only [add_sub_assoc] using h

omit [DirectSum.Decomposition 𝓐] in
 theorem basis_mem_piece (i : ι) : b i ∈ basisPiece 𝓐 b d (d i) := by
  classical
  intro j
  change b.repr (b i) j ∈ 𝓐 (d i-d j)
  by_cases hij : i=j
  · subst j
    simp only [Basis.repr_self,Finsupp.single_eq_same,sub_self]
    exact SetLike.one_mem_graded 𝓐
  · rw [Basis.repr_self,Finsupp.single_eq_of_ne (Ne.symm hij)]
    exact Submodule.zero_mem _

omit [DirectSum.Decomposition 𝓐] in
 theorem pairing_homogeneous (p : N →ₗ[A] Dual A N) (l : ℤ)
    (hp : ∀ i j, p (b i) (b j) ∈ 𝓐 (d i+d j-l))
    {n m : ℤ} {x y : N} (hx : x ∈ basisPiece 𝓐 b d n)
    (hy : y ∈ basisPiece 𝓐 b d m) : p x y ∈ 𝓐 (n+m-l) := by
  classical
  have hexp : p x y = ∑ i, ∑ j,
      b.repr x i * b.repr y j * p (b i) (b j) := by
    conv_lhs => rw [← b.sum_repr x,← b.sum_repr y]
    simp only [map_sum,LinearMap.sum_apply,map_smul,LinearMap.smul_apply,smul_eq_mul,
      Finset.mul_sum,mul_assoc]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hexp]
  apply Submodule.sum_mem
  intro i _
  apply Submodule.sum_mem
  intro j _
  change ∀ i, b.repr x i ∈ 𝓐 (n-d i) at hx
  change ∀ i, b.repr y i ∈ 𝓐 (m-d i) at hy
  have h := SetLike.GradedMul.mul_mem
    (SetLike.GradedMul.mul_mem (hx i) (hy j)) (hp i j)
  convert h using 1
  congr 1
  omega

end
end KLInvariance.Graded
end

end OAI
