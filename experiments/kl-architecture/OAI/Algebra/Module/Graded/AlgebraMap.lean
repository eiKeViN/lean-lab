import Mathlib
import OAI.Algebra.Module.Graded.Generators

/-! Semantic home: OAI.Algebra.Module.Graded.AlgebraMap. Source spans: Frobenius:14, Frobenius:11, Frobenius:7.
See migration.json and MIGRATION.md for exact provenance. -/

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


section
namespace KLInvariance.Graded
universe uk us
variable {k : Type uk} [Field k] {σ : Type us}

 theorem algHom_polynomialGrading (f : MvPolynomial σ k →ₐ[k] MvPolynomial σ k)
    (hX : ∀ i, f (MvPolynomial.X i) ∈ polynomialGrading k σ 1)
    {n : ℤ} {p : MvPolynomial σ k} (hp : p ∈ polynomialGrading k σ n) :
    f p ∈ polynomialGrading k σ n := by
  classical
  induction hp using MvPolynomial.IsWeightedHomogeneous.induction_on with
  | zero => simpa only [map_zero] using (polynomialGrading k σ n).zero_mem
  | add p q _ _ hp hq => simpa only [map_add] using (polynomialGrading k σ n).add_mem hp hq
  | monomial d c hd =>
    rw [MvPolynomial.monomial_eq,map_mul]
    have hc : f (MvPolynomial.C c)=MvPolynomial.C c := f.commutes c
    rw [hc]
    apply MvPolynomial.IsWeightedHomogeneous.C_mul
    simp only [Finsupp.prod,map_prod,map_pow]
    have hh := SetLike.prod_pow_mem_graded (polynomialGrading k σ)
      (fun _ : σ => (1:ℤ)) (fun i => f (MvPolynomial.X i)) d (F := d.support)
      (fun i _ => hX i)
    simpa only [Finsupp.weight_apply,Finsupp.sum] using hd ▸ hh

end KLInvariance.Graded
end


section
namespace KLInvariance.Graded
universe uk ua
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [IsDomain A]
  [Algebra k A] (𝓐 : ℤ → Submodule k A) [DirectSum.Decomposition 𝓐]
  [SetLike.GradedSMul 𝓐 𝓐]

 theorem homogeneous_of_mul {a b : A} {d n : ℤ}
    (ha : a ∈ 𝓐 d) (hne : a ≠ 0) (hab : a*b ∈ 𝓐 n) : b ∈ 𝓐 (n-d) := by
  have hc := component_homogeneous_smul 𝓐 𝓐 d a ha n b
  have he : component 𝓐 n (a*b)=a*b :=
    DirectSum.decompose_of_mem_same 𝓐 hab
  rw [smul_eq_mul,he,smul_eq_mul] at hc
  have hb : b=component 𝓐 (n-d) b := mul_left_cancel₀ hne hc
  rw [hb]
  exact (DirectSum.decompose 𝓐 b (n-d)).property

end KLInvariance.Graded
end

end OAI
