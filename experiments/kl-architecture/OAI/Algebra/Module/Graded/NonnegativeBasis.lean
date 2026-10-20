import Mathlib
import OAI.Algebra.Module.Graded.Hilbert.Series

/-! Semantic home: OAI.Algebra.Module.Graded.NonnegativeBasis. Source spans: SheafMorphisms:2, SheafMorphisms:7, SheafMorphisms:1.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.Graded
universe uk us
variable (k : Type uk) [Field k] (σ : Type us)

 theorem polynomial_scalar_mod_positive (a : MvPolynomial σ k) :
    ∃ c : k, a-algebraMap k (MvPolynomial σ k) c ∈ positiveIdeal (polynomialGrading k σ) := by
  obtain ⟨c,hc⟩ := polynomialGrading_zero k σ _
    (DirectSum.decompose (polynomialGrading k σ) a 0).property
  refine ⟨c,?_⟩
  rw [positiveIdeal_eq_augmentation_ker _ (polynomialGrading_negative k σ)]
  change component (polynomialGrading k σ) 0 (a-algebraMap k (MvPolynomial σ k) c)=0
  rw [map_sub,hc]
  rw [show component (polynomialGrading k σ) 0
    (DirectSum.decompose (polynomialGrading k σ) a 0 : MvPolynomial σ k) =
    (DirectSum.decompose (polynomialGrading k σ) a 0 : MvPolynomial σ k) from
    DirectSum.decompose_of_mem_same _ (DirectSum.decompose (polynomialGrading k σ) a 0).property]
  exact sub_self _

end KLInvariance.Graded
end


section
namespace KLInvariance.Graded
universe uk ua um ui
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} [DirectSum.Decomposition 𝓐]
  {M : Type um} [AddCommGroup M] [Module A M] [Module k M] [IsScalarTower k A M]
  (𝓜 : ℤ → Submodule k M) [DirectSum.Decomposition 𝓜] [SetLike.GradedSMul 𝓐 𝓜]
noncomputable section

omit [IsScalarTower k A M] in
 theorem basis_coordinates_graded {ι : Type ui} [Fintype ι]
    (b : Module.Basis ι A M) (d : ι → ℤ) (hd : ∀ i, b i ∈ 𝓜 (d i))
    (n : ℤ) (m : M) (hm : m ∈ 𝓜 n) :
    ∀ i, b.equivFun m i ∈ 𝓐 (n-d i) := by
  classical
  let : DirectSum.Decomposition (shiftedPiece 𝓐 d) := (shifted_isInternal 𝓐 d).chooseDecomposition
  have he : ∀ n v, v ∈ shiftedPiece 𝓐 d n → b.equivFun.symm v ∈ 𝓜 n := by
    intro n v hv
    rw [b.equivFun_symm_apply]
    apply Submodule.sum_mem
    intro i _
    simpa using SetLike.GradedSMul.smul_mem (hv i) (hd i)
  have hh := map_component (shiftedPiece 𝓐 d) 𝓜 b.equivFun.symm.toLinearMap 0
    (by simpa using he) n (b.equivFun m)
  simp only [sub_zero,LinearEquiv.coe_toLinearMap,LinearEquiv.symm_apply_apply] at hh
  rw [show component 𝓜 n m=m from DirectSum.decompose_of_mem_same 𝓜 hm] at hh
  have hc : component (shiftedPiece 𝓐 d) n (b.equivFun m)=b.equivFun m := by
    apply b.equivFun.symm.injective
    exact hh.symm.trans (b.equivFun.symm_apply_apply m).symm
  rw [← hc]
  exact (DirectSum.decompose (shiftedPiece 𝓐 d) (b.equivFun m) n).property

end
end KLInvariance.Graded
end


section
namespace KLInvariance.Graded
open Polynomial
universe uk us um ui
variable {k : Type uk} [Field k] {σ : Type us} [Finite σ]
  {M : Type um} [AddCommGroup M] [Module k M] [Module (MvPolynomial σ k) M]
  [IsScalarTower k (MvPolynomial σ k) M]
  (𝓜 : ℤ → Submodule k M) [DirectSum.Decomposition 𝓜]
  [SetLike.GradedSMul (polynomialGrading k σ) 𝓜]

structure NonnegativeBasis where
  index : Type um
  finite : Fintype index
  basis : Module.Basis index (MvPolynomial σ k) M
  degree : index → ℕ
  homogeneous : ∀ i, basis i ∈ 𝓜 (degree i)

attribute [instance] NonnegativeBasis.finite

theorem exists_nonnegativeBasis [Module.Free (MvPolynomial σ k) M]
    [Module.Finite (MvPolynomial σ k) M] (hneg : ∀ n < 0, 𝓜 n = ⊥) :
    Nonempty (NonnegativeBasis (σ := σ) 𝓜) := by
  classical
  obtain ⟨ι,hι,b,hb⟩ := exists_homogeneous_basis_polynomial (σ := σ) 𝓜 0 hneg
  let := hι
  let : Fintype ι := Fintype.ofFinite ι
  choose d hd using hb
  have hd0 (i : ι) : 0 ≤ d i := by
    by_contra h
    have hh := hd i
    rw [hneg _ (lt_of_not_ge h),Submodule.mem_bot] at hh
    exact b.ne_zero i hh
  exact ⟨⟨ι,inferInstance,b,fun i => (d i).toNat,fun i => by simpa [Int.toNat_of_nonneg (hd0 i)] using hd i⟩⟩

namespace NonnegativeBasis
variable {𝓜} (b : NonnegativeBasis (σ := σ) 𝓜)

noncomputable def polynomial : ℤ[X] := ∑ i, X ^ b.degree i

omit [Finite σ] [IsScalarTower k (MvPolynomial σ k) M]
  [DirectSum.Decomposition 𝓜] [SetLike.GradedSMul (polynomialGrading k σ) 𝓜] in
lemma coeff_nonneg (n : ℕ) : 0 ≤ b.polynomial.coeff n := by
  classical
  simp only [polynomial,Polynomial.finsetSum_coeff,Polynomial.coeff_X_pow]
  exact Finset.sum_nonneg (fun i _ => by split <;> norm_num)

omit [Finite σ] [IsScalarTower k (MvPolynomial σ k) M]
  [DirectSum.Decomposition 𝓜] [SetLike.GradedSMul (polynomialGrading k σ) 𝓜] in
lemma eval₂_eq (q : ℝ) : Polynomial.eval₂ (Int.castRingHom ℝ) q b.polynomial =
    ∑ i, q ^ b.degree i := by
  change (Polynomial.eval₂RingHom (Int.castRingHom ℝ) q) (∑ i, X ^ b.degree i) = _
  simp

omit [Finite σ] in
lemma hasSum [Fintype σ] {q : ℝ} (hq : 0 < q) (hq1 : q < 1) :
    HasSum (fun n : ℤ => (Module.finrank k (𝓜 n) : ℝ)*q^n)
      (Polynomial.eval₂ (Int.castRingHom ℝ) q b.polynomial * (1-q)⁻¹ ^ Fintype.card σ) := by
  rw [b.eval₂_eq]
  convert Hilbert.hasSum_homogeneous_basis 𝓜 b.basis (fun i => (b.degree i : ℤ))
    b.homogeneous hq hq1 using 1
  simp

lemma polynomial_eq (c : NonnegativeBasis (σ := σ) 𝓜) : b.polynomial = c.polynomial := by
  classical
  let : Fintype σ := Fintype.ofFinite σ
  apply Polynomial.map_injective (Int.castRingHom ℝ) Int.cast_injective
  apply Polynomial.eq_of_infinite_eval_eq
  have hsub : Set.Ioo (0 : ℝ) 1 ⊆ {q | Polynomial.eval q (b.polynomial.map (Int.castRingHom ℝ)) =
      Polynomial.eval q (c.polynomial.map (Int.castRingHom ℝ))} := by
    intro q hq
    have h := (b.hasSum hq.1 hq.2).unique (c.hasSum hq.1 hq.2)
    have hne : (1-q)⁻¹ ^ Fintype.card σ ≠ 0 := pow_ne_zero _ (inv_ne_zero (sub_ne_zero.mpr (ne_of_gt hq.2)))
    change Polynomial.eval q (b.polynomial.map (Int.castRingHom ℝ)) =
      Polynomial.eval q (c.polynomial.map (Int.castRingHom ℝ))
    simpa only [Polynomial.eval_map] using mul_right_cancel₀ hne h
  exact Set.Infinite.mono hsub (Set.Ioo_infinite (show (0 : ℝ) < 1 by norm_num))

end NonnegativeBasis

noncomputable def character [Module.Free (MvPolynomial σ k) M]
    [Module.Finite (MvPolynomial σ k) M] (hneg : ∀ n < 0, 𝓜 n = ⊥) : ℤ[X] :=
  (exists_nonnegativeBasis (σ := σ) 𝓜 hneg).some.polynomial

lemma character_coeff_nonneg [Module.Free (MvPolynomial σ k) M]
    [Module.Finite (MvPolynomial σ k) M] (hneg : ∀ n < 0, 𝓜 n = ⊥) (n : ℕ) :
    0 ≤ (character (σ := σ) 𝓜 hneg).coeff n :=
  (exists_nonnegativeBasis (σ := σ) 𝓜 hneg).some.coeff_nonneg n

lemma character_eq [Module.Free (MvPolynomial σ k) M]
    [Module.Finite (MvPolynomial σ k) M] (hneg : ∀ n < 0, 𝓜 n = ⊥)
    (b : NonnegativeBasis (σ := σ) 𝓜) : character (σ := σ) 𝓜 hneg = b.polynomial :=
  (exists_nonnegativeBasis (σ := σ) 𝓜 hneg).some.polynomial_eq b

end KLInvariance.Graded
end

end OAI
