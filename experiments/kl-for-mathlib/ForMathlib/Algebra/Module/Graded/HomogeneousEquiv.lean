module
public import Mathlib
public import ForMathlib.Algebra.Module.Graded.Basis

public section

/-! Semantic home: ForMathlib.Algebra.Module.Graded.HomogeneousEquiv. Source spans: BottSamelson:8, BottSamelson:24.
See migration.json and MIGRATION.md for exact provenance.
Homogeneous linear equivalences, dual pairings, inverse degrees and equivalences of individual graded pieces. -/

namespace OAI

section
namespace KLInvariance.Graded
open Module
universe uk ua um un ui
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {N : Type um} [AddCommGroup N] [Module A N] [Module k N] [IsScalarTower k A N]
  {P : Type un} [AddCommGroup P] [Module A P] [Module k P] [IsScalarTower k A P]
noncomputable section

omit [Algebra k A] [IsScalarTower k A N] [IsScalarTower k A P] in
 theorem equiv_inverse_homogeneous
    (𝓝 : ℤ → Submodule k N) (𝓟 : ℤ → Submodule k P)
    [DirectSum.Decomposition 𝓝] [DirectSum.Decomposition 𝓟]
    (e : N ≃ₗ[A] P) (d : ℤ)
    (he : ∀ n x, x ∈ 𝓝 n → e x ∈ 𝓟 (n+d))
    (n : ℤ) (y : P) (hy : y ∈ 𝓟 n) : e.symm y ∈ 𝓝 (n-d) := by
  have hc : component 𝓝 (n-d) (e.symm y) = e.symm y := by
    apply e.injective
    change e.toLinearMap (component 𝓝 (n-d) (e.symm y)) = e.toLinearMap (e.symm y)
    rw [← map_component 𝓝 𝓟 e.toLinearMap d he n (e.symm y)]
    simp only [LinearEquiv.coe_coe,LinearEquiv.apply_symm_apply]
    exact DirectSum.decompose_of_mem_same 𝓟 hy
  rw [← hc]
  exact (DirectSum.decompose 𝓝 (e.symm y) (n-d)).property

variable (𝓐 : ℤ → Submodule k A) [DirectSum.Decomposition 𝓐]
  [SetLike.GradedMonoid 𝓐] {ι : Type ui} [Fintype ι] [DecidableEq ι]
  (b : Basis ι A N) (d : ι → ℤ)

omit [DirectSum.Decomposition 𝓐] in
 theorem pairing_to_dual_homogeneous (p : N →ₗ[A] Dual A N) (l : ℤ)
    (hp : ∀ i j, p (b i) (b j) ∈ 𝓐 (d i+d j-l))
    {n : ℤ} {x : N} (hx : x ∈ basisPiece 𝓐 b d n) :
    p x ∈ basisPiece 𝓐 b.dualBasis (fun i => -d i) (n-l) := by
  rw [mem_basisPiece]
  intro i
  rw [Basis.dualBasis_repr]
  have h := pairing_homogeneous 𝓐 b d p l hp hx (basis_mem_piece 𝓐 b d i)
  convert h using 1
  congr 1
  omega

 theorem perfectPairing_inverse_homogeneous (p : N ≃ₗ[A] Dual A N) (l : ℤ)
    (hp : ∀ i j, p (b i) (b j) ∈ 𝓐 (d i+d j-l))
    {n : ℤ} {y : Dual A N}
    (hy : y ∈ basisPiece 𝓐 b.dualBasis (fun i => -d i) n) :
    p.symm y ∈ basisPiece 𝓐 b d (n+l) := by
  have he : ∀ m x, x ∈ basisPiece 𝓐 b d m →
      p x ∈ basisPiece 𝓐 b.dualBasis (fun i => -d i) (m+(-l)) := by
    intro m x hx
    exact pairing_to_dual_homogeneous 𝓐 b d p.toLinearMap l hp hx
  simpa only [sub_neg_eq_add] using equiv_inverse_homogeneous
    (basisPiece 𝓐 b d) (basisPiece 𝓐 b.dualBasis (fun i => -d i)) p (-l) he n y hy

end
end KLInvariance.Graded
end


section
namespace KLInvariance.Graded
universe uk um un
variable {k : Type uk} [Field k]
  {M : Type um} [AddCommGroup M] [Module k M]
  {N : Type un} [AddCommGroup N] [Module k N]
  (𝓜 : ℤ → Submodule k M) (𝓝 : ℤ → Submodule k N)
  [DirectSum.Decomposition 𝓜] [DirectSum.Decomposition 𝓝]
  (e : M ≃ₗ[k] N) (d : ℤ)
  (he : ∀ n m, m ∈ 𝓜 n → e m ∈ 𝓝 (n+d))
noncomputable section

 @[expose] def homogeneousPieceEquiv (n : ℤ) : 𝓜 n ≃ₗ[k] 𝓝 (n+d) where
  toFun m := ⟨e m.val,he n m.val m.property⟩
  invFun v := ⟨e.symm v.val,by
    simpa only [add_sub_cancel_right] using
      equiv_inverse_homogeneous 𝓜 𝓝 e d he (n+d) v.val v.property⟩
  left_inv v := Subtype.ext (e.symm_apply_apply v.val)
  right_inv v := Subtype.ext (e.apply_symm_apply v.val)
  map_add' v w := Subtype.ext (map_add e v.val w.val)
  map_smul' r v := Subtype.ext (map_smul e r v.val)

include e he in
 theorem finrank_homogeneousEquiv (n : ℤ) :
    Module.finrank k (𝓝 n)=Module.finrank k (𝓜 (n-d)) := by
  have h := (homogeneousPieceEquiv 𝓜 𝓝 e d he (n-d)).finrank_eq
  have hn : n-d+d=n := by omega
  rw [hn] at h
  exact h.symm

end
end KLInvariance.Graded
end

end OAI
