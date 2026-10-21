import Mathlib
import ForMathlib.Algebra.Module.Graded.ModuleData.Basic
import ForMathlib.Algebra.Module.Graded.NonnegativeBasis

/-! Semantic home: ForMathlib.Algebra.Module.Graded.ModuleData.Character. Source spans: SheafMorphisms:29, SheafMorphisms:30.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.Graded.ModuleData
open Polynomial
universe uk us um
variable {k : Type uk} [Field k] {σ : Type us} [Finite σ]
  {M N : ModuleData.{uk,max uk us,um} (polynomialGrading k σ)}

noncomputable def mapNonnegativeBasis (e : M ≃ₗ[MvPolynomial σ k] N)
    (he : ∀ n v, v ∈ M.piece n → e v ∈ N.piece n)
    (b : NonnegativeBasis (σ := σ) M.piece) : NonnegativeBasis (σ := σ) N.piece where
  index := b.index
  finite := b.finite
  basis := b.basis.map e
  degree := b.degree
  homogeneous i := he _ _ (b.homogeneous i)

 theorem character_eq_of_gradedEquiv [Module.Free (MvPolynomial σ k) M]
    [Module.Free (MvPolynomial σ k) N] (e : M ≃ₗ[MvPolynomial σ k] N)
    (he : ∀ n v, v ∈ M.piece n → e v ∈ N.piece n) :
    character (σ := σ) M.piece M.nonneg = character (σ := σ) N.piece N.nonneg := by
  let b := (exists_nonnegativeBasis (σ := σ) M.piece M.nonneg).some
  rw [character_eq M.piece M.nonneg b,
    character_eq N.piece N.nonneg (mapNonnegativeBasis e he b)]
  rfl

end KLInvariance.Graded.ModuleData
end


section
namespace KLInvariance.Graded.ModuleData
open Polynomial Module
universe uk us um
variable {k : Type uk} [Field k] {σ : Type us} [Finite σ]
  (M N : ModuleData.{uk,max uk us,um} (polynomialGrading k σ))
noncomputable section

 abbrev char [Module.Free (MvPolynomial σ k) M] : Polynomial ℤ :=
  character (σ := σ) M.piece M.nonneg

 def shiftedBasis (b : NonnegativeBasis (σ := σ) M.piece) (d : ℕ) :
    NonnegativeBasis (σ := σ) (M.shift d).piece where
  index := b.index
  finite := b.finite
  basis := b.basis
  degree i := b.degree i+d
  homogeneous i := by
    change b.basis i ∈ M.piece ((b.degree i+d : ℕ)-(d:ℤ))
    simpa only [Nat.cast_add,add_sub_cancel_right] using b.homogeneous i

 instance shift_free [Module.Free (MvPolynomial σ k) M] (d : ℕ) :
    Module.Free (MvPolynomial σ k) (M.shift d) := ‹Module.Free (MvPolynomial σ k) M›

 theorem char_shift [Module.Free (MvPolynomial σ k) M] (d : ℕ) :
    (M.shift d).char=X^d*M.char := by
  let b := (exists_nonnegativeBasis (σ := σ) M.piece M.nonneg).some
  rw [char,character_eq _ _ (M.shiftedBasis b d),char,character_eq _ _ b]
  change (∑ i : b.index, (X : Polynomial ℤ) ^ (b.degree i+d)) = X^d*∑ i, X^b.degree i
  simp only [pow_add,mul_comm,Finset.mul_sum]

 def productBasis (b : NonnegativeBasis (σ := σ) M.piece)
    (c : NonnegativeBasis (σ := σ) N.piece) :
    NonnegativeBasis (σ := σ) (M.prod N).piece where
  index := b.index ⊕ c.index
  finite := inferInstance
  basis := b.basis.prod c.basis
  degree := Sum.elim b.degree c.degree
  homogeneous i := by
    cases i with
    | inl i =>
      change ((b.basis.prod c.basis) (Sum.inl i)).1 ∈ M.piece (b.degree i) ∧
        ((b.basis.prod c.basis) (Sum.inl i)).2 ∈ N.piece (b.degree i)
      simpa only [Basis.prod_apply_inl_fst,Basis.prod_apply_inl_snd] using
        And.intro (b.homogeneous i) (Submodule.zero_mem (N.piece (b.degree i)))
    | inr i =>
      change ((b.basis.prod c.basis) (Sum.inr i)).1 ∈ M.piece (c.degree i) ∧
        ((b.basis.prod c.basis) (Sum.inr i)).2 ∈ N.piece (c.degree i)
      simpa only [Basis.prod_apply_inr_fst,Basis.prod_apply_inr_snd] using
        And.intro (Submodule.zero_mem (M.piece (c.degree i))) (c.homogeneous i)

 instance prod_free [Module.Free (MvPolynomial σ k) M] [Module.Free (MvPolynomial σ k) N] :
    Module.Free (MvPolynomial σ k) (M.prod N) :=
  (inferInstance : Module.Free (MvPolynomial σ k) (M × N))

 theorem char_prod [Module.Free (MvPolynomial σ k) M] [Module.Free (MvPolynomial σ k) N] :
    (M.prod N).char=M.char+N.char := by
  let b := (exists_nonnegativeBasis (σ := σ) M.piece M.nonneg).some
  let c := (exists_nonnegativeBasis (σ := σ) N.piece N.nonneg).some
  rw [char,character_eq _ _ (M.productBasis N b c),char,character_eq _ _ b,
    char,character_eq _ _ c]
  change (∑ i : b.index ⊕ c.index, (X : Polynomial ℤ)^Sum.elim b.degree c.degree i) =
    (∑ i : b.index, X^b.degree i)+(∑ i : c.index, X^c.degree i)
  exact Fintype.sum_sum_type (fun i => (X : Polynomial ℤ)^Sum.elim b.degree c.degree i)

 def piBasis {ι : Type um} [Fintype ι]
    (F : ι → ModuleData.{uk,max uk us,um} (polynomialGrading k σ))
    (b : ∀ i, NonnegativeBasis (σ := σ) (F i).piece) :
    NonnegativeBasis (σ := σ) (pi F).piece where
  index := Σ i, (b i).index
  finite := inferInstance
  basis := Pi.basis (fun i => (b i).basis)
  degree i := (b i.1).degree i.2
  homogeneous i := by
    classical
    intro j _
    change (Pi.basis (fun i => (b i).basis)) i j ∈ (F j).piece ((b i.1).degree i.2)
    rw [Pi.basis_apply]
    by_cases h : j=i.1
    · subst j
      simpa only [Pi.single_eq_same] using (b i.1).homogeneous i.2
    · simp only [Pi.single_eq_of_ne h,Submodule.zero_mem]

 instance pi_free {ι : Type um} [Fintype ι]
    (F : ι → ModuleData.{uk,max uk us,um} (polynomialGrading k σ))
    [∀ i, Module.Free (MvPolynomial σ k) (F i)] :
    Module.Free (MvPolynomial σ k) (pi F) :=
  (inferInstance : Module.Free (MvPolynomial σ k) (∀ i, F i))

 theorem char_pi {ι : Type um} [Fintype ι]
    (F : ι → ModuleData.{uk,max uk us,um} (polynomialGrading k σ))
    [∀ i, Module.Free (MvPolynomial σ k) (F i)] :
    (pi F).char=∑ i, (F i).char := by
  let b := fun i => (exists_nonnegativeBasis (σ := σ) (F i).piece (F i).nonneg).some
  rw [char,character_eq _ _ (piBasis F b)]
  change (∑ i : Σ j, (b j).index, (X : Polynomial ℤ)^(b i.1).degree i.2) = _
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro i _
  exact (character_eq (F i).piece (F i).nonneg (b i)).symm

 theorem char_zero [Subsingleton M] [Module.Free (MvPolynomial σ k) M] : M.char=0 := by
  let b := (exists_nonnegativeBasis (σ := σ) M.piece M.nonneg).some
  have : IsEmpty b.index := ⟨fun i => b.basis.ne_zero i (Subsingleton.elim _ _)⟩
  rw [char,character_eq _ _ b]
  simp [NonnegativeBasis.polynomial]

end
end KLInvariance.Graded.ModuleData
end

end OAI
