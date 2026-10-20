import Mathlib
import OAI.Algebra.Module.Graded.ModuleData.Duality

/-! Semantic home: OAI.Algebra.Module.Graded.ModuleData.CharacterDual. Source spans: CharacterReciprocity:35, CharacterReciprocity:15.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.Graded.ModuleData
open Polynomial Module
universe uk us um
variable {k : Type uk} [Field k] {σ : Type us} [Finite σ]
noncomputable section

 def unitPolynomialBasis : NonnegativeBasis (σ := σ)
    (unit.{uk,max uk us,um} (polynomialGrading_negative k σ)).piece where
  index := PUnit.{max uk us um + 1}
  finite := inferInstance
  basis := Pi.basisFun (MvPolynomial σ k) _
  degree _ := 0
  homogeneous i := by
    intro j
    change (Pi.basisFun (MvPolynomial σ k) _ i) j ∈ polynomialGrading k σ (0-0)
    cases i
    cases j
    simpa using SetLike.one_mem_graded (polynomialGrading k σ)

 theorem char_unit :
    (unit.{uk,max uk us,um} (polynomialGrading_negative k σ)).char=1 := by
  rw [char,character_eq _ _ (unitPolynomialBasis (k := k) (σ := σ))]
  change (∑ i : PUnit.{max uk us um + 1}, (X : Polynomial ℤ)^0)=1
  simp

end
end KLInvariance.Graded.ModuleData
end


section
namespace KLInvariance.Graded.ModuleData
open Polynomial Module
universe uk us um
variable {k : Type uk} [Field k] {σ : Type us} [Finite σ]
  (M N : ModuleData.{uk,max uk us,um} (polynomialGrading k σ))
noncomputable section

 theorem char_natDegree_le_of_dual_equiv [Module.Free (MvPolynomial σ k) M]
    (e : Dual (MvPolynomial σ k) M ≃ₗ[MvPolynomial σ k] N) (l : ℕ)
    (he : ∀ r lam, (∀ j (v : M), v∈M.piece j →
      lam v∈polynomialGrading k σ (j+r)) → e lam∈N.piece (r+l)) :
    M.char.natDegree≤l := by
  classical
  let c := (exists_nonnegativeBasis (σ := σ) M.piece M.nonneg).some
  rw [char,character_eq _ _ c]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i _
  simpa only [Polynomial.natDegree_X_pow] using M.degree_le_of_dual_equiv N e l he c i

end
end KLInvariance.Graded.ModuleData
end

end OAI
