import Mathlib
import ForMathlib.GroupTheory.Coxeter.Roots.Basic

/-! Semantic home: ForMathlib.GroupTheory.Coxeter.Roots.Splines. Source spans: DihedralIntervals:2.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.TitsSpace
open Module
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
  {σ : Type us} (basis : Basis σ ℝ (Extended M))
noncomputable section

 def linearPolynomial : Extended M →ₗ[ℝ] MvPolynomial σ ℝ :=
  (SymmetricAlgebra.equivMvPolynomial basis).toLinearMap.comp
    (SymmetricAlgebra.ι ℝ (Extended M))

 def orbitSpline (y : W) (v₀ : Extended M) (v : W) : MvPolynomial σ ℝ :=
  linearPolynomial basis (extendedAction M cs (v*y⁻¹) v₀ - v₀)

 theorem orbitSpline_self (y : W) (v₀ : Extended M) : orbitSpline cs basis y v₀ y = 0 := by
  simp [orbitSpline]

 theorem orbitSpline_reflection {t : W} {a : I → ℝ}
    (ha : Represents M cs t a) (y x : W) (v₀ : Extended M) :
    linearPolynomial basis (embed M a) ∣
      orbitSpline cs basis y v₀ x - orbitSpline cs basis y v₀ (t*x) := by
  let c := extendedForm M (embed M a) (extendedAction M cs (x*y⁻¹) v₀)
  have heq : extendedAction M cs (t*x*y⁻¹) v₀ =
      extendedAction M cs (x*y⁻¹) v₀ - c • embed M a := by
    rw [mul_assoc,map_mul,LinearEquiv.mul_apply,ha.formula]
  unfold orbitSpline
  rw [← map_sub,heq]
  have hv : (extendedAction M cs (x*y⁻¹) v₀ - v₀) -
      (extendedAction M cs (x*y⁻¹) v₀ - c • embed M a - v₀) = c • embed M a := by abel
  rw [hv,map_smul]
  exact ⟨algebraMap ℝ (MvPolynomial σ ℝ) c, by simp [Algebra.smul_def,mul_comm]⟩

 theorem exists_pair_vector {t r : W} {a d : I → ℝ}
    (ha : Represents M cs t a) (hd : Represents M cs r d) (htr : t ≠ r) :
    ∃ v₀ : Extended M, extendedForm M (embed M a) v₀ = -1 ∧
      extendedForm M (embed M d) v₀ = 0 := by
  have hli := (ha.extended_independent_of_ne hd htr).map'
    (extendedForm M) (extendedForm_spec M).2.1.ker_eq_bot
  have hli' : LinearIndependent ℝ ![extendedForm M (embed M a),
      extendedForm M (embed M d)] := by
    convert hli using 1
    funext i
    fin_cases i <;> rfl
  obtain ⟨v₀,hv₀⟩ := ReflectionPlane.formPair_surjective _ _ hli' (-1,0)
  exact ⟨v₀,congrArg Prod.fst hv₀,congrArg Prod.snd hv₀⟩

 theorem orbitSpline_pair_factor {x y z t r : W} {a d : I → ℝ}
    (ha : Represents M cs t a) (hd : Represents M cs r d)
    (hxy : x*y⁻¹=t) (hzy : z*y⁻¹=r) (hxz : x ≠ z) :
    ∃ v₀ : Extended M,
      orbitSpline cs basis y v₀ x = linearPolynomial basis (embed M a) ∧
      orbitSpline cs basis y v₀ y = 0 ∧ orbitSpline cs basis y v₀ z = 0 := by
  have htr : t ≠ r := by
    intro he
    apply hxz
    exact mul_right_cancel (hxy.trans (he.trans hzy.symm))
  obtain ⟨v₀,hv₀a,hv₀d⟩ := exists_pair_vector cs ha hd htr
  refine ⟨v₀,?_,orbitSpline_self cs basis y v₀,?_⟩
  · simp only [orbitSpline,hxy,ha.formula,hv₀a]
    congr 1
    module
  · simp only [orbitSpline,hzy,hd.formula,hv₀d,zero_smul,sub_zero,sub_self,map_zero]

 theorem orbitSpline_single_factor {x y t : W} {a : I → ℝ}
    (ha : Represents M cs t a) (hxy : x*y⁻¹=t) :
    ∃ v₀ : Extended M,
      orbitSpline cs basis y v₀ x = linearPolynomial basis (embed M a) ∧
      orbitSpline cs basis y v₀ y = 0 := by
  let v₀ : Extended M := (-1/2 : ℝ) • embed M a
  have hv₀ : extendedForm M (embed M a) v₀ = -1 := by
    simp only [v₀,map_smul,smul_eq_mul,embed,(extendedForm_spec M).2.2,ha.isRoot.norm]
    norm_num
  refine ⟨v₀,?_,orbitSpline_self cs basis y v₀⟩
  simp only [orbitSpline,hxy,ha.formula,hv₀]
  congr 1
  module

end
end KLInvariance.TitsSpace
end

end OAI
