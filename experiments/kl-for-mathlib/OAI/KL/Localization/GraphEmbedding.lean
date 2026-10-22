import Mathlib
import ForMathlib.GroupTheory.Coxeter.Roots.Splines
import ForMathlib.LinearAlgebra.PlaneReduction
import ForMathlib.LinearAlgebra.SymmetricAlgebra.Quotient
import OAI.KL.Localization.Ambient

/-! Semantic home: OAI.KL.Localization.GraphEmbedding. Source spans: PlaneLocalization:7, PlaneLocalization:24, PlaneLocalization:27.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.TitsSpace
open Module
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {σ : Type us} (basis : Basis σ ℝ (Extended M))
noncomputable section

 def embedLinear : (I → ℝ) →ₗ[ℝ] Extended M where
  toFun := embed M
  map_add' _ _ := by simp [embed]
  map_smul' _ _ := by simp [embed]

 theorem embedLinear_injective : Function.Injective (embedLinear (M := M)) := by
  intro a b hab
  exact congrArg Prod.fst hab

 def planePrime (P : Submodule ℝ (I → ℝ)) : Ideal (MvPolynomial σ ℝ) :=
  Ideal.map (SymmetricAlgebra.equivMvPolynomial basis).toRingHom
    (SymmetricPlaneIdeal.ideal (P.map (embedLinear (M := M))))

 instance planePrime_isPrime (P : Submodule ℝ (I → ℝ)) : (planePrime basis P).IsPrime :=
  Ideal.map_isPrime_of_equiv (SymmetricAlgebra.equivMvPolynomial basis)

 theorem linear_mem_planePrime_iff (P : Submodule ℝ (I → ℝ)) (a : I → ℝ) :
    linearPolynomial basis (embed M a) ∈ planePrime basis P ↔ a ∈ P := by
  rw [planePrime,Ideal.mem_map_iff_of_surjective (SymmetricAlgebra.equivMvPolynomial basis).toRingHom
    (SymmetricAlgebra.equivMvPolynomial basis).surjective]
  change (∃ z, z ∈ SymmetricPlaneIdeal.ideal (P.map (embedLinear (M := M))) ∧
    SymmetricAlgebra.equivMvPolynomial basis z =
      SymmetricAlgebra.equivMvPolynomial basis (SymmetricAlgebra.ι ℝ (Extended M) (embed M a))) ↔ _
  constructor
  · rintro ⟨z,hz,he⟩
    have h := (SymmetricAlgebra.equivMvPolynomial basis).injective he
    subst z
    have ha := (SymmetricPlaneIdeal.ι_mem_iff _ _).mp hz
    obtain ⟨b,hb,he⟩ := ha
    have he' : b = a := embedLinear_injective he
    exact he' ▸ hb
  · intro ha
    refine ⟨_,(SymmetricPlaneIdeal.ι_mem_iff _ _).mpr ?_,rfl⟩
    exact ⟨a,ha,rfl⟩

 abbrev PlaneRing (P : Submodule ℝ (I → ℝ)) := Localization.AtPrime (planePrime basis P)

 theorem linear_mem_maximal_iff (P : Submodule ℝ (I → ℝ)) (a : I → ℝ) :
    algebraMap (MvPolynomial σ ℝ) (PlaneRing basis P) (linearPolynomial basis (embed M a)) ∈
      IsLocalRing.maximalIdeal (PlaneRing basis P) ↔ a ∈ P := by
  rw [IsLocalization.AtPrime.to_map_mem_maximal_iff _ (planePrime basis P),
    linear_mem_planePrime_iff]

 theorem linear_isUnit_iff (P : Submodule ℝ (I → ℝ)) (a : I → ℝ) :
    IsUnit (algebraMap (MvPolynomial σ ℝ) (PlaneRing basis P)
      (linearPolynomial basis (embed M a))) ↔ a ∉ P := by
  rw [IsLocalization.AtPrime.isUnit_to_map_iff _ (planePrime basis P)]
  change _ ∉ planePrime basis P ↔ _
  rw [linear_mem_planePrime_iff]

end
end KLInvariance.TitsSpace
end


section
namespace KLInvariance.TitsSpace
open Module
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {σ : Type us} (basis : Basis σ ℝ (Extended M))
noncomputable section

 def localizedLinear (P : Submodule ℝ (I → ℝ)) : (I → ℝ) →ₗ[ℝ] PlaneRing basis P :=
  (IsScalarTower.toAlgHom ℝ (MvPolynomial σ ℝ) (PlaneRing basis P)).toLinearMap.comp
    ((linearPolynomial basis).comp (embedLinear (M := M)))

 def localizedEdgeIdeal (P : Submodule ℝ (I → ℝ)) (a : I → ℝ) : Ideal (PlaneRing basis P) :=
  Ideal.span {localizedLinear basis P a}

 abbrev LocalizedEdgeRing (P : Submodule ℝ (I → ℝ)) (a : I → ℝ) :=
  PlaneRing basis P ⧸ localizedEdgeIdeal basis P a

 def localizedReduction (P : Submodule ℝ (I → ℝ)) (a : I → ℝ) :
    (I → ℝ) →ₗ[ℝ] LocalizedEdgeRing basis P a :=
  (Ideal.Quotient.mkₐ ℝ (localizedEdgeIdeal basis P a)).toLinearMap.comp
    (localizedLinear basis P)

 theorem localizedReduction_self (P : Submodule ℝ (I → ℝ)) (a : I → ℝ) :
    localizedReduction basis P a a = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))

 theorem positiveRoot_not_line {a c : PositiveRoot M cs} (hca : c ≠ a) :
    c.val ∉ Submodule.span ℝ ({a.val} : Set (I → ℝ)) := by
  intro h
  obtain ⟨r,hr⟩ := Submodule.mem_span_singleton.mp h
  exact (linearIndependent_fin2.mp (positiveRoots_independent c a hca)).2 r hr

 theorem localizedReduction_associated (P : Submodule ℝ (I → ℝ))
    (a b c : PositiveRoot M cs) (hc : c.val ∈ rootPlane a b) (hca : c ≠ a) :
    Associated (localizedReduction basis P a.val c.val)
      (localizedReduction basis P a.val b.val) :=
by
  exact @PlaneReduction.associated_reduction ℝ _ (I → ℝ) _ _
    (LocalizedEdgeRing basis P a.val) _ _ (localizedReduction basis P a.val)
    a.val b.val c.val (localizedReduction_self basis P a.val) hc
    (positiveRoot_not_line hca)

end
end KLInvariance.TitsSpace
end


section
namespace KLInvariance.TitsSpace
open Module BruhatGraph
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {σ : Type us} (basis : Basis σ ℝ (Extended M))
noncomputable section

 theorem polynomialRoot_localized (P : Submodule ℝ (I → ℝ)) (a : PositiveRoot M cs) :
    algebraMap (MvPolynomial σ ℝ) (PlaneRing basis P) (polynomialRoot cs basis a) =
      localizedLinear basis P a.val := rfl

 theorem polynomialRoot_reduced (P : Submodule ℝ (I → ℝ)) (a c : PositiveRoot M cs) :
    algebraMap (PlaneRing basis P) (LocalizedEdgeRing basis P a.val)
      (algebraMap (MvPolynomial σ ℝ) (PlaneRing basis P) (polynomialRoot cs basis c)) =
      localizedReduction basis P a.val c.val := rfl

 theorem planeRoot_outside {x : W} {a b : PositiveRoot M cs} (hab : a ≠ b)
    (Q : (planeWeight x a).support) (hQ : Q.val ≠ rootPlane a b) :
    (planeRoot x a Q).val ∉ rootPlane a b := by
  intro h
  apply hQ
  rw [← planeRoot_plane x a Q]
  exact rootPlane_eq_of_mem a b a (planeRoot x a Q) hab
    (Submodule.subset_span (Set.mem_insert _ _)) h (planeRoot_ne x a Q).symm

 theorem reduced_planeRoot_other_isUnit {x : W} {a b : PositiveRoot M cs} (hab : a ≠ b)
    (Q : (planeWeight x a).support) (hQ : Q.val ≠ rootPlane a b) :
    IsUnit (localizedReduction basis (rootPlane a b) a.val (planeRoot x a Q).val) := by
  have h := (linear_isUnit_iff basis (rootPlane a b) (planeRoot x a Q).val).mpr
    (planeRoot_outside hab Q hQ)
  exact h.map (algebraMap (PlaneRing basis (rootPlane a b))
    (LocalizedEdgeRing basis (rootPlane a b) a.val))

/-- The actual integral edge factor reduces, in each actual plane, to precisely
its plane weight. All other factors are proven units, not discarded formally. -/
 theorem edgeFactor_local_associated (x : W) (a b : PositiveRoot M cs) (hab : a ≠ b) :
    Associated
      (algebraMap (PlaneRing basis (rootPlane a b)) (LocalizedEdgeRing basis (rootPlane a b) a.val)
        (algebraMap (MvPolynomial σ ℝ) (PlaneRing basis (rootPlane a b)) (edgeFactorLift cs basis x a)))
      ((localizedReduction basis (rootPlane a b) a.val b.val)^((planeWeight x a (rootPlane a b)).toNat)) := by
  classical
  let p := localizedReduction basis (rootPlane a b) a.val b.val
  have hfactor (Q : (planeWeight x a).support) :
      Associated
        ((localizedReduction basis (rootPlane a b) a.val (planeRoot x a Q).val)^((planeWeight x a Q.val).toNat))
        (if Q.val=rootPlane a b then p^((planeWeight x a (rootPlane a b)).toNat) else 1) := by
    by_cases hQ : Q.val=rootPlane a b
    · rw [ite_eq_left hQ]
      have hc : (planeRoot x a Q).val ∈ rootPlane a b := by
        rw [← hQ,← planeRoot_plane x a Q]
        exact Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
      have h := localizedReduction_associated basis (rootPlane a b) a b (planeRoot x a Q)
        hc (planeRoot_ne x a Q)
      simpa only [hQ] using (Associated.pow_pow (M := LocalizedEdgeRing basis (rootPlane a b) a.val) h (n := (planeWeight x a Q.val).toNat))
    · rw [ite_eq_right hQ]
      exact associated_one_iff_isUnit.mpr ((reduced_planeRoot_other_isUnit basis hab Q hQ).pow _)
  have hprod := Associated.prod Finset.univ
    (fun Q : (planeWeight x a).support =>
      (localizedReduction basis (rootPlane a b) a.val (planeRoot x a Q).val)^((planeWeight x a Q.val).toNat))
    (fun Q => if Q.val=rootPlane a b then p^((planeWeight x a (rootPlane a b)).toNat) else 1)
    (fun Q _ => hfactor Q)
  have hp : (∏ Q : (planeWeight x a).support,
      if Q.val=rootPlane a b then p^((planeWeight x a (rootPlane a b)).toNat) else 1) =
      p^((planeWeight x a (rootPlane a b)).toNat) := by
    rw [Fintype.prod_ite_eq_ite_exists _ (fun i j hi hj => Subtype.ext (hi.trans hj.symm))]
    by_cases hP : rootPlane a b ∈ (planeWeight x a).support
    · rw [ite_eq_left ⟨⟨rootPlane a b,hP⟩,rfl⟩]
    · have hz := Finsupp.notMem_support_iff.mp hP
      rw [hz,Int.toNat_zero,pow_zero]
      split_ifs <;> rfl
  rw [hp] at hprod
  simpa only [edgeFactorLift,map_prod,map_pow,polynomialRoot_reduced] using hprod

end
end KLInvariance.TitsSpace
end

end OAI
