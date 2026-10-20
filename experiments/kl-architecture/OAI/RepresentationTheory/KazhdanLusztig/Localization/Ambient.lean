import Mathlib
import OAI.GroupTheory.Coxeter.Roots.LaterCount
import OAI.RepresentationTheory.KazhdanLusztig.Sheaves.Support

/-! Semantic home: OAI.RepresentationTheory.KazhdanLusztig.Localization.Ambient. Source spans: PlaneLocalization:4, PlaneLocalization:25, PlaneLocalization:29, PlaneLocalization:21.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.BruhatGraph
universe u v
variable {I : Type u} {M : CoxeterMatrix I} {W : Type v} [Group W]
  (cs : CoxeterSystem M W) (u b : W)

 theorem exists_outgoing_below (x c : Interval cs u b) (hxc : x < c) :
    ∃ e : Edge cs u b, source cs u b e = x ∧ target cs u b e ≤ c := by
  rcases Relation.ReflTransGen.cases_head hxc.le with heq | ⟨z,hxz,hzc⟩
  · exact (hxc.ne (Subtype.ext heq)).elim
  · let y : Interval cs u b := ⟨z,bruhat_trans cs x.property.1 (.single hxz),
      bruhat_trans cs hzc c.property.2⟩
    exact ⟨⟨(x,y),hxz⟩,rfl,hzc⟩

end KLInvariance.BruhatGraph
end


section
namespace KLInvariance.BruhatGraph
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
noncomputable section

 def polynomialRoot (a : PositiveRoot M cs) : Coefficient (σ := σ) :=
  SymmetricAlgebra.equivMvPolynomial basis
    (SymmetricAlgebra.ι ℝ (Extended M) (embed M a.val))

 theorem polynomialRoot_homogeneous (a : PositiveRoot M cs) :
    polynomialRoot cs basis a ∈ polynomialGrading ℝ σ 1 := by
  classical
  unfold polynomialRoot
  rw [← basis.sum_repr (embed M a.val)]
  simp only [map_sum,map_smul,SymmetricAlgebra.equivMvPolynomial_ι_apply]
  apply Submodule.sum_mem
  intro i _
  exact (polynomialGrading ℝ σ 1).smul_mem _
    (MvPolynomial.isWeightedHomogeneous_X ℝ (fun _ : σ => (1 : ℤ)) i)

omit [Fintype σ] in
 theorem polynomialRoot_prime (a : PositiveRoot M cs) : Prime (polynomialRoot cs basis a) := by
  apply (MulEquiv.prime_iff (SymmetricAlgebra.equivMvPolynomial basis)).mpr
  apply EdgeAlgebra.symmetric_ι_prime
  intro h
  exact a.property.1.ne_zero (congrArg Prod.fst h)

omit [Fintype σ] in
 theorem polynomialRoot_not_dvd {a r : PositiveRoot M cs} (h : r ≠ a) :
    ¬ polynomialRoot cs basis a ∣ polynomialRoot cs basis r := by
  rintro ⟨z,hz⟩
  apply embed_not_rootLine a r h
  apply (EdgeAlgebra.symmetric_ι_dvd_iff _ _).mp
  refine ⟨(SymmetricAlgebra.equivMvPolynomial basis).symm z,?_⟩
  apply (SymmetricAlgebra.equivMvPolynomial basis).injective
  simpa only [map_mul,AlgEquiv.apply_symm_apply,polynomialRoot] using hz


 def edgeFactorLift (x : W) (a : PositiveRoot M cs) : Coefficient (σ := σ) :=
  ∏ P : (planeWeight x a).support,
    polynomialRoot cs basis (planeRoot x a P) ^ (planeWeight x a P.val).toNat

 theorem edgeFactorLift_homogeneous (x : W) (a : PositiveRoot M cs) :
    edgeFactorLift cs basis x a ∈ polynomialGrading ℝ σ (edgeFactorDegree x a : ℤ) := by
  classical
  have h := SetLike.prod_pow_mem_graded (polynomialGrading ℝ σ)
    (fun _ : (planeWeight x a).support => (1 : ℤ))
    (fun P => polynomialRoot cs basis (planeRoot x a P))
    (fun P => (planeWeight x a P.val).toNat)
    (F := Finset.univ) (fun P _ => polynomialRoot_homogeneous cs basis (planeRoot x a P))
  simpa only [edgeFactorLift,edgeFactorDegree,Nat.cast_sum,nsmul_eq_mul,mul_one] using h

omit [Fintype σ] in
 theorem edgeFactorLift_not_dvd (x : W) (a : PositiveRoot M cs) :
    ¬ polynomialRoot cs basis a ∣ edgeFactorLift cs basis x a := by
  classical
  apply (polynomialRoot_prime cs basis a).not_dvd_finsetProd
  intro P _ h
  exact polynomialRoot_not_dvd cs basis (planeRoot_ne x a P)
    ((polynomialRoot_prime cs basis a).dvd_of_dvd_pow h)

omit [Fintype σ] in
 theorem edgeFactorLift_reduction (x : W) (a : PositiveRoot M cs) :
    Ideal.Quotient.mk (EdgeAlgebra.rootIdeal (k := ℝ) (embed M a.val))
      ((SymmetricAlgebra.equivMvPolynomial basis).symm (edgeFactorLift cs basis x a)) =
      edgeFactor x a := by
  simp only [edgeFactorLift,map_prod,map_pow,polynomialRoot,AlgEquiv.symm_apply_apply,
    edgeFactor,reducedPlaneRoot]

variable (u b : W) (hub : BruhatLE cs u b)
  (B : BoundarySheaf (polynomialGrading_negative ℝ σ)
    (graph cs u b) (polynomialLabel cs u b basis) ⟨b,hub,bruhat_refl cs b⟩)

theorem rootRef_root (e : Edge cs u b) :
    rootRef (root cs u b e) = label cs u b e :=
  congrArg Subtype.val ((positiveRootEquiv M cs).left_inv
    ⟨label cs u b e,label_isReflection cs u b e⟩)

 theorem root_not_inverted (e : Edge cs u b) :
    ¬ rootInverted (source cs u b e).val (root cs u b e) := by
  intro h
  have hi := ((rootReflection_represents M cs (root cs u b e)).inversion_iff
    (root cs u b e).property.2 (source cs u b e).val).mp h
  have hl := hi.2
  change cs.length (rootRef (root cs u b e) * (source cs u b e).val) <
    cs.length (source cs u b e).val at hl
  rw [rootRef_root, label_mul_source] at hl
  exact (not_lt_of_ge e.property.1.le) hl

 theorem edgeFactorDegree_edge (e : Edge cs u b) :
    2 * (edgeFactorDegree (source cs u b e).val (root cs u b e) : ℤ) =
      (cs.length (target cs u b e).val : ℤ) - cs.length (source cs u b e).val - 1 := by
  rw [edgeFactorDegree_cast]
  have h := sum_planeWeight (source cs u b e).val (root cs u b e)
    (root_not_inverted cs u b e)
  rwa [rootRef_root, label_mul_source] at h

/-- Multiplication by the genuine plane product on the actual edge module. -/
 def edgeFactorMap (e : Edge cs u b) : B.sheaf.edge e →ₗ[Coefficient (σ := σ)] B.sheaf.edge e :=
  LinearMap.lsmul (Coefficient (σ := σ)) (B.sheaf.edge e)
    (edgeFactorLift cs basis (source cs u b e).val (root cs u b e))

 theorem edgeFactorMap_graded (e : Edge cs u b) (n : ℤ) (v : B.sheaf.edge e)
    (hv : v ∈ (B.sheaf.edge e).piece n) :
    edgeFactorMap cs basis u b hub B e v ∈ (B.sheaf.edge e).piece
      (n + edgeFactorDegree (source cs u b e).val (root cs u b e)) := by
  simpa only [edgeFactorMap,LinearMap.lsmul_apply,vadd_eq_add,add_comm] using
    SetLike.GradedSMul.smul_mem (edgeFactorLift_homogeneous cs basis
      (source cs u b e).val (root cs u b e)) hv

omit [Fintype σ] in
 theorem edgeFactorLift_regular (e : Edge cs u b) :
    Function.Injective (fun v : B.sheaf.edge e =>
      edgeFactorLift cs basis (source cs u b e).val (root cs u b e) • v) := by
  let := B.free ((graph cs u b).target e)
  exact FiniteFreeScalar.scalar_quotient_regular
    (Module.Free.chooseBasis (Coefficient (σ := σ)) (B.sheaf.vertex ((graph cs u b).target e)))
    (B.sheaf.upper e).map (B.quotient e).1
    (polynomialLabel cs u b basis e)
    (edgeFactorLift cs basis (source cs u b e).val (root cs u b e))
    (polynomialLabel_prime cs u b basis e)
    (edgeFactorLift_not_dvd cs basis (source cs u b e).val (root cs u b e)) (B.quotient e).2

end
end KLInvariance.BruhatGraph
end


section
namespace KLInvariance.BruhatGraph
open TitsSpace
universe u v u' v'
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {I' : Type u'} [Fintype I'] {M' : CoxeterMatrix I'}
  {W' : Type v'} [Group W'] {cs' : CoxeterSystem M' W'}
  {u b : W} {u' b' : W'}
  (φ : Interval cs u b ≃o Interval cs' u' b')
noncomputable section

 def upperSource (e : Edge cs 1 b) (hx : BruhatLE cs u (source cs 1 b e).val) : Interval cs u b :=
  ⟨(source cs 1 b e).val,hx,(source cs 1 b e).property.2⟩
 def upperTarget (e : Edge cs 1 b) (hx : BruhatLE cs u (source cs 1 b e).val) : Interval cs u b :=
  ⟨(target cs 1 b e).val,bruhat_trans cs hx (.single e.property),(target cs 1 b e).property.2⟩
 def mappedEdgeRoot (e : Edge cs 1 b) (hx : BruhatLE cs u (source cs 1 b e).val) :
     PositiveRoot M' cs' :=
   graphRoot ((intervalIso_bruhatStep_iff_general cs cs' φ (upperSource e hx) (upperTarget e hx)).mpr e.property)

end
end KLInvariance.BruhatGraph
end


section
namespace KLInvariance.BruhatGraph
open TitsSpace MomentGraph MomentGraph.Sheaf
universe u v u' v'
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {I' : Type u'} [Fintype I'] {M' : CoxeterMatrix I'}
  {W' : Type v'} [Group W'] {cs' : CoxeterSystem M' W'}
  {u b : W} {u' b' : W'}
  (φ : Interval cs u b ≃o Interval cs' u' b')
noncomputable section

 def ambientLater (α : PositiveRoot M' cs') : Set (Edge cs 1 b) :=
  {e | ∃ hx : BruhatLE cs u (source cs 1 b e).val,
    ambientAfterIndicator (φ ⟨(source cs 1 b e).val,hx,(source cs 1 b e).property.2⟩).val α
      (φ ⟨(target cs 1 b e).val,bruhat_trans cs hx (.single e.property),
        (target cs 1 b e).property.2⟩).val = 1}

end
end KLInvariance.BruhatGraph
end

end OAI
