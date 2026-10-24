module
public import Mathlib
public import ForMathlib.Algebra.Module.Graded.NonnegativeBasis
public import ForMathlib.Combinatorics.MomentGraph.Bruhat.Basic
public import ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Extension
public import ForMathlib.GroupTheory.Coxeter.Bruhat.Descent
public import ForMathlib.GroupTheory.Coxeter.Roots.Basic
public import ForMathlib.LinearAlgebra.SymmetricAlgebra.RootIdeal
public import ForMathlib.RepresentationTheory.KazhdanLusztig.Polynomials.Normalized

public section

/-! Semantic home: OAI.KL.Sheaves.Boundary. Source spans: SheafMorphisms:3, SheafMorphisms:4, SheafMorphisms:6.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.BruhatGraph
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W) (u b : W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
noncomputable section


abbrev Coefficient := MvPolynomial σ ℝ

@[expose] def root (e : Edge cs u b) : PositiveRoot M cs :=
  positiveRootEquiv M cs ⟨label cs u b e,label_isReflection cs u b e⟩

@[expose] def polynomialLabel (e : Edge cs u b) : Coefficient (σ := σ) :=
  SymmetricAlgebra.equivMvPolynomial basis
    (SymmetricAlgebra.ι ℝ (Extended M) (embed M (root cs u b e).val))

 theorem polynomialLabel_homogeneous (e : Edge cs u b) :
    polynomialLabel cs u b basis e ∈ polynomialGrading ℝ σ 1 := by
  classical
  unfold polynomialLabel
  rw [← basis.sum_repr (embed M (root cs u b e).val)]
  simp only [map_sum,map_smul,SymmetricAlgebra.equivMvPolynomial_ι_apply]
  apply Submodule.sum_mem
  intro i _
  exact (polynomialGrading ℝ σ 1).smul_mem _
    (MvPolynomial.isWeightedHomogeneous_X ℝ (fun _ : σ => (1 : ℤ)) i)

omit [Fintype σ] in
 theorem polynomialLabel_ne_zero (e : Edge cs u b) :
    polynomialLabel cs u b basis e ≠ 0 := by
  intro he
  have h0 : SymmetricAlgebra.ι ℝ (Extended M) (embed M (root cs u b e).val) = 0 :=
    (SymmetricAlgebra.equivMvPolynomial basis).injective
      (he.trans (map_zero _).symm)
  have h1 : embed M (root cs u b e).val = 0 :=
    EdgeAlgebra.symmetric_ι_injective (k := ℝ) (h0.trans (map_zero _).symm)
  have h2 := congrArg Prod.fst h1
  exact (root cs u b e).property.1.ne_zero h2


 theorem exists_boundarySheaf (hub : BruhatLE cs u b) :
    Nonempty (BoundarySheaf (polynomialGrading_negative ℝ σ)
      (graph cs u b) (polynomialLabel cs u b basis) ⟨b,hub,bruhat_refl cs b⟩) := by
  classical
  let : Finite (Interval cs u b) := interval_finite cs u b
  let : Fintype (Interval cs u b) := Fintype.ofFinite _
  let : Fintype (Edge cs u b) := Fintype.ofFinite _
  exact MomentGraph.exists_boundarySheaf (polynomialGrading_negative ℝ σ)
    (graph cs u b) (polynomial_scalar_mod_positive ℝ σ)
    ⟨b,hub,bruhat_refl cs b⟩ (fun x => x.property.2)
    (polynomialLabel cs u b basis) (polynomialLabel_homogeneous cs u b basis)

end
end KLInvariance.BruhatGraph
end


section
namespace KLInvariance.BruhatGraph
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W) (u b : W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  (hub : BruhatLE cs u b)
noncomputable section

@[expose] def boundarySheaf : BoundarySheaf (polynomialGrading_negative ℝ σ)
    (graph cs u b) (polynomialLabel cs u b basis) ⟨b,hub,bruhat_refl cs b⟩ :=
  (exists_boundarySheaf cs u b basis hub).some

@[expose] def stalkCharacter (x : Interval cs u b) : Polynomial ℤ := by
  let B := boundarySheaf cs u b basis hub
  let := B.free x
  exact Graded.character (σ := σ) (B.sheaf.vertex x).piece (B.sheaf.vertex x).nonneg

 theorem stalkCharacter_coeff_nonneg (x : Interval cs u b) (n : ℕ) :
    0 ≤ (stalkCharacter cs u b basis hub x).coeff n := by
  let B := boundarySheaf cs u b basis hub
  let := B.free x
  exact Graded.character_coeff_nonneg (σ := σ) (B.sheaf.vertex x).piece
    (B.sheaf.vertex x).nonneg n


@[expose] def StalkCharacterObligation : Prop :=
  ∀ x : Interval cs u b, stalkCharacter cs u b basis hub x = klPolynomial cs x.val b


@[expose] def CostalkFreeObligation : Prop :=
  ∀ x : Interval cs u b, Module.Free (Coefficient (σ := σ))
    (LinearMap.ker ((boundarySheaf cs u b basis hub).sheaf.forget.stalkMap x))

end
end KLInvariance.BruhatGraph
end


section
namespace KLInvariance.BruhatGraph
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph
universe u
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W) (b : W)
  {σ : Type u} [Fintype σ] (basis : Basis σ ℝ (Extended M))
noncomputable section
local instance _root_.OAI.KLInvariance.BruhatGraph.instDecidable_oAI (p : Prop) : Decidable p := Classical.propDecidable p

 abbrev lowerIdealGraph (c : Interval cs 1 b) :=
  lowerGraph (graph cs 1 b) (Set.Iic c) (isLowerSet_Iic c)

 @[expose] def lowerIntervalMap (c : Interval cs 1 b) :
    GraphMap (lowerIdealGraph cs b c) (graph cs 1 c.val) where
  vertex x := ⟨x.val.val,x.val.property.1,x.property⟩
  edge e := ⟨(⟨(source cs 1 b e.val).val,(source cs 1 b e.val).property.1,
      bruhat_trans cs (.single e.val.property) e.property⟩,
    ⟨(target cs 1 b e.val).val,(target cs 1 b e.val).property.1,e.property⟩),e.val.property⟩
  source _ := rfl
  target _ := rfl

 omit [Fintype I] in
 theorem lowerIntervalMap_injective (c : Interval cs 1 b) :
    Function.Injective (lowerIntervalMap cs b c).vertex := by
  intro x y h
  exact Subtype.ext (Subtype.ext (show x.val.val=y.val.val from
    congrArg (fun z : Interval cs 1 c.val => z.val) h))

 omit [Fintype I] in
 theorem lowerIntervalMap_outgoing (c : Interval cs 1 b)
    (e : Edge cs 1 c.val) (x : Set.Iic c)
    (hx : (lowerIntervalMap cs b c).vertex x=source cs 1 c.val e) :
    ∃ a, (lowerIntervalMap cs b c).edge a=e ∧ (lowerIdealGraph cs b c).source a=x := by
  have hxx := congrArg Subtype.val hx
  let y : Interval cs 1 b := ⟨(target cs 1 c.val e).val,(target cs 1 c.val e).property.1,
    bruhat_trans cs (target cs 1 c.val e).property.2 c.property.2⟩
  let a : Edge cs 1 b := ⟨(x.val,y),hxx.symm ▸ e.property⟩
  refine ⟨⟨a,(target cs 1 c.val e).property.2⟩,?_,?_⟩
  · apply Subtype.ext
    exact Prod.ext hx rfl
  · rfl

 @[expose] def lowerIntervalBoundary (c : Interval cs 1 b) :
    BoundarySheaf (polynomialGrading_negative ℝ σ) (lowerIdealGraph cs b c)
      (fun e => polynomialLabel cs 1 b basis e.val) ⟨c,Set.mem_Iic.mpr le_rfl⟩ :=
  (boundarySheaf cs 1 c.val basis (one_bruhat cs c.val)).pullback
    (lowerIntervalMap cs b c) (lowerIntervalMap_injective cs b c)
    (lowerIntervalMap_outgoing cs b c) ⟨c,Set.mem_Iic.mpr le_rfl⟩ rfl

 @[expose] def boundaryModels : GradedSheaf.BoundaryModels (polynomialGrading_negative ℝ σ)
    (G := graph cs 1 b) (polynomialLabel cs 1 b basis) where
  sheaf c := (lowerIntervalBoundary cs b basis c).sheaf.lowerExtend
  free c := (lowerIntervalBoundary cs b basis c).sheaf.lowerExtend_free
    (lowerIntervalBoundary cs b basis c).free
  quotient c := (lowerIntervalBoundary cs b basis c).sheaf.lowerExtend_quotient _
    (lowerIntervalBoundary cs b basis c).quotient
  generated c := (lowerIntervalBoundary cs b basis c).sheaf.lowerExtend_generated
    (lowerIntervalBoundary cs b basis c).generated
  flabby c := (lowerIntervalBoundary cs b basis c).sheaf.lowerExtend_flabby
    (lowerIntervalBoundary cs b basis c).flabby.flabby
  support c x hx := (lowerIntervalBoundary cs b basis c).sheaf.lowerExtend_support x hx
  top c := ((lowerIntervalBoundary cs b basis c).sheaf.lowerExtendVertex ⟨c,Set.mem_Iic.mpr le_rfl⟩).trans
    (ModuleData.equivOfEq (lowerIntervalBoundary cs b basis c).top)
  top_graded c n v hv := ModuleData.equivOfEq_graded (lowerIntervalBoundary cs b basis c).top n _
    ((lowerIntervalBoundary cs b basis c).sheaf.lowerExtendVertex_graded ⟨c,Set.mem_Iic.mpr le_rfl⟩ n v hv)
  minimal c x hx := (lowerIntervalBoundary cs b basis c).sheaf.lowerExtend_minimal x
    (fun hxc => (lowerIntervalBoundary cs b basis c).minimal ⟨x,hxc⟩
      (fun hh => hx (congrArg Subtype.val hh)))

end
end KLInvariance.BruhatGraph
end

end OAI
