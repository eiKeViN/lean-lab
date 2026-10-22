module
public import Mathlib
public import OAI.KL.BottSamelson.Character

public section

/-! Semantic home: OAI.KL.Sheaves.Reciprocity. Source spans: CharacterReciprocity:29, CharacterReciprocity:30, CharacterReciprocity:32.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.BruhatGraph
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph
universe u
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W) (b : W)
  {σ : Type u} [Fintype σ] (basis : Basis σ ℝ (Extended M))
noncomputable section

 theorem boundarySheaf_perfectPairing :
    Nonempty (GradedSheaf.PerfectPairing
      (boundarySheaf cs 1 b basis (one_bruhat cs b)).sheaf (cs.length b : ℤ)) := by
  classical
  let := interval_finite cs 1 b
  let := Fintype.ofFinite (Interval cs 1 b)
  let := Fintype.ofFinite (Edge cs 1 b)
  let S := symmetricBoundarySheaf cs basis b
  let T := boundarySheaf cs 1 b basis (one_bruhat cs b)
  let e := SymmetricAlgebra.equivMvPolynomial basis
  have he : ∀ n a, a∈symmetricGrading basis n ↔ e a∈polynomialGrading ℝ σ n :=
    mem_symmetricGrading basis
  obtain ⟨p⟩ := symmetricBoundarySheaf_perfectPairing cs basis b
  obtain ⟨j⟩ := BoundarySheaf.iso_coefficientChange e he S T
    (polynomialGrading_zero ℝ σ) (fun x => x.property.2)
  exact ⟨(p.coefficientChange e he).pullback j⟩

 variable [Fintype (Edge cs 1 b)] [Fintype (Interval cs 1 b)] [DecidableEq (Interval cs 1 b)]

 theorem sectionDualityObligation : SectionDualityObligation cs b basis := by
  obtain ⟨p⟩ := boundarySheaf_perfectPairing cs b basis
  exact sectionDualityObligation_of_perfectPairing cs b basis p

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

@[expose] local instance finiteInterval : Fintype (Interval cs 1 b) := by
  let := interval_finite cs 1 b
  exact Fintype.ofFinite _
@[expose] local instance finiteEdges : Fintype (Edge cs 1 b) := Fintype.ofFinite _
@[expose] local instance _root_.OAI.KLInvariance.BruhatGraph.instDecidableEq_oAI (a : Type*) : DecidableEq a := Classical.decEq a

 @[expose] def boundaryFreeSheaf : FreeSheaf cs 1 b basis where
  sheaf := (boundarySheaf cs 1 b basis (one_bruhat cs b)).sheaf
  free := (boundarySheaf cs 1 b basis (one_bruhat cs b)).free
  quotient := (boundarySheaf cs 1 b basis (one_bruhat cs b)).quotient
  generated := (boundarySheaf cs 1 b basis (one_bruhat cs b)).generated

 @[expose] def boundaryPerfectPairing : GradedSheaf.PerfectPairing
    (boundaryFreeSheaf cs b basis).sheaf (cs.length b : ℤ) :=
  (boundarySheaf_perfectPairing cs b basis).some

 @[expose] def boundaryFreeDuality : FreeSheaf.SectionDuality cs 1 b basis (boundaryFreeSheaf cs b basis) :=
  FreeSheaf.dualityOfPairing cs 1 b basis _ (boundaryPerfectPairing cs b basis)

 theorem boundaryKernelFree (x : Interval cs 1 b) :
    Module.Free (Coefficient (σ := σ))
      (GradedSheaf.kernelData (boundaryFreeSheaf cs b basis).sheaf x) :=
  FreeSheaf.kernel_free cs b basis _ (boundaryFreeDuality cs b basis) x

 @[expose] def costalkCharacter (x : Interval cs 1 b) : Polynomial ℤ :=
  GradedSheaf.freeKernelChar (boundaryFreeSheaf cs b basis).sheaf (boundaryKernelFree cs b basis) x

 theorem costalkCharacter_reflect (x : Interval cs 1 b) :
    costalkCharacter cs b basis x=Polynomial.reflect (rankDifference cs x.val b)
      (stalkCharacter cs 1 b basis (one_bruhat cs b) x) := by
  apply FreeSheaf.kernel_character cs b basis _ (boundaryFreeDuality cs b basis) (cs.length b) _ le_rfl x
  intro i j m a hm ha
  exact (boundaryPerfectPairing cs b basis).homogeneous i j m a
    (fun x => hm x (Set.mem_univ x)) (fun x => ha x (Set.mem_univ x))

 theorem stalkBasis_degree_le (x : Interval cs 1 b)
    (c : NonnegativeBasis (σ := σ)
      ((boundaryFreeSheaf cs b basis).sheaf.vertex x).piece) (i : c.index) :
    c.degree i≤rankDifference cs x.val b := by
  apply ModuleData.degree_le_of_dual_equiv _ _
    (FreeSheaf.kernelDual cs b basis _ (boundaryFreeDuality cs b basis) x)
    (rankDifference cs x.val b) _ c i
  exact FreeSheaf.kernelDual_homogeneous cs b basis _ (boundaryFreeDuality cs b basis)
    (cs.length b) (fun i j m a hm ha => (boundaryPerfectPairing cs b basis).homogeneous i j m a
      (fun x => hm x (Set.mem_univ x)) (fun x => ha x (Set.mem_univ x)))
    x (length_le_of_bruhat cs x.property.2)

end
end KLInvariance.BruhatGraph
end


section
namespace KLInvariance.BruhatGraph
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph Polynomial
universe u
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W) (b : W)
  {σ : Type u} [Fintype σ] (basis : Basis σ ℝ (Extended M))
noncomputable section
@[expose] local instance _root_.OAI.KLInvariance.BruhatGraph.instDecidable_oAI_2 (p : Prop) : Decidable p := Classical.propDecidable p

 @[expose] def lowerKernelEquiv (c x : Interval cs 1 b) (hx : x≤c) :
    GradedSheaf.kernelData ((boundaryModels cs b basis).sheaf c) x ≃ₗ[Coefficient (σ := σ)]
      GradedSheaf.kernelData (boundaryFreeSheaf cs c.val basis).sheaf ⟨x.val,x.property.1,hx⟩ :=
  ((lowerIntervalBoundary cs b basis c).sheaf.lowerExtendKernelEquiv ⟨x,hx⟩).trans
    ((boundaryFreeSheaf cs c.val basis).sheaf.pullbackKernelEquiv
      (lowerIntervalMap cs b c) (lowerIntervalMap_outgoing cs b c) ⟨x,hx⟩)

 theorem lowerKernelEquiv_graded (c x : Interval cs 1 b) (hx : x≤c)
    (n : ℤ) (v : GradedSheaf.kernelData ((boundaryModels cs b basis).sheaf c) x)
    (hv : v∈(GradedSheaf.kernelData ((boundaryModels cs b basis).sheaf c) x).piece n) :
    lowerKernelEquiv cs b basis c x hx v∈(GradedSheaf.kernelData
      (boundaryFreeSheaf cs c.val basis).sheaf ⟨x.val,x.property.1,hx⟩).piece n :=
  (lowerIntervalBoundary cs b basis c).sheaf.lowerExtendKernelEquiv_graded ⟨x,hx⟩ n v hv

 theorem boundaryModels_kernelFree (c x : Interval cs 1 b) :
    Module.Free (Coefficient (σ := σ))
      (GradedSheaf.kernelData ((boundaryModels cs b basis).sheaf c) x) := by
  by_cases hx : x≤c
  · let := boundaryKernelFree cs c.val basis ⟨x.val,x.property.1,hx⟩
    exact Module.Free.of_equiv (lowerKernelEquiv cs b basis c x hx).symm
  · let := (boundaryModels cs b basis).support c x hx
    let : Subsingleton (GradedSheaf.kernelData ((boundaryModels cs b basis).sheaf c) x) :=
      ⟨fun v w => Subtype.ext (Subsingleton.elim _ _)⟩
    infer_instance

 theorem boundaryModels_kernelCharacter (c x : Interval cs 1 b) :
    GradedSheaf.freeKernelChar ((boundaryModels cs b basis).sheaf c)
      (boundaryModels_kernelFree cs b basis c) x=
      Polynomial.reflect (rankDifference cs x.val c.val) (lowerCharacter cs b basis c x) := by
  let := boundaryModels_kernelFree cs b basis c x
  by_cases hx : x≤c
  · rw [lowerCharacter,dite_eq_left hx,← costalkCharacter_reflect cs c.val basis ⟨x.val,x.property.1,hx⟩]
    let := boundaryKernelFree cs c.val basis ⟨x.val,x.property.1,hx⟩
    exact ModuleData.character_eq_of_gradedEquiv (lowerKernelEquiv cs b basis c x hx)
      (lowerKernelEquiv_graded cs b basis c x hx)
  · rw [lowerCharacter,dite_eq_right hx,Polynomial.reflect_zero]
    let := (boundaryModels cs b basis).support c x hx
    let : Subsingleton (GradedSheaf.kernelData ((boundaryModels cs b basis).sheaf c) x) :=
      ⟨fun v w => Subtype.ext (Subsingleton.elim _ _)⟩
    exact ModuleData.char_zero _

end
end KLInvariance.BruhatGraph
end

end OAI
