module
public import Mathlib
public import ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Character
public import OAI.KL.Sheaves.Boundary

public section

/-! Semantic home: OAI.KL.Sheaves.LowerCharacter. Source spans: Decomposition:2.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.BruhatGraph
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph Polynomial
universe u
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W) (b : W)
  {σ : Type u} [Fintype σ] (basis : Basis σ ℝ (Extended M))
noncomputable section
@[expose] local instance _root_.OAI.KLInvariance.BruhatGraph.instDecidable_oAI_1 (p : Prop) : Decidable p := Classical.propDecidable p

 @[expose] def lowerCharacter (c x : Interval cs 1 b) : Polynomial ℤ :=
  if h : x≤c then stalkCharacter cs 1 c.val basis (one_bruhat cs c.val)
    ⟨x.val,x.property.1,h⟩ else 0

 theorem boundaryModels_character (c x : Interval cs 1 b) :
    GradedSheaf.freeStalkChar ((boundaryModels cs b basis).sheaf c)
      ((boundaryModels cs b basis).free c) x=lowerCharacter cs b basis c x := by
  let _ := (boundaryModels cs b basis).free c x
  by_cases hx : x≤c
  · rw [lowerCharacter,dite_eq_left hx]
    let B := lowerIntervalBoundary cs b basis c
    let _ := B.sheaf.lowerExtend_free B.free x
    let _ := (boundarySheaf cs 1 c.val basis (one_bruhat cs c.val)).free ⟨x.val,x.property.1,hx⟩
    exact ModuleData.character_eq_of_gradedEquiv (B.sheaf.lowerExtendVertex ⟨x,hx⟩)
      (B.sheaf.lowerExtendVertex_graded ⟨x,hx⟩)
  · rw [lowerCharacter,dite_eq_right hx]
    let _ := (boundaryModels cs b basis).support c x hx
    exact ModuleData.char_zero _

 theorem lowerCharacter_zero (c x : Interval cs 1 b) (hx : ¬x≤c) :
    lowerCharacter cs b basis c x=0 := dite_eq_right hx

 theorem lowerCharacter_nonneg (c x : Interval cs 1 b) (n : ℕ) :
    0≤(lowerCharacter cs b basis c x).coeff n := by
  unfold lowerCharacter
  split
  · exact stalkCharacter_coeff_nonneg cs 1 c.val basis (one_bruhat cs c.val) _ n
  · simp

end
end KLInvariance.BruhatGraph
end

end OAI
