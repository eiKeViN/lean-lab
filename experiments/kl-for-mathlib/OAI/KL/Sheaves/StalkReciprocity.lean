import Mathlib
import ForMathlib.Algebra.BigOperators.SingleCoordinate
import OAI.KL.BottSamelson.CharacterDecomposition

/-! Semantic home: OAI.KL.Sheaves.StalkReciprocity. Source spans: DyerPaths:2.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.BruhatGraph
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph Polynomial
universe u
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W)
  {σ : Type u} [Fintype σ] (basis : Basis σ ℝ (Extended M))
noncomputable section
local instance _root_.OAI.KLInvariance.BruhatGraph.instDecidable_oAI_5 (p : Prop) : Decidable p := Classical.propDecidable p
local instance bmpRecInterval (b : W) : Fintype (Interval cs 1 b) := by
  let := interval_finite cs 1 b
  exact Fintype.ofFinite _

 theorem stalkCharacter_reciprocity (b : W) (x : Interval cs 1 b) :
    reflect (rankDifference cs x.val b) (stalkCharacter cs 1 b basis (one_bruhat cs b) x)=
      ∑ z : Interval cs 1 b, OrdinaryR.polynomial cs x.val z.val*
        stalkCharacter cs 1 b basis (one_bruhat cs b) z := by
  generalize hn : cs.length b=n
  induction n using Nat.strong_induction_on generalizing b with
  | h n ih =>
    obtain ⟨l,hl,rfl⟩ := cs.exists_isReduced b
    let b := cs.wordProd l
    let t : Interval cs 1 b := ⟨b,one_bruhat cs b,bruhat_refl cs b⟩
    obtain ⟨m,_hm,hs,hk⟩ := bottCharacter_decomposition_both cs basis l hl
    have hmt : m t=1 := by
      have hh := hs t
      rw [bottStalkCharacter_top cs basis l hl] at hh
      rw [Finset.sum_eq_single t] at hh
      · simpa only [lowerCharacter_diagonal,mul_one] using hh.symm
      · intro y _ hy
        have hv : y.val≠b := fun h => hy (Subtype.ext h)
        rw [lowerCharacter_at_top,ite_eq_right hv,mul_zero]
      · simp
    have ht (z : Interval cs 1 b) : lowerCharacter cs b basis t z=
        stalkCharacter cs 1 b basis (one_bruhat cs b) z := dite_eq_left z.property.2
    have hw : (∑ y, m y*reflect (rankDifference cs x.val y.val) (lowerCharacter cs b basis y x))=
        ∑ z : Interval cs 1 b, OrdinaryR.polynomial cs x.val z.val*
          (∑ y, m y*lowerCharacter cs b basis y z) := by
      rw [←hk x,bottKernelCharacter_rConvolution cs basis l hl x]
      simp only [hs]
      rfl
    have hh := finite_character_cancellation t m
      (fun z : Interval cs 1 b => OrdinaryR.polynomial cs x.val z.val)
      (fun y z => lowerCharacter cs b basis y z)
      (fun y => reflect (rankDifference cs x.val y.val) (lowerCharacter cs b basis y x))
      hmt hw (fun y hy => ?_)
    · simpa only [ht] using hh
    · apply lowerCharacter_reciprocity_lift
      intro z
      apply ih (cs.length y.val) _ y.val z rfl
      rw [←hn]
      exact length_lt_of_bruhat_ne cs y.property.2 (fun he => hy (Subtype.ext he))

end
end KLInvariance.BruhatGraph
end

end OAI
