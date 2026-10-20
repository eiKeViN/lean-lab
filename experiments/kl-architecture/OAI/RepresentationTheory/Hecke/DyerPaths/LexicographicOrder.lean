import Mathlib
import OAI.Combinatorics.DirectedPaths.Basic
import OAI.Combinatorics.DirectedPaths.SortedSchedule
import OAI.GroupTheory.Coxeter.Bruhat.Defs
import OAI.GroupTheory.Coxeter.Roots.Basic
import OAI.GroupTheory.Coxeter.Roots.Order
import OAI.GroupTheory.Coxeter.Roots.PlaneBasis
import OAI.GroupTheory.Coxeter.Roots.ReflectionOrder
import OAI.RepresentationTheory.Hecke.DyerPaths.Adapted
import OAI.RepresentationTheory.Hecke.DyerPaths.PlaneCoordinates

/-! Semantic home: OAI.RepresentationTheory.Hecke.DyerPaths.LexicographicOrder. Source spans: ReflectionOrders:5.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.TitsSpace
open Module SchedulePaths AdaptedDyer
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
noncomputable section
local instance _root_.OAI.KLInvariance.TitsSpace.instDecidable_oAI_10 (p : Prop) : Decidable p := Classical.propDecidable p

def lexRootScore (f : Module.Dual ℝ (I → ℝ)) (a : PositiveRoot M cs) : ℝ ×ₗ ℝ :=
  toLex (f (normalizedRoot a),geometricSlope a)

theorem lexRootScore_injective (f : Module.Dual ℝ (I → ℝ)) :
    Function.Injective (lexRootScore (M := M) (cs := cs) f) := by
  intro a b hab
  apply geometricSlope_injective
  exact congrArg (fun p : ℝ ×ₗ ℝ => (ofLex p).2) hab

def lexEdgeScore (f : Module.Dual ℝ (I → ℝ)) (e : AdaptedDyer.Edge cs) : ℝ ×ₗ ℝ :=
  lexRootScore f (rootLabel cs e)

theorem lexEdgeScore_ties (f : Module.Dual ℝ (I → ℝ)) (e e' : AdaptedDyer.Edge cs)
    (he : lexEdgeScore f e=lexEdgeScore f e') : target cs e ≠ source cs e' := by
  intro hj
  exact rootLabel_ne_of_join cs e e' hj (lexRootScore_injective f he)

omit [Fintype I] in
theorem lex_affine_nonneg {c d x y : ℝ} (hc : 0 ≤ c)
    (h : (toLex (c*x+d,x) : ℝ ×ₗ ℝ) ≤ toLex (c*y+d,y)) : x ≤ y := by
  rcases Prod.Lex.toLex_le_toLex.mp h with h | h
  · by_contra hn
    have hxy : y < x := lt_of_not_ge hn
    nlinarith [mul_nonneg hc (sub_nonneg.mpr hxy.le)]
  · exact h.2

omit [Fintype I] in
theorem lex_affine_neg {c d x y : ℝ} (hc : c < 0)
    (h : (toLex (c*x+d,x) : ℝ ×ₗ ℝ) ≤ toLex (c*y+d,y)) : y ≤ x := by
  rcases Prod.Lex.toLex_le_toLex.mp h with h | h
  · by_contra hn
    have hxy : x < y := lt_of_not_ge hn
    nlinarith [mul_nonpos_of_nonpos_of_nonneg hc.le (sub_nonneg.mpr hxy.le)]
  · have he : x=y := by nlinarith [h.1]
    exact he.symm.le

namespace PlaneBasis
variable {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)

include B in
/-- Any linearly sorted full plane block is either angularly sorted or
reverse-angularly sorted. This includes tied primary labels refined by the
fixed genuine geometric functional. -/
theorem lex_block_orientation (f : Module.Dual ℝ (I → ℝ))
    (p : List (AdaptedDyer.Edge cs))
    (hP : ∀ e ∈ p, (rootLabel cs e).val ∈ P)
    (hs : p.Pairwise (fun e e' => lexEdgeScore f e' ≤ lexEdgeScore f e)) :
    p.Pairwise (fun e e' => geometricSlope (rootLabel cs e') ≤ geometricSlope (rootLabel cs e)) ∨
    p.Pairwise (fun e e' => geometricSlope (rootLabel cs e) ≤ geometricSlope (rootLabel cs e')) := by
  obtain ⟨c,d,hf⟩ := B.exists_affine f
  have hv (e : AdaptedDyer.Edge cs) (he : e ∈ p) :
      lexEdgeScore f e=toLex (c*geometricSlope (rootLabel cs e)+d,geometricSlope (rootLabel cs e)) := by
    unfold lexEdgeScore lexRootScore
    rw [hf _ (hP e he)]
  by_cases hc : 0 ≤ c
  · left
    apply hs.imp_of_mem
    intro e e' he he' hee'
    rw [hv e he,hv e' he'] at hee'
    exact lex_affine_nonneg hc hee'
  · right
    apply hs.imp_of_mem
    intro e e' he he' hee'
    rw [hv e he,hv e' he'] at hee'
    exact lex_affine_neg (lt_of_not_ge hc) hee'

include B in
/-- A complete plane block, sorted by any functional, has precisely the
same actual path product as its angularly sorted version. -/
theorem dispatch_plane_functional {R : Type*} [Semiring R] (T : R) (b : W)
    (f : Module.Dual ℝ (I → ℝ)) (p q : List (AdaptedDyer.Edge cs))
    (hpnd : p.Nodup) (hqnd : q.Nodup)
    (hpfull : ∀ e, e ∈ p ↔ (rootLabel cs e).val ∈ P ∧ BruhatLE cs (target cs e) b)
    (hqfull : ∀ e, e ∈ q ↔ (rootLabel cs e).val ∈ P ∧ BruhatLE cs (target cs e) b)
    (hp : p.Pairwise (fun e e' => lexEdgeScore f e' ≤ lexEdgeScore f e))
    (hq : q.Pairwise (fun e e' => geometricSlope (rootLabel cs e') ≤ geometricSlope (rootLabel cs e)))
    (x y : W) (hy : BruhatLE cs y b) :
    dispatch (source cs) (target cs) T (fun z => if z=y then 1 else 0) p x =
      dispatch (source cs) (target cs) T (fun z => if z=y then 1 else 0) q x := by
  let L : AdaptedDyer.Edge cs → ℝ := fun e => geometricSlope (rootLabel cs e)
  have hties : ∀ e e', L e=L e' → target cs e ≠ source cs e' := by
    intro e e' he hj
    exact rootLabel_ne_of_join cs e e' hj (geometricSlope_injective he)
  rcases B.lex_block_orientation f p (fun e he => ((hpfull e).mp he).1) hp with hs|hs
  · exact dispatch_entries_eq_of_sorted (source cs) (target cs) T L hties
      p q hpnd hqnd hs hq (fun e => (hpfull e).trans (hqfull e).symm) x y
  · have hentry := dispatch_entries_eq_of_sorted (source cs) (target cs) T
      (fun e => -L e) (fun e e' he => hties e e' (neg_injective he))
      p q.reverse hpnd (List.nodup_reverse.mpr hqnd)
      (hs.imp (fun he => neg_le_neg he))
      (by rw [List.pairwise_reverse]; exact hq.imp (fun he => neg_le_neg he))
      (fun e => (hpfull e).trans ((hqfull e).symm.trans List.mem_reverse.symm)) x y
    exact hentry.trans (B.dispatch_plane_reverse T b q hqnd hqfull hq x y hy).symm

end PlaneBasis
end
end KLInvariance.TitsSpace
end

end OAI
