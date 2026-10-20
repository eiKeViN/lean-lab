import Mathlib
import OAI.Order.Interval.Diamonds
import OAI.GroupTheory.Coxeter.Roots.ReflectionLabels

/-! Semantic home: OAI.GroupTheory.Coxeter.Bruhat.DiamondClosure. Source spans: ReflectionSchedules:21.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

namespace KLInvariance
universe u
 theorem bruhatStep_of_interval_covBy
    {I W : Type*} {M : CoxeterMatrix I} [Group W] (cs : CoxeterSystem M W)
    {u b : W} {x y : Interval cs u b} (h : x ⋖ y) : BruhatStep cs x.val y.val := by
  rcases Relation.ReflTransGen.cases_head h.le with heq | ⟨z,hxz,hzy⟩
  · exact (h.ne (Subtype.ext heq)).elim
  · have hle : BruhatLE cs x.val z := Relation.ReflTransGen.single hxz
    let v : Interval cs u b := ⟨z,bruhat_trans cs x.property.1 hle,
      bruhat_trans cs hzy y.property.2⟩
    have hv : v = x ∨ v = y := h.eq_or_eq hle hzy
    rcases hv with hv | hv
    · have heq : z = x.val := congrArg Subtype.val hv
      exact (lt_irrefl _ (heq ▸ hxz.1)).elim
    · have heq : z = y.val := congrArg Subtype.val hv
      exact heq ▸ hxz


 theorem diamondEdges_bruhatStep
    {I W : Type*} [Fintype I] {M : CoxeterMatrix I} [Group W]
    (cs : CoxeterSystem M W) {u b : W} {x y : Interval cs u b}
    (h : DiamondEdges x y) : BruhatStep cs x.val y.val := by
  induction h with
  | cover h => exact bruhatStep_of_interval_covBy cs h
  | diamond _ _ _ _ _ _ _ _ hab hcd hxa hxb hac had hbc hbd hcz hdz =>
    exact TitsSpace.bruhatStep_diamond_closure hxa hxb hac had hbc hbd hcz hdz
      (fun he => hab (Subtype.ext he)) (fun he => hcd (Subtype.ext he))

end KLInvariance

end OAI
