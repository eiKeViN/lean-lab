import Mathlib
import OAI.GroupTheory.Coxeter.Roots.Order

/-! Semantic home: OAI.GroupTheory.Coxeter.Roots.ReflectionLabels. Source spans: ReflectionSchedules:16, ReflectionSchedules:17.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.TitsSpace
open Module
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
noncomputable section

/-- A product of three genuine Coxeter reflections in one root plane is a
Coxeter reflection, using the proved reflection faithfulness of the actual
Tits extension. This is the sufficiency direction of graph diamond closure. -/
theorem Represents.triple_isReflection {t s r : W} {a b c : I → ℝ}
    (ha : Represents M cs t a) (hb : Represents M cs s b) (hc : Represents M cs r c)
    (hplane : c ∈ Submodule.span ℝ {a,b}) : cs.IsReflection (t*s*r) := by
  have hplane' : embed M c ∈ Submodule.span ℝ {embed M a,embed M b} := by
    obtain ⟨x,y,hxy⟩ := Submodule.mem_span_pair.mp hplane
    apply Submodule.mem_span_pair.mpr
    refine ⟨x,y,?_⟩
    ext
    · exact congrFun hxy _
    · simp [embed]
  obtain ⟨d,hd,he⟩ := ReflectionPlane.reflection_triple_in_plane (extendedForm M)
    (extendedForm_spec M).1 (embed M a) (embed M b) (embed M c)
    (by rw [(extendedForm_spec M).2.2]; exact ha.isRoot.norm)
    (by rw [(extendedForm_spec M).2.2]; exact hb.isRoot.norm)
    (by rw [(extendedForm_spec M).2.2]; exact hc.isRoot.norm) hplane'
  apply isReflection_of_moving_rank_one M cs
  have heq : extendedAction M cs (t*s*r) = Module.reflection hd := by
    rw [map_mul,map_mul,ha.extendedAction_eq,hb.extendedAction_eq,hc.extendedAction_eq]
    exact he
  rw [heq]
  exact Realization.finrank_reflection_sub_id _ _ hd

end
end KLInvariance.TitsSpace
end


section
namespace KLInvariance
universe u v
variable {I : Type u} [klPreservedInstance7 : Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
noncomputable section

include klPreservedInstance7 in
 theorem BruhatStep.label_reflection {x y : W} (h : BruhatStep cs x y) :
    cs.IsReflection (y*x⁻¹) := by
  have _ := klPreservedInstance7
  obtain ⟨_,t,ht,rfl⟩ := h
  simpa [mul_assoc] using ht

 theorem BruhatStep.composable_labels_ne {x y z : W}
    (h : BruhatStep cs x y) (h' : BruhatStep cs y z) :
    y*x⁻¹ ≠ z*y⁻¹ := by
  intro he
  have hh : z*x⁻¹=1 := by
    calc
      z*x⁻¹ = (z*y⁻¹)*(y*x⁻¹) := by group
      _ = (y*x⁻¹)*(y*x⁻¹) := by rw [← he]
      _ = 1 := h.label_reflection.mul_self
  have hzx : z = x := by simpa using congrArg (fun w => w*x) hh
  have hlen := lt_trans h.1 h'.1
  simp [hzx] at hlen

namespace TitsSpace
open Module

 def graphRoot {x y : W} (h : BruhatStep cs x y) : PositiveRoot M cs :=
   positiveRoot M cs ⟨y*x⁻¹,h.label_reflection⟩

 theorem graphRoot_represents {x y : W} (h : BruhatStep cs x y) :
    Represents M cs (y*x⁻¹) (graphRoot h).val :=
  positiveRoot_represents M cs ⟨y*x⁻¹,h.label_reflection⟩

 theorem graphRoot_ne_of_same_source {x a b : W}
    (ha : BruhatStep cs x a) (hb : BruhatStep cs x b) (hab : a ≠ b) :
    graphRoot ha ≠ graphRoot hb := by
  intro he
  have hl := (graphRoot_represents ha).reflection_unique
    (he.symm ▸ graphRoot_represents hb)
  exact hab ((mul_right_cancel_iff).mp hl)

 theorem graphRoot_ne_of_path {x a z : W}
    (ha : BruhatStep cs x a) (hb : BruhatStep cs a z) :
    graphRoot ha ≠ graphRoot hb := by
  intro he
  exact ha.composable_labels_ne hb ((graphRoot_represents ha).reflection_unique
    (he.symm ▸ graphRoot_represents hb))

 theorem graphRoot_square_plane {x a b z : W}
    (hxa : BruhatStep cs x a) (hxb : BruhatStep cs x b)
    (haz : BruhatStep cs a z) (hbz : BruhatStep cs b z) (hab : a ≠ b) :
    rootPlane (graphRoot hxa) (graphRoot haz) =
      rootPlane (graphRoot hxa) (graphRoot hxb) := by
  have hp := (graphRoot_represents haz).plane_eq_of_product_eq
    (graphRoot_represents hxa) (graphRoot_represents hbz) (graphRoot_represents hxb)
    (Ne.symm (hxa.composable_labels_ne haz)) (Ne.symm (hxb.composable_labels_ne hbz))
    (by group : (z*a⁻¹)*(a*x⁻¹)=(z*b⁻¹)*(b*x⁻¹))
  have hp' := congrArg (Submodule.map
    (LinearMap.fst ℝ (I → ℝ) (Module.Dual ℝ (LinearMap.ker (form M))))) hp
  have hp'' : rootPlane (graphRoot haz) (graphRoot hxa) =
      rootPlane (graphRoot hbz) (graphRoot hxb) := by
    simpa only [rootPlane,Submodule.map_span,Set.image_insert_eq,
      Set.image_singleton,LinearMap.fst_apply,embed] using hp'
  have hm : (graphRoot hxb).val ∈ rootPlane (graphRoot hxa) (graphRoot haz) := by
    rw [rootPlane,Set.pair_comm]
    change (graphRoot hxb).val ∈ rootPlane (graphRoot haz) (graphRoot hxa)
    rw [hp'']
    exact Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  exact ((rootPlane_eq_iff (graphRoot hxa) (graphRoot haz) (graphRoot hxb)
    (graphRoot_ne_of_path hxa haz)).mpr
    ⟨Ne.symm (graphRoot_ne_of_same_source hxa hxb hab),hm⟩).symm

/-- Soundness of the eight-edge diamond closure rule for the genuine Bruhat
reflection graph. Vertex ranks need not be consecutive; the proof uses actual
root planes and reflection faithfulness, not a labeled graph isomorphism. -/
 theorem bruhatStep_diamond_closure {x a b c d z : W}
    (hxa : BruhatStep cs x a) (hxb : BruhatStep cs x b)
    (hac : BruhatStep cs a c) (had : BruhatStep cs a d)
    (hbc : BruhatStep cs b c) (hbd : BruhatStep cs b d)
    (hcz : BruhatStep cs c z) (hdz : BruhatStep cs d z)
    (hab : a ≠ b) (hcd : c ≠ d) : BruhatStep cs x z := by
  let P := rootPlane (graphRoot hxa) (graphRoot hxb)
  let Q := rootPlane (graphRoot hac) (graphRoot had)
  have hPc := graphRoot_square_plane hxa hxb hac hbc hab
  have hPd := graphRoot_square_plane hxa hxb had hbd hab
  have hacP : (graphRoot hac).val ∈ P := by
    change (graphRoot hac).val ∈ rootPlane (graphRoot hxa) (graphRoot hxb)
    rw [← hPc]
    exact Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have hadP : (graphRoot had).val ∈ P := by
    change (graphRoot had).val ∈ rootPlane (graphRoot hxa) (graphRoot hxb)
    rw [← hPd]
    exact Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have hQP : Q=P := by
    apply Submodule.eq_of_le_of_finrank_eq
    · apply Submodule.span_le.mpr
      intro v hv
      rcases Set.mem_insert_iff.mp hv with rfl | hv
      · exact hacP
      · have hv' := Set.mem_singleton_iff.mp hv
        rw [hv']
        exact hadP
    · dsimp [Q,P]
      rw [rootPlane_finrank _ _ (graphRoot_ne_of_same_source hac had hcd),
        rootPlane_finrank _ _ (graphRoot_ne_of_same_source hxa hxb hab)]
  have hQc := graphRoot_square_plane hac had hcz hdz hcd
  have hm : (graphRoot hxa).val ∈
      Submodule.span ℝ {(graphRoot hcz).val,(graphRoot hac).val} := by
    rw [Set.pair_comm]
    change (graphRoot hxa).val ∈ rootPlane (graphRoot hac) (graphRoot hcz)
    rw [hQc]
    change (graphRoot hxa).val ∈ Q
    rw [hQP]
    exact Submodule.subset_span (Set.mem_insert _ _)
  have href := (graphRoot_represents hcz).triple_isReflection
    (graphRoot_represents hac) (graphRoot_represents hxa) hm
  have heq : (z*c⁻¹)*(c*a⁻¹)*(a*x⁻¹)=z*x⁻¹ := by group
  rw [heq] at href
  exact ⟨lt_trans hxa.1 (lt_trans hac.1 hcz.1), z*x⁻¹,href,by group⟩

end TitsSpace
end
end KLInvariance
end

end OAI
