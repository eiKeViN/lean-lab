import Mathlib
import ForMathlib.Algebra.BigOperators.SingleCoordinate
import ForMathlib.Combinatorics.DirectedPaths.Suffix
import OAI.KL.Localization.Edge

/-! Semantic home: OAI.KL.Comparison.SuffixFreeness. Source spans: SimultaneousInvariance:3, SimultaneousInvariance:1, SimultaneousInvariance:2, SimultaneousInvariance:4, SimultaneousInvariance:6.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.BruhatGraph
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph SchedulePaths
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W) (u b : W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  (hub : BruhatLE cs u b)
  (B : BoundarySheaf (polynomialGrading_negative ℝ σ)
    (graph cs u b) (polynomialLabel cs u b basis) ⟨b,hub,bruhat_refl cs b⟩)
noncomputable section

omit [Fintype σ] in
 theorem no_conditions_free (x : Interval cs u b) :
    Module.Free (Coefficient (σ := σ))
      (B.sheaf.upwardSubmodule x (remainingConditions cs u b [] x)) := by
  have he : B.sheaf.upwardSubmodule x (remainingConditions cs u b [] x) = ⊤ := by
    ext v
    change (∀ e, e ∈ remainingConditions cs u b [] x → _) ↔ True
    simp [remainingConditions]
  rw [he]
  let := B.free x
  exact Module.Free.of_equiv (Submodule.topEquiv :
    (⊤ : Submodule (Coefficient (σ := σ)) (B.sheaf.vertex x)) ≃ₗ[Coefficient] B.sheaf.vertex x).symm

/-- Reverse traversal of the actual schedule, after embedded image equality.
Both kernels used in Schanuel have already been made free at this point. -/
 theorem schedule_kernels_free_of_images_eq (p : List (Edge cs u b))
    (heq : ∀ e q, e::q <:+ p →
      B.sheaf.lowerImage e (remainingConditions cs u b q ((graph cs u b).source e)) =
      (B.sheaf.upperImage e (remainingConditions cs u b q ((graph cs u b).target e))).map
        (edgeFactorMap cs basis u b hub B e)) :
    ∀ q, q <:+ p → ∀ x : Interval cs u b,
      Module.Free (Coefficient (σ := σ))
        (B.sheaf.upwardSubmodule x (remainingConditions cs u b q x)) := by
  induction p with
  | nil =>
    intro q hq x
    have hq' : q=[] := by simpa using hq
    subst q
    exact no_conditions_free cs u b basis hub B x
  | cons e p ih =>
    have hip := ih (fun a q hq => heq a q (hq.trans (List.suffix_cons e p)))
    intro q hq x
    rcases List.suffix_cons_iff.mp hq with h | h
    · subst q
      by_cases hx : source cs u b e = x
      · subst x
        rw [remainingConditions_cons_source]
        let hS : Module.Free (Coefficient (σ := σ))
            (B.sheaf.upwardSubmodule ((graph cs u b).source e)
              (remainingConditions cs u b p (source cs u b e))) :=
          hip p (List.suffix_refl _) (source cs u b e)
        let hT : Module.Free (Coefficient (σ := σ))
            (B.sheaf.upwardSubmodule ((graph cs u b).target e)
              (remainingConditions cs u b p ((graph cs u b).target e))) :=
          hip p (List.suffix_refl _) (target cs u b e)
        exact partial_kernel_free_of_image_eq cs u b basis hub B e _ _
          (heq e p (List.suffix_refl _))
      · rw [remainingConditions_cons_other cs u b e p x hx]
        exact hip p (List.suffix_refl _) x
    · exact hip q h x

 theorem schedule_kernels_free_of_endpoint_eq (p : List (Edge cs u b))
    (hinc : ∀ e q, e::q <:+ p →
      B.sheaf.lowerImage e (remainingConditions cs u b q ((graph cs u b).source e)) ≤
      (B.sheaf.upperImage e (remainingConditions cs u b q ((graph cs u b).target e))).map
        (edgeFactorMap cs basis u b hub B e))
    {t : ℝ} (ht : 0 < t) (ht1 : t < 1)
    (hend : scheduleState cs u b basis hub B t [] =
      dispatch (source cs u b) (target cs u b) (t⁻¹-t)
        (scheduleState cs u b basis hub B t p) p.reverse) :
    ∀ q, q <:+ p → ∀ x : Interval cs u b,
      Module.Free (Coefficient (σ := σ))
        (B.sheaf.upwardSubmodule x (remainingConditions cs u b q x)) := by
  exact schedule_kernels_free_of_images_eq cs u b basis hub B p
    (edgeImages_eq_of_scheduleState_eq cs u b basis hub B p hinc ht ht1 hend)

end
end KLInvariance.BruhatGraph
end


section
namespace KLInvariance.BruhatGraph
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph SchedulePaths
universe u v u' v' us
variable {I : Type u} {M : CoxeterMatrix I} {W : Type v} [Group W]
  {cs : CoxeterSystem M W} {I' : Type u'} {M' : CoxeterMatrix I'}
  {W' : Type v'} [Group W'] {cs' : CoxeterSystem M' W'}
  {u b : W} {u' b' : W'}
  (φ : Interval cs u b ≃o Interval cs' u' b')
noncomputable section

 def upperIntervalIso (x : Interval cs u b) :
    Interval cs x.val b ≃o Interval cs' (φ x).val b' where
  toFun z :=
    let zI : Interval cs u b := ⟨z.val,x.property.1.trans z.property.1,z.property.2⟩
    ⟨(φ zI).val,φ.monotone z.property.1,(φ zI).property.2⟩
  invFun z :=
    let zI : Interval cs' u' b' := ⟨z.val,(φ x).property.1.trans z.property.1,z.property.2⟩
    ⟨(φ.symm zI).val,by
      change x ≤ φ.symm zI
      simpa only [φ.symm_apply_apply] using φ.symm.monotone
        (show φ x ≤ zI from z.property.1),(φ.symm zI).property.2⟩
  left_inv z := by
    apply Subtype.ext
    change (φ.symm (φ ⟨z.val,x.property.1.trans z.property.1,z.property.2⟩)).val=z.val
    exact congrArg (fun a : Interval cs u b => a.val) (φ.symm_apply_apply _)
  right_inv z := by
    apply Subtype.ext
    change (φ (φ.symm ⟨z.val,(φ x).property.1.trans z.property.1,z.property.2⟩)).val=z.val
    exact congrArg (fun a : Interval cs' u' b' => a.val) (φ.apply_symm_apply _)
  map_rel_iff' := by
    intro x y
    exact φ.map_rel_iff

 def upperGraphInclusion (x : Interval cs u b) :
    GraphMap (graph cs x.val b) (graph cs u b) where
  vertex z := ⟨z.val,x.property.1.trans z.property.1,z.property.2⟩
  edge e := ⟨(⟨(source cs x.val b e).val,
      x.property.1.trans (source cs x.val b e).property.1,(source cs x.val b e).property.2⟩,
    ⟨(target cs x.val b e).val,
      x.property.1.trans (target cs x.val b e).property.1,(target cs x.val b e).property.2⟩),e.property⟩
  source _ := rfl
  target _ := rfl

 theorem upperGraphInclusion_outgoing (x : Interval cs u b) (e : Edge cs u b)
    (z : Interval cs x.val b)
    (hz : (upperGraphInclusion x).vertex z=source cs u b e) :
    ∃ a, (upperGraphInclusion x).edge a=e ∧ source cs x.val b a=z := by
  have hzval := congrArg Subtype.val hz
  let y : Interval cs x.val b := ⟨(target cs u b e).val,
    z.property.1.trans (hzval.symm ▸ Relation.ReflTransGen.single e.property),
    (target cs u b e).property.2⟩
  let a : Edge cs x.val b := ⟨(z,y),hzval.symm ▸ e.property⟩
  refine ⟨a,?_,rfl⟩
  exact Subtype.ext (Prod.ext hz rfl)

 theorem upperIntervalIso_val (x : Interval cs u b) (z : Interval cs x.val b) :
    (upperIntervalIso φ x z).val=(φ ((upperGraphInclusion x).vertex z)).val := rfl

variable [Fintype I']

 theorem upper_transportedSlope (x : Interval cs u b) (e : Edge cs x.val b) :
    transportedSlope (upperIntervalIso φ x) e =
      transportedSlope φ ((upperGraphInclusion x).edge e) := rfl

 theorem cutoff_is_suffix (s : ℝ) :
    ∃ q, q <:+ chronologicalSchedule φ ∧
      ∀ e : Edge cs u b, e ∈ q ↔ s < transportedSlope φ e := by
  obtain ⟨q,hq,he⟩ := exists_suffix_score_gt (transportedSlope φ) s
    (chronologicalSchedule φ) (chronologicalSchedule_pairwise φ)
  exact ⟨q,hq,fun e => by simpa only [chronologicalSchedule_full φ e,true_and] using he e⟩

variable [Fintype I] {σ : Type (max us v)} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  (hub : BruhatLE cs u b)

 theorem intervalBoundary_upper_kernel (x : Interval cs u b)
    (z : Interval cs x.val b) (T : Set (Edge cs u b)) :
    (intervalBoundary basis x.property.2).sheaf.upwardSubmodule z
      {e | (upperGraphInclusion x).edge e.val ∈ T} =
    (intervalBoundary basis hub).sheaf.upwardSubmodule ((upperGraphInclusion x).vertex z)
      {e | e.val ∈ T} := by
  exact (intervalBoundary basis hub).sheaf.forget.pullback_kernel
    (upperGraphInclusion x) z T Set.univ
    (fun e he => False.elim (he (Set.mem_univ e)))
    (fun e _ he => upperGraphInclusion_outgoing x e z he)

end
end KLInvariance.BruhatGraph
end


section
namespace KLInvariance.BruhatGraph
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph SchedulePaths
universe u v u' v' us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {σ : Type (max us v)} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  {I' : Type u'} [Fintype I'] {M' : CoxeterMatrix I'}
  {W' : Type v'} [Group W'] {cs' : CoxeterSystem M' W'}
  {u b : W} {u' b' : W'} (hub : BruhatLE cs u b)
  (φ : Interval cs u b ≃o Interval cs' u' b')
noncomputable section

def FreeSuffixes : Prop :=
  ∀ q, q <:+ chronologicalSchedule φ → ∀ x : Interval cs u b,
    Module.Free (Coefficient (σ := σ))
      ((intervalBoundary basis hub).sheaf.upwardSubmodule x
        (remainingConditions cs u b q x))

 theorem target_free_of_upper_suffixes {e : Edge cs u b} {q : List (Edge cs u b)}
    (hq : e::q <:+ chronologicalSchedule φ)
    (hsmall : FreeSuffixes basis (target cs u b e).property.2
      (upperIntervalIso φ (target cs u b e))) :
    Module.Free (Coefficient (σ := σ))
      ((intervalBoundary basis hub).sheaf.upwardSubmodule (target cs u b e)
        (remainingConditions cs u b q (target cs u b e))) := by
  let x := target cs u b e
  let z := intervalBottom cs x.property.2
  obtain ⟨p,hp,he⟩ := cutoff_is_suffix (upperIntervalIso φ x) (transportedSlope φ e)
  have hh := hsmall p hp z
  let T : Set (Edge cs u b) := {f | transportedSlope φ e < transportedSlope φ f}
  have hs : remainingConditions cs x.val b p z =
      {f | (upperGraphInclusion x).edge f.val ∈ T} := by
    ext f
    exact he f.val
  rw [hs,intervalBoundary_upper_kernel basis hub x z T] at hh
  have hb : remainingConditions cs u b q x = {f | f.val ∈ T} := by
    ext f
    exact suffix_target_iff φ hq f.property
  rw [hb]
  exact hh

end
end KLInvariance.BruhatGraph
end


section
namespace KLInvariance.BruhatGraph
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph Polynomial SchedulePaths
universe u u'
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] {cs : CoxeterSystem M W}
  {σ : Type u} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  {I' : Type u'} [Fintype I'] {M' : CoxeterMatrix I'}
  {W' : Type u'} [Group W'] {cs' : CoxeterSystem M' W'}
  {a b : W} {a' b' : W'} (hab : BruhatLE cs a b)
  (φ : Interval cs a b ≃o Interval cs' a' b')
noncomputable section
local instance _root_.OAI.KLInvariance.BruhatGraph.instDecidableEq_oAI_2 (X : Type*) : DecidableEq X := Classical.decEq X

 theorem transported_initial_scaledStalk {t : ℝ} (ht : 0<t) (ht1 : t<1)
    (x : Interval cs a b) :
    scheduleState cs a b basis hab (intervalBoundary basis hab) t (chronologicalSchedule φ) x=
      scaledStalk cs b basis t⁻¹ ((upperInclusion cs a b).vertex x) := by
  rw [scheduleState,schedule_all_conditions φ]
  unfold intervalBoundary
  rw [normalized_fullKernel_restrictBoundary]
  exact normalized_fullKernel_scaledStalk cs b basis _ ht ht1

 theorem actual_comparison_of_upper_freeness
    (hfree : ∀ e q, e::q <:+ chronologicalSchedule φ →
      Module.Free (Coefficient (σ := σ))
        ((intervalBoundary basis hab).sheaf.upwardSubmodule (target cs a b e)
          (remainingConditions cs a b q (target cs a b e))))
    {t : ℝ} (ht : 0<t) (ht1 : t<1) :
    (fun x : Interval cs a b => scaledStalk cs b basis t ((upperInclusion cs a b).vertex x)) ≤
      dispatch (source cs a b) (target cs a b) (t⁻¹-t)
        (fun x => scaledStalk cs b basis t⁻¹ ((upperInclusion cs a b).vertex x))
        (transportedSchedule φ) := by
  have h := schedule_comparison_of_upper_freeness basis hab φ hfree ht ht1
  rwa [funext (schedule_final_scaledStalk cs b basis a hab ht ht1),
    funext (transported_initial_scaledStalk basis hab φ ht ht1)] at h

 theorem actual_endpoint_of_rTilde_eq
    (hr : ∀ x z : Interval cs a b, Hecke.rTilde cs x.val z.val=
      Hecke.rTilde cs' (φ x).val (φ z).val)
    {t : ℝ} (ht : 0<t) (ht1 : t<1) :
    scheduleState cs a b basis hab (intervalBoundary basis hab) t []=
      dispatch (source cs a b) (target cs a b) (t⁻¹-t)
        (scheduleState cs a b basis hab (intervalBoundary basis hab) t (chronologicalSchedule φ))
        (chronologicalSchedule φ).reverse := by
  rw [funext (schedule_final_scaledStalk cs b basis a hab ht ht1),
    funext (transported_initial_scaledStalk basis hab φ ht ht1),
    chronologicalSchedule,List.reverse_reverse]
  funext x
  rw [transported_dispatch_matrix φ _ (Int.castRingHom ℝ),
    scaledStalk_reciprocity_upper cs b basis t ht.ne' a x]
  congr 1
  funext z
  rw [hr x z]

 theorem actual_freeSuffixes_of_rTilde_eq
    (hr : ∀ x z : Interval cs a b, Hecke.rTilde cs x.val z.val=
      Hecke.rTilde cs' (φ x).val (φ z).val)
    (hfree : ∀ e q, e::q <:+ chronologicalSchedule φ →
      Module.Free (Coefficient (σ := σ))
        ((intervalBoundary basis hab).sheaf.upwardSubmodule (target cs a b e)
          (remainingConditions cs a b q (target cs a b e)))) :
    FreeSuffixes basis hab φ := by
  apply schedule_kernels_free_of_endpoint_eq cs a b basis hab (intervalBoundary basis hab)
    (chronologicalSchedule φ)
    (fun e q hq => by
      let := hfree e q hq
      exact schedule_edge_image_le basis hab φ hq)
    (t := 1/2) (by norm_num) (by norm_num)
  exact actual_endpoint_of_rTilde_eq basis hab φ hr (by norm_num) (by norm_num)

end
end KLInvariance.BruhatGraph
end


section
namespace KLInvariance.BruhatGraph
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph Polynomial SchedulePaths
universe u u'
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] {cs : CoxeterSystem M W}
  {σ : Type u} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  {I' : Type u'} [Fintype I'] {M' : CoxeterMatrix I'}
  {W' : Type u'} [Group W'] {cs' : CoxeterSystem M' W'}
  {a b : W} {a' b' : W'} (hab : BruhatLE cs a b) (hab' : BruhatLE cs' a' b')
  (φ : Interval cs a b ≃o Interval cs' a' b')
noncomputable section
local instance _root_.OAI.KLInvariance.BruhatGraph.instDecidableEq_oAI_3 (X : Type*) : DecidableEq X := Classical.decEq X

 theorem scaledStalk_upper_top {C : Type*} [Field C] (t : C) :
    scaledStalk cs b basis t ((upperInclusion cs a b).vertex (intervalTop cs hab))=1 := by
  change t^((cs.length b : ℤ)-cs.length b)*
    eval₂ (Int.castRingHom C) (t^2)
      (stalkCharacter cs 1 b basis (one_bruhat cs b)
        ⟨b,one_bruhat cs b,bruhat_refl cs b⟩)=1
  rw [stalkCharacter_top]
  simp

include hab hab'

 theorem rTilde_eval_le_of_comparison
    (hrow : ∀ z : Interval cs a b, z.val≠b →
      Hecke.rTilde cs a z.val=Hecke.rTilde cs' a' (φ z).val)
    {t : ℝ} (ht : 0<t) (_ht1 : t<1)
    (hcomp : (fun x : Interval cs a b => scaledStalk cs b basis t ((upperInclusion cs a b).vertex x)) ≤
      dispatch (source cs a b) (target cs a b) (t⁻¹-t)
        (fun x => scaledStalk cs b basis t⁻¹ ((upperInclusion cs a b).vertex x))
        (transportedSchedule φ)) :
    eval₂ (Int.castRingHom ℝ) (t⁻¹-t) (Hecke.rTilde cs a b) ≤
      eval₂ (Int.castRingHom ℝ) (t⁻¹-t) (Hecke.rTilde cs' a' b') := by
  let := interval_finite cs a b
  let := Fintype.ofFinite (Interval cs a b)
  have hc := hcomp (intervalBottom cs hab)
  change scaledStalk cs b basis t ((upperInclusion cs a b).vertex (intervalBottom cs hab)) ≤ _ at hc
  rw [transported_dispatch_matrix φ _ (Int.castRingHom ℝ),
    scaledStalk_reciprocity_upper cs b basis t ht.ne' a,
    intervalIso_bottom cs cs' hab hab' φ,finsum_eq_sum_of_fintype,
    finsum_eq_sum_of_fintype] at hc
  have hd := Comparison.matrix_difference_single
    (fun z : Interval cs a b => scaledStalk cs b basis t⁻¹ ((upperInclusion cs a b).vertex z))
    (fun z => eval₂ (Int.castRingHom ℝ) (t⁻¹-t) (Hecke.rTilde cs a z.val))
    (fun z => eval₂ (Int.castRingHom ℝ) (t⁻¹-t) (Hecke.rTilde cs' a' (φ z).val))
    (intervalTop cs hab) (scaledStalk_upper_top basis hab t⁻¹)
    (fun z hz => congrArg _ (hrow z (fun h => hz (Subtype.ext h))))
  rw [intervalIso_top cs cs' hab hab' φ] at hd
  have hh : (∑ z : Interval cs a b, scaledStalk cs b basis t⁻¹ ((upperInclusion cs a b).vertex z)*
      eval₂ (Int.castRingHom ℝ) (t⁻¹-t) (Hecke.rTilde cs a z.val))-
      (∑ z : Interval cs a b, scaledStalk cs b basis t⁻¹ ((upperInclusion cs a b).vertex z)*
      eval₂ (Int.castRingHom ℝ) (t⁻¹-t) (Hecke.rTilde cs' a' (φ z).val)) ≤ 0 := by
    apply sub_nonpos.mpr
    simpa only [mul_comm,intervalBottom] using hc
  rw [hd] at hh
  exact sub_nonpos.mp hh

 theorem rTilde_eval_le_of_upper_freeness
    (hrow : ∀ z : Interval cs a b, z.val≠b →
      Hecke.rTilde cs a z.val=Hecke.rTilde cs' a' (φ z).val)
    (hfree : ∀ e q, e::q <:+ chronologicalSchedule φ →
      Module.Free (Coefficient (σ := σ))
        ((intervalBoundary basis hab).sheaf.upwardSubmodule (target cs a b e)
          (remainingConditions cs a b q (target cs a b e))))
    {t : ℝ} (ht : 0<t) (ht1 : t<1) :
    eval₂ (Int.castRingHom ℝ) (t⁻¹-t) (Hecke.rTilde cs a b) ≤
      eval₂ (Int.castRingHom ℝ) (t⁻¹-t) (Hecke.rTilde cs' a' b') :=
  rTilde_eval_le_of_comparison basis hab hab' φ hrow ht ht1
    (actual_comparison_of_upper_freeness basis hab φ hfree ht ht1)

end
end KLInvariance.BruhatGraph
end

end OAI
