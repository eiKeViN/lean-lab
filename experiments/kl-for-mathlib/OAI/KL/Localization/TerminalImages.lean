module
public import Mathlib
public import ForMathlib.Combinatorics.MomentGraph.Sheaf.ScaledImages
public import OAI.KL.Localization.Plane

public section

/-! Semantic home: OAI.KL.Localization.TerminalImages. Source spans: TerminalKernels:4, TerminalKernels:3, TerminalKernels:5, TerminalKernels:8.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.TitsSpace.PlaneBasis
open Module BruhatGraph MomentGraph MomentGraph.Sheaf
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)
  {σ : Type (max us v)} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  (a₀ b : W) (hmin : ∀ z ∈ planeSubgroup M cs P, cs.length a₀ ≤ cs.length (z*a₀))
noncomputable section

 theorem localized_boundary_decomposition :
    ∃ C : Sheaf.{max us v,v,v,max us v} (R := PlaneRing basis P) (B.cosetGraph a₀ b),
      ModelSum (B.cosetModels basis a₀ b hmin).sheaf Set.univ C ∧
      Nonempty (Iso (B.localizedCoset basis a₀ b hmin
        (boundarySheaf cs 1 b basis (one_bruhat cs b)).sheaf.forget) C) := by
  let D := boundarySheaf cs 1 b basis (one_bruhat cs b)
  apply exists_modelSumIso (B.cosetModels basis a₀ b hmin)
    (B.localizedCoset basis a₀ b hmin D.sheaf.forget)
  · intro x
    let : Module.Free (MvPolynomial σ ℝ)
        (D.sheaf.forget.vertex ((B.cosetGraphMap a₀ b hmin).vertex x)) :=
      D.free (B.cosetAmbient a₀ b x)
    exact D.sheaf.forget.baseChange_vertex_free (PlaneRing basis P) _
  · intro x
    let : Module.Finite (MvPolynomial σ ℝ)
        (D.sheaf.forget.vertex ((B.cosetGraphMap a₀ b hmin).vertex x)) :=
      (D.sheaf.vertex (B.cosetAmbient a₀ b x)).finite
    exact D.sheaf.forget.baseChange_vertex_finite (PlaneRing basis P) _
  · exact B.localizedCoset_quotient basis a₀ b hmin D.sheaf.forget D.quotient
  · exact B.localizedCoset_flabby basis a₀ b hmin D.sheaf.forget D.quotient D.flabby.flabby
  · exact B.localizedCoset_generated basis a₀ b hmin D.sheaf.forget D.generated

end
end KLInvariance.TitsSpace.PlaneBasis
end


section
namespace KLInvariance.TitsSpace.PlaneBasis
open Module BruhatGraph MomentGraph MomentGraph.Sheaf
universe u v us u' v'
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)
  {σ : Type us} (basis : Basis σ ℝ (Extended M))
  {I' : Type u'} [Fintype I'] {M' : CoxeterMatrix I'}
  {W' : Type v'} [Group W'] {cs' : CoxeterSystem M' W'}
  {a₀ u b : W} {u' b' : W'}
  (hmin : ∀ z ∈ planeSubgroup M cs P, cs.length a₀ ≤ cs.length (z*a₀))
  (φ : Interval cs u b ≃o Interval cs' u' b')
noncomputable section

 theorem scheduledLower_root_ne (e : B.CosetEdge a₀ b)
    (hx : BruhatLE cs u ((e.val.1.val:W)*a₀))
    (f : Outgoing (G := B.cosetGraph a₀ b) e.val.1)
    (hf : f ∈ B.scheduledLower hmin φ e hx) :
    B.edgeRoot f.val.property ≠ B.edgeRoot e.property := by
  intro he
  have hroot : BruhatGraph.root cs 1 b (B.cosetEdgeAmbient a₀ b hmin f.val) =
      BruhatGraph.root cs 1 b (B.cosetEdgeAmbient a₀ b hmin e) := by
    rwa [B.cosetRoot_eq a₀ b hmin f.val,B.cosetRoot_eq a₀ b hmin e]
  have hh : f.val=e := B.cosetEdgeAmbient_injective a₀ b hmin
    (eq_of_label_source_eq cs 1 b (root_injective_on_labels cs 1 b hroot)
      (congrArg (B.cosetAmbient a₀ b) f.property))
  have hff : f=(⟨e,rfl⟩ : Outgoing (G := B.cosetGraph a₀ b) e.val.1) := Subtype.ext hh
  exact B.scheduledLower_self hmin φ e hx (hff ▸ hf)

 theorem outgoingUpper_root_ne (e : B.CosetEdge a₀ b)
    (f : Outgoing (G := B.cosetGraph a₀ b) e.val.2) :
    B.edgeRoot f.val.property ≠ B.edgeRoot e.property := by
  rcases f with ⟨⟨⟨s,t⟩,hst⟩,hs⟩
  change s=e.val.2 at hs
  subst s
  exact (B.edgeRoot_ne_of_path e.property hst).symm

include B in
/-- Every root in the chosen root plane has a distinct positive-root complement
spanning that plane. The basis roots supply the witness; no schedule, interval
comparison or sheaf data is needed for this geometric choice. -/
theorem exists_root_plane_complement (α : PositiveRoot M cs) (hα : α.val ∈ P) :
    ∃ β : PositiveRoot M cs, α ≠ β ∧ rootPlane α β = P := by
  obtain ⟨β,hαβ,hβ⟩ : ∃ β : PositiveRoot M cs, α ≠ β ∧ β.val ∈ P := by
    by_cases h : α=B.left
    · exact ⟨B.right,h ▸ B.distinct,B.right_mem⟩
    · exact ⟨B.left,h,B.left_mem⟩
  exact ⟨β,hαβ,(rootPlane_eq_of_mem B.left B.right α β B.distinct
    (B.plane_eq.ge hα) (B.plane_eq.ge hβ) hαβ).trans B.plane_eq⟩

 theorem coset_structure_scaledImages [Fintype (B.CosetEdge a₀ b)]
    (e : B.CosetEdge a₀ b) (hx : BruhatLE cs u ((e.val.1.val:W)*a₀))
    (c : B.CosetVertex a₀ b) :
    (structureSheaf (B.cosetGraph a₀ b) (B.cosetLabel basis a₀ b hmin) c).ScaledImages
      e (B.scheduledLower hmin φ e hx) (B.scheduledUpper hmin φ e hx)
      (algebraMap (MvPolynomial σ ℝ) (PlaneRing basis P)
        (edgeFactorLift cs basis ((e.val.1.val:W)*a₀) (B.edgeRoot e.property))) := by
  classical
  by_cases hyc : e.val.2 ≤ c
  · let α := B.edgeRoot e.property
    obtain ⟨β,hαβ,hplane⟩ := B.exists_root_plane_complement α
      (B.edgeRoot_plane e.property)
    apply structure_scaledImages_of_count (B.cosetGraph a₀ b) (B.cosetLabel basis a₀ b hmin) c
      e _ _ _ (B.reducedCosetRoot basis a₀ b hmin e β)
      ((planeWeight ((e.val.1.val:W)*a₀) α P).toNat)
      (B.coset_supported_pairwise basis a₀ b hmin c e.val.1 _)
      (B.coset_supported_pairwise basis a₀ b hmin c e.val.2 _)
    · intro f hf
      exact B.cosetLabel_reduction_associated basis a₀ b hmin e f.val β hplane
        (B.scheduledLower_root_ne hmin φ e hx f (Finset.mem_filter.mp hf).2.1)
    · intro f _
      exact B.cosetLabel_reduction_associated basis a₀ b hmin e f.val β hplane
        (B.outgoingUpper_root_ne e f)
    · exact B.cosetFactor_reduction_associated basis a₀ b hmin e β hαβ hplane
    · exact B.supported_count_difference hmin φ e hx c hyc
  · let := structureSheaf_edge_subsingleton (B.cosetGraph a₀ b)
        (B.cosetLabel basis a₀ b hmin) c e hyc
    intro z
    constructor <;> intro _ <;> exact ⟨0,Submodule.zero_mem _,Subsingleton.elim _ _⟩

end
end KLInvariance.TitsSpace.PlaneBasis
end


section
namespace KLInvariance.TitsSpace.PlaneBasis
open Module BruhatGraph MomentGraph MomentGraph.Sheaf
universe u v us u' v'
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)
  {σ : Type (max us v)} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  {I' : Type u'} [Fintype I'] {M' : CoxeterMatrix I'}
  {W' : Type v'} [Group W'] {cs' : CoxeterSystem M' W'}
  {a₀ u b : W} {u' b' : W'}
  (hmin : ∀ z ∈ planeSubgroup M cs P, cs.length a₀ ≤ cs.length (z*a₀))
  (φ : Interval cs u b ≃o Interval cs' u' b')
noncomputable section

 theorem localized_boundary_scaledImages (e : B.CosetEdge a₀ b)
    (hx : BruhatLE cs u ((e.val.1.val:W)*a₀)) :
    (B.localizedCoset basis a₀ b hmin
      (boundarySheaf cs 1 b basis (one_bruhat cs b)).sheaf.forget).ScaledImages
      e (B.scheduledLower hmin φ e hx) (B.scheduledUpper hmin φ e hx)
      (algebraMap (MvPolynomial σ ℝ) (PlaneRing basis P)
        (edgeFactorLift cs basis ((e.val.1.val:W)*a₀) (B.edgeRoot e.property))) := by
  classical
  let := Fintype.ofFinite (B.CosetVertex a₀ b)
  let : Finite (B.CosetEdge a₀ b) := Finite.of_injective
    (fun e : B.CosetEdge a₀ b => e.val) Subtype.val_injective
  let := Fintype.ofFinite (B.CosetEdge a₀ b)
  obtain ⟨C,hC,⟨j⟩⟩ := B.localized_boundary_decomposition basis a₀ b hmin
  apply j.symm.scaledImages
  apply hC.scaledImages
  intro c _
  exact B.coset_structure_scaledImages basis hmin φ e hx c

end
end KLInvariance.TitsSpace.PlaneBasis
end


section
namespace KLInvariance.TitsSpace.PlaneBasis
open Module BruhatGraph MomentGraph MomentGraph.Sheaf
universe u v us um u' v'
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)
  {σ : Type us} (basis : Basis σ ℝ (Extended M))
  {a₀ b : W}
  (hmin : ∀ z ∈ planeSubgroup M cs P, cs.length a₀ ≤ cs.length (z*a₀))
noncomputable section

 theorem localizedCoset_kernel
    (C : Sheaf.{us,v,v,um} (R := MvPolynomial σ ℝ) (graph cs 1 b))
    (hq : C.UpperQuotient (polynomialLabel cs 1 b basis))
    (x : B.CosetVertex a₀ b) (T : Set (Edge cs 1 b)) :
    (B.localizedCoset basis a₀ b hmin C).upwardKernel x
      {e | B.cosetEdgeAmbient a₀ b hmin e.val ∈ T} =
    (C.baseChange (PlaneRing basis P)).upwardKernel (B.cosetAmbient a₀ b x) {e | e.val ∈ T} := by
  apply (C.baseChange (PlaneRing basis P)).pullback_kernel (B.cosetGraphMap a₀ b hmin) x T
    {e | label cs 1 b e ∈ planeSubgroup M cs P}
  · intro e he
    exact (C.baseChange (PlaneRing basis P)).edge_subsingleton_of_unit _
      (C.baseChange_upperQuotient (PlaneRing basis P) _ hq) e
      ((polynomialLabel_unit_iff (P := P) basis b e).mpr he)
  · intro e he hx
    exact B.coset_lift_live a₀ b hmin e he x hx

end

variable {σ : Type (max us v)} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  {I' : Type u'} [Fintype I'] {M' : CoxeterMatrix I'}
  {W' : Type v'} [Group W'] {cs' : CoxeterSystem M' W'}
  {u : W} {u' b' : W'}
  (φ : Interval cs u b ≃o Interval cs' u' b')
noncomputable section

 theorem ambient_boundary_scaledImages (e : B.CosetEdge a₀ b)
    (hx : BruhatLE cs u ((e.val.1.val:W)*a₀)) :
    let D := (boundarySheaf cs 1 b basis (one_bruhat cs b)).sheaf.forget
    let T := ambientLater φ (B.mappedCosetRoot hmin φ e hx)
    (D.baseChange (PlaneRing basis P)).ScaledImages (B.cosetEdgeAmbient a₀ b hmin e)
      {f | f.val ∈ T} {f | f.val ∈ T}
      (algebraMap (MvPolynomial σ ℝ) (PlaneRing basis P)
        (edgeFactorLift cs basis ((e.val.1.val:W)*a₀) (B.edgeRoot e.property))) := by
  let D := boundarySheaf cs 1 b basis (one_bruhat cs b)
  have h := B.localized_boundary_scaledImages basis hmin φ e hx
  dsimp only
  intro z
  have hh := h z
  change (∃ v ∈ (B.localizedCoset basis a₀ b hmin D.sheaf.forget).upwardKernel e.val.1
      (B.scheduledOutgoing hmin φ _ e.val.1 hx), _) ↔
    ∃ w ∈ (B.localizedCoset basis a₀ b hmin D.sheaf.forget).upwardKernel e.val.2
      (B.scheduledOutgoing hmin φ _ e.val.2 (B.cosetEdge_target_upper hmin e hx)), _ at hh
  rw [B.scheduledOutgoing_eq hmin φ,B.scheduledOutgoing_eq hmin φ,
    B.localizedCoset_kernel basis hmin D.sheaf.forget D.quotient,
    B.localizedCoset_kernel basis hmin D.sheaf.forget D.quotient] at hh
  exact hh

end
end KLInvariance.TitsSpace.PlaneBasis
end

end OAI
