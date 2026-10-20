import Mathlib
import OAI.Algebra.Module.Quotient.ScalarImage
import OAI.RepresentationTheory.KazhdanLusztig.Comparison.Propagation
import OAI.RepresentationTheory.KazhdanLusztig.Localization.Terminal

/-! Semantic home: OAI.RepresentationTheory.KazhdanLusztig.Localization.Edge. Source spans: TerminalKernels:10, TerminalKernels:12, TerminalKernels:13, TerminalKernels:15, TerminalKernels:19, TerminalKernels:9, TerminalKernels:20, TerminalKernels:21, TerminalKernels:22, TerminalKernels:23.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.BruhatGraph
open Module TitsSpace EdgeAlgebra
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
  {σ : Type us} (basis : Basis σ ℝ (Extended M))
noncomputable section

 abbrev EdgeRing (a : PositiveRoot M cs) :=
   MvPolynomial σ ℝ ⧸ Ideal.span {polynomialRoot cs basis a}

 def edgeRingEquiv (a : PositiveRoot M cs) : EdgeRing cs basis a ≃ₐ[ℝ] EdgeCoefficient a :=
   (Ideal.quotientEquivAlg (rootIdeal (k := ℝ) (embed M a.val))
     (Ideal.span {polynomialRoot cs basis a}) (SymmetricAlgebra.equivMvPolynomial basis)
     (by simp only [rootIdeal,Ideal.map_span,Set.image_singleton,polynomialRoot]; rfl)).symm

 @[simp] theorem edgeRingEquiv_root (a β : PositiveRoot M cs) :
    edgeRingEquiv cs basis a (Ideal.Quotient.mk _ (polynomialRoot cs basis β)) =
      Ideal.Quotient.mk _ (SymmetricAlgebra.ι ℝ (Extended M) (embed M β.val)) := by
  apply (edgeRingEquiv cs basis a).symm.injective
  simp only [AlgEquiv.symm_apply_apply]
  rfl

 instance edgeRing_isDomain (a : PositiveRoot M cs) : IsDomain (EdgeRing cs basis a) := by
   let : (Ideal.span {polynomialRoot cs basis a}).IsPrime :=
     Ideal.isPrime_span_singleton_of_prime (polynomialRoot_prime cs basis a)
   infer_instance

 instance edgeRing_ufm (a : PositiveRoot M cs) : UniqueFactorizationMonoid (EdgeRing cs basis a) :=
   ((edgeRingEquiv cs basis a).trans (edgePolynomial a)).toMulEquiv.symm.uniqueFactorizationMonoid inferInstance

 theorem reducedPolynomialRoot_prime (a β : PositiveRoot M cs) (hne : a≠β) :
    Prime (Ideal.Quotient.mk (Ideal.span {polynomialRoot cs basis a})
      (polynomialRoot cs basis β)) := by
  apply (MulEquiv.prime_iff (edgeRingEquiv cs basis a)).mp
  rw [edgeRingEquiv_root]
  exact reducedRoot_prime _ _ (embed_not_rootLine a β hne.symm)

 theorem planePrime_span (a β : PositiveRoot M cs) :
    planePrime basis (rootPlane a β) =
      Ideal.span {polynomialRoot cs basis a,polynomialRoot cs basis β} := by
  simp only [planePrime,rootPlane,Submodule.map_span,Set.image_insert_eq,
    Set.image_singleton,SymmetricPlaneIdeal.ideal_span_eq,Ideal.map_span,
    polynomialRoot,embedLinear]
  rfl

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
  (B : BoundarySheaf (polynomialGrading_negative ℝ σ)
    (graph cs u b) (polynomialLabel cs u b basis) ⟨b,hub,bruhat_refl cs b⟩)
noncomputable section

omit [Fintype σ] in
 theorem edgeTorsion (e : Edge cs u b) :
    Module.IsTorsionBy (MvPolynomial σ ℝ) (B.sheaf.edge e) (polynomialRoot cs basis (root cs u b e)) :=
   fun v => GradedSheaf.UpperQuotient.annihilates B.sheaf B.quotient e v

 @[instance_reducible] def edgeModule (e : Edge cs u b) :
    Module (EdgeRing cs basis (root cs u b e)) (B.sheaf.edge e) :=
   (edgeTorsion cs u b basis hub B e).module

omit [Fintype σ] in
 theorem edgeModule_tower (e : Edge cs u b) :
    let _ := edgeModule cs u b basis hub B e
    IsScalarTower (MvPolynomial σ ℝ) (EdgeRing cs basis (root cs u b e)) (B.sheaf.edge e) := by
   dsimp only [edgeModule,Module.IsTorsionBy.module]
   exact Module.IsTorsionBySet.isScalarTower _

omit [Fintype σ] in
 theorem edgeModule_free (e : Edge cs u b) :
    let _ := edgeModule cs u b basis hub B e
    Module.Free (EdgeRing cs basis (root cs u b e)) (B.sheaf.edge e) := by
   let _ := edgeModule cs u b basis hub B e
   let _ := edgeModule_tower cs u b basis hub B e
   let _ := B.free (target cs u b e)
   exact ScalarQuotient.free_of_scalar_presentation _
     (Module.Free.chooseBasis (MvPolynomial σ ℝ) (B.sheaf.vertex (target cs u b e)))
     (B.sheaf.upper e).map (B.quotient e).1 (B.quotient e).2

 theorem upperImage_free (e : Edge cs u b)
    (F : Set (Sheaf.Outgoing (G := graph cs u b) (target cs u b e)))
    [Module.Free (MvPolynomial σ ℝ) (B.sheaf.upwardSubmodule (target cs u b e) F)] :
    let _ := edgeModule cs u b basis hub B e
    let _ := edgeModule_tower cs u b basis hub B e
    Module.Free (EdgeRing cs basis (root cs u b e))
      (ScalarQuotient.submodule (polynomialRoot cs basis (root cs u b e))
        ((B.sheaf.upwardSubmodule (target cs u b e) F).map (B.sheaf.upper e).map)) := by
   let _ := edgeModule cs u b basis hub B e
   let _ := edgeModule_tower cs u b basis hub B e
   let _ : Module.Finite (MvPolynomial σ ℝ) (B.sheaf.vertex (target cs u b e)) :=
     (B.sheaf.vertex (target cs u b e)).finite
   let hfinite : Module.Finite (MvPolynomial σ ℝ) (B.sheaf.upwardSubmodule (target cs u b e) F) :=
     Module.Finite.of_injective (B.sheaf.upwardSubmodule (target cs u b e) F).subtype Subtype.val_injective
   dsimp only
   let hfree := (inferInstance : Module.Free (MvPolynomial σ ℝ) (B.sheaf.upwardSubmodule (target cs u b e) F))
   exact @ScalarQuotient.saturated_image_free (MvPolynomial σ ℝ) _
     (B.sheaf.vertex (target cs u b e)) _ _ (B.sheaf.edge e) _ _
     (polynomialRoot cs basis (root cs u b e)) _ _
     (B.sheaf.upper e).map (B.quotient e).2 (B.sheaf.upwardSubmodule (target cs u b e) F)
     hfree hfinite (by

     exact B.sheaf.upwardSubmodule_saturated (target cs u b e) F _
            (fun f _ => incoming_label_regular_outgoing cs u b basis hub B e f.val f.property))

end
end KLInvariance.BruhatGraph
end


section
namespace KLInvariance.BruhatGraph
open Module TitsSpace EdgeAlgebra
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
  {σ : Type us} (basis : Basis σ ℝ (Extended M))
noncomputable section

 theorem reducedRoot_dvd_iff_mem_plane (a β : PositiveRoot M cs) (z : MvPolynomial σ ℝ) :
    Ideal.Quotient.mk (Ideal.span {polynomialRoot cs basis a}) (polynomialRoot cs basis β) ∣
      Ideal.Quotient.mk (Ideal.span {polynomialRoot cs basis a}) z ↔
    z ∈ planePrime basis (rootPlane a β) := by
  rw [← Ideal.mem_span_singleton]
  change z ∈ Ideal.comap (Ideal.Quotient.mk (Ideal.span {polynomialRoot cs basis a}))
    (Ideal.span {Ideal.Quotient.mk (Ideal.span {polynomialRoot cs basis a})
      (polynomialRoot cs basis β)}) ↔ _
  have hi : Ideal.map (Ideal.Quotient.mk (Ideal.span {polynomialRoot cs basis a}))
      (Ideal.span {polynomialRoot cs basis β}) =
      Ideal.span {Ideal.Quotient.mk (Ideal.span {polynomialRoot cs basis a})
        (polynomialRoot cs basis β)} := by rw [Ideal.map_span,Set.image_singleton]
  rw [← hi,Ideal.comap_map_quotientMk,← Ideal.span_union,Set.singleton_union,planePrime_span]

 theorem reducedFactor_ne_zero (x : W) (a : PositiveRoot M cs) :
    Ideal.Quotient.mk (Ideal.span {polynomialRoot cs basis a})
      (edgeFactorLift cs basis x a) ≠ 0 := by
  simpa only [ne_eq,Ideal.Quotient.eq_zero_iff_mem,Ideal.mem_span_singleton] using
    edgeFactorLift_not_dvd cs basis x a

 theorem prime_dvd_reducedFactor (x : W) (a : PositiveRoot M cs)
    (p : EdgeRing cs basis a) (hp : Prime p)
    (hd : p ∣ Ideal.Quotient.mk _ (edgeFactorLift cs basis x a)) :
    ∃ β : PositiveRoot M cs, a ≠ β ∧
      Associated p (Ideal.Quotient.mk _ (polynomialRoot cs basis β)) := by
  classical
  simp only [edgeFactorLift,map_prod,map_pow] at hd
  obtain ⟨P,_,hP⟩ := (hp.dvd_finsetProd_iff _).mp hd
  exact ⟨planeRoot x a P,(planeRoot_ne x a P).symm,
    hp.irreducible.associated_of_dvd
      (reducedPolynomialRoot_prime cs basis a _ (planeRoot_ne x a P).symm).irreducible
      (hp.dvd_of_dvd_pow hP)⟩

end
end KLInvariance.BruhatGraph
end


section
namespace KLInvariance.BruhatGraph
open Module TitsSpace MomentGraph MomentGraph.Sheaf
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W) (u b : W)
  {σ : Type us} (basis : Basis σ ℝ (Extended M))
noncomputable section

 theorem incoming_root_ne_outgoing (e f : Edge cs u b)
    (h : source cs u b f=target cs u b e) : root cs u b e ≠ root cs u b f := by
  intro hr
  exact source_ne_target_of_label_eq cs u b (root_injective_on_labels cs u b hr.symm) h

 theorem reducedKernelProduct_ne_zero (e : Edge cs u b)
    (F : Set (Outgoing (G := graph cs u b) (target cs u b e))) :
    Ideal.Quotient.mk (Ideal.span {polynomialRoot cs basis (root cs u b e)})
      (outgoingLabelProduct (polynomialLabel cs u b basis) (target cs u b e) F) ≠ 0 := by
  classical
  rw [outgoingLabelProduct,map_prod]
  apply Finset.prod_ne_zero_iff.mpr
  intro f _
  exact (reducedPolynomialRoot_prime cs basis _ _
    (incoming_root_ne_outgoing cs u b e f.val f.property)).ne_zero

 theorem prime_dvd_reducedKernelProduct (e : Edge cs u b)
    (F : Set (Outgoing (G := graph cs u b) (target cs u b e)))
    (p : EdgeRing cs basis (root cs u b e)) (hp : Prime p)
    (hd : p ∣ Ideal.Quotient.mk _
      (outgoingLabelProduct (polynomialLabel cs u b basis) (target cs u b e) F)) :
    ∃ β : PositiveRoot M cs, root cs u b e ≠ β ∧
      Associated p (Ideal.Quotient.mk _ (polynomialRoot cs basis β)) := by
  classical
  rw [outgoingLabelProduct,map_prod] at hd
  obtain ⟨f,_,hf⟩ := (hp.dvd_finsetProd_iff _).mp hd
  exact ⟨root cs u b f.val,incoming_root_ne_outgoing cs u b e f.val f.property,
    hp.irreducible.associated_of_dvd
      (reducedPolynomialRoot_prime cs basis _ _
        (incoming_root_ne_outgoing cs u b e f.val f.property)).irreducible hf⟩

end
end KLInvariance.BruhatGraph
end


section
namespace KLInvariance.BruhatGraph
open Module TitsSpace
universe u v us un
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
  {σ : Type us} (basis : Basis σ ℝ (Extended M))
noncomputable section

 theorem mem_of_plane_denominators (a : PositiveRoot M cs)
    {N : Type un} [AddCommGroup N] [Module (MvPolynomial σ ℝ) N]
    [Module (EdgeRing cs basis a) N] [IsScalarTower (MvPolynomial σ ℝ) (EdgeRing cs basis a) N]
    [Module.IsTorsionFree (EdgeRing cs basis a) N]
    (S : Submodule (MvPolynomial σ ℝ) N)
    [Module.Free (EdgeRing cs basis a) (ScalarQuotient.submodule (polynomialRoot cs basis a) S)]
    (z : N) (c : MvPolynomial σ ℝ)
    (hc : Ideal.Quotient.mk (Ideal.span {polynomialRoot cs basis a}) c ≠ 0)
    (hcz : c • z ∈ S)
    (hprime : ∀ p : EdgeRing cs basis a, Prime p → p ∣ Ideal.Quotient.mk _ c →
      ∃ β : PositiveRoot M cs, a≠β ∧ Associated p (Ideal.Quotient.mk _ (polynomialRoot cs basis β)))
    (hlocal : ∀ β : PositiveRoot M cs, a≠β →
      ∃ s : MvPolynomial σ ℝ, s ∉ planePrime basis (rootPlane a β) ∧ s • z ∈ S) :
    z ∈ S := by
  apply EdgeLattice.mem_of_prime_local_membership
    (ScalarQuotient.submodule (polynomialRoot cs basis a) S) z
  · refine ⟨Ideal.Quotient.mk _ c,hc,?_⟩
    change (algebraMap (MvPolynomial σ ℝ) (EdgeRing cs basis a) c) • z ∈ S
    simpa only [algebraMap_smul] using hcz
  · intro p hp
    by_cases hpc : p ∣ Ideal.Quotient.mk (Ideal.span {polynomialRoot cs basis a}) c
    · obtain ⟨β,hβ,hpβ⟩ := hprime p hp hpc
      obtain ⟨s,hs,hsz⟩ := hlocal β hβ
      refine ⟨Ideal.Quotient.mk _ s,?_,?_⟩
      · rw [hpβ.dvd_iff_dvd_left,reducedRoot_dvd_iff_mem_plane]
        exact hs
      · change (algebraMap (MvPolynomial σ ℝ) (EdgeRing cs basis a) s) • z ∈ S
        simpa only [algebraMap_smul] using hsz
    · refine ⟨Ideal.Quotient.mk _ c,hpc,?_⟩
      change (algebraMap (MvPolynomial σ ℝ) (EdgeRing cs basis a) c) • z ∈ S
      simpa only [algebraMap_smul] using hcz

end
end KLInvariance.BruhatGraph
end


section
namespace KLInvariance.BruhatGraph
open Module TitsSpace MomentGraph MomentGraph.Sheaf
universe u v us u' v'
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {σ : Type (max us v)} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  {I' : Type u'} [Fintype I'] {M' : CoxeterMatrix I'}
  {W' : Type v'} [Group W'] {cs' : CoxeterSystem M' W'}
  {u b : W} {u' b' : W'}
  (φ : Interval cs u b ≃o Interval cs' u' b')
noncomputable section

 theorem boundary_plane_scaledImages (e : Edge cs 1 b)
    (hx : BruhatLE cs u (source cs 1 b e).val)
    (β : PositiveRoot M cs) (hβ : root cs 1 b e ≠ β) :
    let P := rootPlane (root cs 1 b e) β
    let D := (boundarySheaf cs 1 b basis (one_bruhat cs b)).sheaf.forget
    let T := ambientLater φ (mappedEdgeRoot φ e hx)
    (D.baseChange (PlaneRing basis P)).ScaledImages e {f | f.val ∈ T} {f | f.val ∈ T}
      (algebraMap (MvPolynomial σ ℝ) (PlaneRing basis P)
        (edgeFactorLift cs basis (source cs 1 b e).val (root cs 1 b e))) := by
  classical
  let P := rootPlane (root cs 1 b e) β
  let B := (nonempty_planeBasis (root cs 1 b e) β hβ).some
  obtain ⟨a₀,hmin,d,hd⟩ := B.exists_coset_edge e (Submodule.subset_span (by simp))
  have hdx : BruhatLE cs u ((d.val.1.val:W)*a₀) := by
    change BruhatLE cs u (source cs 1 b (B.cosetEdgeAmbient a₀ b hmin d)).val
    rwa [hd]
  have h := B.ambient_boundary_scaledImages hmin basis φ d hdx
  dsimp only at h ⊢
  rw [B.mappedCosetRoot_eq hmin φ d hdx,
    show B.edgeRoot d.property=root cs 1 b (B.cosetEdgeAmbient a₀ b hmin d) from
      (B.cosetRoot_eq a₀ b hmin d).symm] at h
  change ((boundarySheaf cs 1 b basis (one_bruhat cs b)).sheaf.forget.baseChange
    (PlaneRing basis P)).ScaledImages (B.cosetEdgeAmbient a₀ b hmin d)
    {f | f.val ∈ ambientLater φ (mappedEdgeRoot φ (B.cosetEdgeAmbient a₀ b hmin d) hdx)}
    {f | f.val ∈ ambientLater φ (mappedEdgeRoot φ (B.cosetEdgeAmbient a₀ b hmin d) hdx)}
    (algebraMap (MvPolynomial σ ℝ) (PlaneRing basis P)
      (edgeFactorLift cs basis (source cs 1 b (B.cosetEdgeAmbient a₀ b hmin d)).val
        (root cs 1 b (B.cosetEdgeAmbient a₀ b hmin d)))) at h
  have h' := h
  simp only [hd] at h'
  exact Eq.mp (congrArg (fun z : Edge cs 1 b =>
    ((boundarySheaf cs 1 b basis (one_bruhat cs b)).sheaf.forget.baseChange
      (PlaneRing basis P)).ScaledImages z
      {f | f.val ∈ ambientLater φ (mappedEdgeRoot φ e hx)}
      {f | f.val ∈ ambientLater φ (mappedEdgeRoot φ e hx)}
      (algebraMap (MvPolynomial σ ℝ) (PlaneRing basis P)
        (edgeFactorLift cs basis (source cs 1 b e).val (root cs 1 b e)))) hd) h'

end
end KLInvariance.BruhatGraph
end


section
namespace KLInvariance.BruhatGraph
open Module TitsSpace MomentGraph MomentGraph.Sheaf
universe u v us u' v'
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {σ : Type (max us v)} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  {I' : Type u'} [Fintype I'] {M' : CoxeterMatrix I'}
  {W' : Type v'} [Group W'] {cs' : CoxeterSystem M' W'}
  {u b : W} {u' b' : W'}
  (φ : Interval cs u b ≃o Interval cs' u' b')
noncomputable section

 theorem boundary_edge_image_le (e : Edge cs 1 b)
    (hx : BruhatLE cs u (source cs 1 b e).val)
    [Module.Free (MvPolynomial σ ℝ)
      ((boundarySheaf cs 1 b basis (one_bruhat cs b)).sheaf.upwardSubmodule
        (target cs 1 b e) {f | f.val ∈ ambientLater φ (mappedEdgeRoot φ e hx)})] :
    let D := (boundarySheaf cs 1 b basis (one_bruhat cs b)).sheaf.forget
    let T := ambientLater φ (mappedEdgeRoot φ e hx)
    (D.upwardKernel (source cs 1 b e) {f | f.val ∈ T}).map (D.lower e) ≤
      ((D.upwardKernel (target cs 1 b e) {f | f.val ∈ T}).map (D.upper e)).map
        (LinearMap.lsmul (MvPolynomial σ ℝ) (D.edge e)
          (edgeFactorLift cs basis (source cs 1 b e).val (root cs 1 b e))) := by
  classical
  let B := boundarySheaf cs 1 b basis (one_bruhat cs b)
  let D := B.sheaf.forget
  let F : Set (Outgoing (G := graph cs 1 b) (source cs 1 b e)) :=
    {f | f.val ∈ ambientLater φ (mappedEdgeRoot φ e hx)}
  let G : Set (Outgoing (G := graph cs 1 b) (target cs 1 b e)) :=
    {f | f.val ∈ ambientLater φ (mappedEdgeRoot φ e hx)}
  let a := root cs 1 b e
  let f := edgeFactorLift cs basis (source cs 1 b e).val a
  let J := (D.upwardKernel (target cs 1 b e) G).map (D.upper e)
  let S := J.map (LinearMap.lsmul (MvPolynomial σ ℝ) (D.edge e) f)
  let pG := outgoingLabelProduct (polynomialLabel cs 1 b basis) (target cs 1 b e) G
  let _ : Module (EdgeRing cs basis a) (D.edge e) :=
    edgeModule cs 1 b basis (one_bruhat cs b) B e
  let _ : IsScalarTower (MvPolynomial σ ℝ) (EdgeRing cs basis a) (D.edge e) :=
    edgeModule_tower cs 1 b basis (one_bruhat cs b) B e
  let _ : Module.Free (EdgeRing cs basis a) (D.edge e) :=
    edgeModule_free cs 1 b basis (one_bruhat cs b) B e
  let _ : Module.Free (EdgeRing cs basis a)
      (ScalarQuotient.submodule (polynomialRoot cs basis a) J) :=
    upperImage_free cs 1 b basis (one_bruhat cs b) B e G
  let _ : Module.Free (EdgeRing cs basis a) (ScalarQuotient.submodule (polynomialRoot cs basis a) S) :=
    ScalarQuotient.free_scalarImage (polynomialRoot cs basis a) f J
      (edgeFactorLift_regular cs basis 1 b (one_bruhat cs b) B e)
  change (D.upwardKernel (source cs 1 b e) F).map (D.lower e) ≤ S
  intro z hz
  apply mem_of_plane_denominators cs basis a S z (f*pG)
  · rw [map_mul]
    exact mul_ne_zero (reducedFactor_ne_zero cs basis _ a)
      (reducedKernelProduct_ne_zero cs 1 b basis e G)
  · refine ⟨pG • z,?_,?_⟩
    · exact D.outgoingLabelProduct_smul_upperImage (polynomialLabel cs 1 b basis)
        (GradedSheaf.UpperQuotient.annihilates B.sheaf B.quotient) e (B.quotient e).1 G z
    · change f • (pG • z) = (f*pG) • z
      rw [mul_smul]
  · intro p hp hd
    rw [map_mul] at hd
    rcases hp.dvd_mul.mp hd with hf | hG
    · exact prime_dvd_reducedFactor cs basis _ a p hp hf
    · exact prime_dvd_reducedKernelProduct cs 1 b basis e G p hp hG
  · intro β hβ
    obtain ⟨s,hs⟩ := D.scaledImages_denominator (PlaneRing basis (rootPlane a β))
      (planePrime basis (rootPlane a β)).primeCompl e F G f
      (boundary_plane_scaledImages basis φ e hx β hβ) z hz
    exact ⟨s,s.property,hs⟩

end
end KLInvariance.BruhatGraph
end


section
namespace KLInvariance.BruhatGraph
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph SchedulePaths
universe u v us u' v'
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {σ : Type (max us v)} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  {I' : Type u'} [Fintype I'] {M' : CoxeterMatrix I'}
  {W' : Type v'} [Group W'] {cs' : CoxeterSystem M' W'}
  {u b : W} {u' b' : W'} (hub : BruhatLE cs u b)
  (φ : Interval cs u b ≃o Interval cs' u' b')
noncomputable section

 def intervalBoundary := restrictBoundary cs u b basis hub
  (boundarySheaf cs 1 b basis (one_bruhat cs b))

 theorem schedule_edge_image_le {e : Edge cs u b} {q : List (Edge cs u b)}
    (hq : e::q <:+ chronologicalSchedule φ)
    [hF : Module.Free (Coefficient (σ := σ))
      ((intervalBoundary basis hub).sheaf.upwardSubmodule (target cs u b e)
        (remainingConditions cs u b q (target cs u b e)))] :
    (intervalBoundary basis hub).sheaf.lowerImage e
        (remainingConditions cs u b q (source cs u b e)) ≤
      ((intervalBoundary basis hub).sheaf.upperImage e
        (remainingConditions cs u b q (target cs u b e))).map
        (edgeFactorMap cs basis u b hub (intervalBoundary basis hub) e) := by
  let B := boundarySheaf cs 1 b basis (one_bruhat cs b)
  let a := (upperInclusion cs u b).edge e
  let r := AdaptedDyer.rootLabel cs' (transportedEdge φ e)
  have hr : mappedEdgeRoot φ a (source cs u b e).property.1 = r := rfl
  have hk (x : Interval cs u b) :=
    restrictBoundary_kernel cs u b basis hub B x (ambientLater φ r)
  have hs : (intervalBoundary basis hub).sheaf.upwardSubmodule (source cs u b e)
      (remainingConditions cs u b q (source cs u b e)) =
      B.sheaf.upwardSubmodule (source cs 1 b a) {f | f.val ∈ ambientLater φ r} :=
    (congrArg ((intervalBoundary basis hub).sheaf.upwardSubmodule (source cs u b e))
      (remainingConditions_source_ambient φ hq)).trans (hk (source cs u b e))
  have ht : (intervalBoundary basis hub).sheaf.upwardSubmodule (target cs u b e)
      (remainingConditions cs u b q (target cs u b e)) =
      B.sheaf.upwardSubmodule (target cs 1 b a) {f | f.val ∈ ambientLater φ r} :=
    (congrArg ((intervalBoundary basis hub).sheaf.upwardSubmodule (target cs u b e))
      (remainingConditions_target_ambient φ hq)).trans (hk (target cs u b e))
  have hfree : Module.Free (Coefficient (σ := σ))
      (B.sheaf.upwardSubmodule (target cs 1 b a) {f | f.val ∈ ambientLater φ r}) :=
    (congrArg (fun N : Submodule (Coefficient (σ := σ)) (B.sheaf.vertex (target cs 1 b a)) =>
      Module.Free (Coefficient (σ := σ)) N) ht).mp hF
  let hf : Module.Free (Coefficient (σ := σ))
      (B.sheaf.upwardSubmodule (target cs 1 b a)
        {f | f.val ∈ ambientLater φ (mappedEdgeRoot φ a (source cs u b e).property.1)}) := by
    rw [hr]
    exact hfree
  have h := boundary_edge_image_le basis φ a (source cs u b e).property.1
  dsimp only at h
  rw [hr] at h
  have hs' := congrArg (fun N : Submodule (Coefficient (σ := σ)) (B.sheaf.vertex (source cs 1 b a)) =>
    N.map (B.sheaf.lower a).map) hs
  have ht' := congrArg (fun N : Submodule (Coefficient (σ := σ)) (B.sheaf.vertex (target cs 1 b a)) =>
    (N.map (B.sheaf.upper a).map).map
      (edgeFactorMap cs basis u b hub (intervalBoundary basis hub) e)) ht
  exact hs'.le.trans (h.trans ht'.symm.le)

 theorem schedule_comparison_of_upper_freeness
    (hfree : ∀ e q, e::q <:+ chronologicalSchedule φ →
      Module.Free (Coefficient (σ := σ))
        ((intervalBoundary basis hub).sheaf.upwardSubmodule (target cs u b e)
          (remainingConditions cs u b q (target cs u b e))))
    {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    scheduleState cs u b basis hub (intervalBoundary basis hub) t [] ≤
      dispatch (source cs u b) (target cs u b) (t⁻¹-t)
        (scheduleState cs u b basis hub (intervalBoundary basis hub) t (chronologicalSchedule φ))
        (transportedSchedule φ) := by
  have h := scheduleState_le cs u b basis hub (intervalBoundary basis hub) (chronologicalSchedule φ)
    (fun e q hq => by
      let _ := hfree e q hq
      exact schedule_edge_image_le basis hub φ hq) ht ht1
  simpa only [chronologicalSchedule,List.reverse_reverse] using h

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

 theorem schedule_final_of_character
    (hc : StalkCharacterObligation cs 1 b basis (one_bruhat cs b))
    {t : ℝ} (ht : 0 < t) (ht1 : t < 1) (x : Interval cs u b) :
    scheduleState cs u b basis hub (intervalBoundary basis hub) t [] x =
      scaledKL cs t x.val b := by
  have he : remainingConditions cs u b [] x = ∅ := by
    ext e
    simp [remainingConditions]
  rw [scheduleState,he]
  unfold intervalBoundary
  rw [normalized_emptyKernel_restrictBoundary]
  exact normalized_emptyKernel_of_character cs 1 b basis (one_bruhat cs b)
    (boundarySheaf cs 1 b basis (one_bruhat cs b))
    ((upperInclusion cs u b).vertex x) (hc _) ht ht1

omit [Fintype I] [Fintype σ] in
 theorem schedule_all_conditions (x : Interval cs u b) :
    remainingConditions cs u b (chronologicalSchedule φ) x = Set.univ := by
  ext e
  simp only [remainingConditions,Set.mem_ofPred_eq,Set.mem_univ,iff_true]
  exact chronologicalSchedule_full φ e.val

variable [Fintype (Edge cs 1 b)] [Fintype (Interval cs 1 b)] [DecidableEq (Interval cs 1 b)]

 theorem schedule_initial_of_duality_character
    (d : SectionDuality cs 1 b basis (one_bruhat cs b)
      (boundarySheaf cs 1 b basis (one_bruhat cs b)))
    (hd : ∀ i j (m n : (boundarySheaf cs 1 b basis (one_bruhat cs b)).sheaf.sections Set.univ),
      m ∈ ((boundarySheaf cs 1 b basis (one_bruhat cs b)).sheaf.sections Set.univ).piece i →
      n ∈ ((boundarySheaf cs 1 b basis (one_bruhat cs b)).sheaf.sections Set.univ).piece j →
      d.pairing m n ∈ polynomialGrading ℝ σ (i+j-(cs.length b : ℤ)))
    (hc : StalkCharacterObligation cs 1 b basis (one_bruhat cs b))
    {t : ℝ} (ht : 0 < t) (ht1 : t < 1) (x : Interval cs u b) :
    scheduleState cs u b basis hub (intervalBoundary basis hub) t (chronologicalSchedule φ) x =
      scaledKL cs t⁻¹ x.val b := by
  rw [scheduleState,schedule_all_conditions φ]
  unfold intervalBoundary
  rw [normalized_fullKernel_restrictBoundary]
  exact normalized_fullKernel_of_duality_character cs b basis
    (boundarySheaf cs 1 b basis (one_bruhat cs b)) d hd
    ((upperInclusion cs u b).vertex x) (hc _) ht ht1

end
end KLInvariance.BruhatGraph
end


section
namespace KLInvariance.BruhatGraph
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph Polynomial SchedulePaths
universe u
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W) (b : W)
  {σ : Type u} [Fintype σ] (basis : Basis σ ℝ (Extended M))
noncomputable section
local instance actualInterval : Fintype (Interval cs 1 b) := by
  let := interval_finite cs 1 b
  exact Fintype.ofFinite _
local instance actualEdges : Fintype (Edge cs 1 b) := Fintype.ofFinite _
local instance _root_.OAI.KLInvariance.BruhatGraph.instDecidableEq_oAI_1 (a : Type*) : DecidableEq a := Classical.decEq a

 theorem normalized_emptyKernel_scaledStalk (x : Interval cs 1 b)
    {t : ℝ} (ht : 0<t) (ht1 : t<1) :
    normalizedKernel cs 1 b basis (one_bruhat cs b) (ActualBoundary cs b basis) t x ∅=
      scaledStalk cs b basis t x := by
  rw [normalizedKernel,emptyKernel_hilbert cs 1 b basis (one_bruhat cs b)
    (ActualBoundary cs b basis) x (sq_pos_of_pos ht) (by nlinarith)]
  dsimp only [stateScale,scaledStalk]
  have hne : 1-t^2≠0 := ne_of_gt (by nlinarith : 0<1-t^2)
  rw [inv_pow]
  field_simp [hne,inv_pow]

 theorem normalized_fullKernel_scaledStalk (x : Interval cs 1 b)
    {t : ℝ} (ht : 0<t) (ht1 : t<1) :
    normalizedKernel cs 1 b basis (one_bruhat cs b) (ActualBoundary cs b basis) t x Set.univ=
      scaledStalk cs b basis t⁻¹ x := by
  let C := ActualBoundary cs b basis
  let := C.free x
  let c := (exists_nonnegativeBasis (σ := σ) (C.sheaf.vertex x).piece
    (C.sheaf.vertex x).nonneg).some
  have hcp : c.polynomial=stalkCharacter cs 1 b basis (one_bruhat cs b) x := by
    rw [stalkCharacter_eq_character cs 1 b basis (one_bruhat cs b) C x,
      character_eq (C.sheaf.vertex x).piece (C.sheaf.vertex x).nonneg c]
  rw [normalizedKernel,GradedSheaf.kernelHilbert,
    fullKernel_eq cs 1 b basis (one_bruhat cs b) C x,
    costalk_hilbert_of_duality cs 1 b basis (one_bruhat cs b) C (actualSectionDuality cs b basis)
      (cs.length b) (actualSectionDuality_homogeneous cs b basis) x c
      (sq_pos_of_pos ht) (by nlinarith),hcp,incoming_card cs b x]
  dsimp only [stateScale,scaledStalk]
  have hscale : t^((cs.length x.val : ℤ)-cs.length b)*
      (t^2)^((cs.length b : ℤ)-cs.length x.val)=
      (t⁻¹)^((cs.length x.val : ℤ)-cs.length b) := by
    rw [show (t^2)^((cs.length b : ℤ)-cs.length x.val)=
      t^(2*((cs.length b : ℤ)-cs.length x.val)) by rw [zpow_mul]; norm_num,
      ←zpow_add₀ ht.ne',inv_zpow,←zpow_neg]
    congr 1
    omega
  rw [show (t^2)⁻¹=(t⁻¹)^2 by rw [inv_pow]]
  have hne : 1-t^2≠0 := ne_of_gt (by nlinarith : 0<1-t^2)
  calc
    _ = (t^((cs.length x.val : ℤ)-cs.length b)*
      (t^2)^((cs.length b : ℤ)-cs.length x.val))*
      eval₂ (Int.castRingHom ℝ) ((t⁻¹)^2) (stalkCharacter cs 1 b basis (one_bruhat cs b) x) := by
      have hcancel : (1-t^2)^(Fintype.card σ)*((1-t^2)⁻¹)^(Fintype.card σ)=1 := by
        rw [←mul_pow,mul_inv_cancel₀ hne,one_pow]
      calc
        _ = ((1-t^2)^(Fintype.card σ)*((1-t^2)⁻¹)^(Fintype.card σ))*
            ((t^((cs.length x.val : ℤ)-cs.length b)*(t^2)^((cs.length b : ℤ)-cs.length x.val))*
            eval₂ (Int.castRingHom ℝ) ((t⁻¹)^2) (stalkCharacter cs 1 b basis (one_bruhat cs b) x)) := by ring
        _ = _ := by rw [hcancel,one_mul]
    _ = _ := by rw [hscale]

 theorem schedule_final_scaledStalk (a : W) (hab : BruhatLE cs a b)
    {t : ℝ} (ht : 0<t) (ht1 : t<1) (x : Interval cs a b) :
    scheduleState cs a b basis hab (intervalBoundary basis hab) t [] x=
      scaledStalk cs b basis t ((upperInclusion cs a b).vertex x) := by
  have he : remainingConditions cs a b [] x=∅ := by
    ext e
    simp [remainingConditions]
  rw [scheduleState,he]
  unfold intervalBoundary
  rw [normalized_emptyKernel_restrictBoundary]
  exact normalized_emptyKernel_scaledStalk cs b basis _ ht ht1

 theorem schedule_initial_scaledStalk (a : W) (hab : BruhatLE cs a b)
    {t : ℝ} (ht : 0<t) (ht1 : t<1) (x : Interval cs a b) :
    scheduleState cs a b basis hab (intervalBoundary basis hab) t
      (chronologicalSchedule (OrderIso.refl (Interval cs a b))) x=
      scaledStalk cs b basis t⁻¹ ((upperInclusion cs a b).vertex x) := by
  rw [scheduleState,schedule_all_conditions (OrderIso.refl (Interval cs a b))]
  unfold intervalBoundary
  rw [normalized_fullKernel_restrictBoundary]
  exact normalized_fullKernel_scaledStalk cs b basis _ ht ht1

 theorem native_endpoint_eq (a : W) (hab : BruhatLE cs a b)
    {t : ℝ} (ht : 0<t) (ht1 : t<1) :
    scheduleState cs a b basis hab (intervalBoundary basis hab) t []=
      dispatch (source cs a b) (target cs a b) (t⁻¹-t)
        (scheduleState cs a b basis hab (intervalBoundary basis hab) t
           (chronologicalSchedule (OrderIso.refl (Interval cs a b))))
        (chronologicalSchedule (OrderIso.refl (Interval cs a b))).reverse := by
  have hf := funext (schedule_final_scaledStalk cs b basis a hab ht ht1)
  have hi := funext (schedule_initial_scaledStalk cs b basis a hab ht ht1)
  rw [hf,hi,chronologicalSchedule,List.reverse_reverse]
  funext x
  rw [transported_dispatch_matrix (OrderIso.refl (Interval cs a b)) _ (Int.castRingHom ℝ)]
  exact scaledStalk_reciprocity_upper cs b basis t ht.ne' a x

end
end KLInvariance.BruhatGraph
end

end OAI
