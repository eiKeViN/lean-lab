import Mathlib
import ForMathlib.Combinatorics.DirectedPaths.ScalarMap
import ForMathlib.Combinatorics.MomentGraph.Boundary.Extension
import ForMathlib.RepresentationTheory.Hecke.DyerPaths.Wall
import ForMathlib.RepresentationTheory.KazhdanLusztig.Polynomials.ScaledReciprocity
import OAI.KL.BottSamelson.CanonicalPairing
import OAI.KL.Sheaves.StalkReciprocity

/-! Semantic home: OAI.KL.Comparison.Transport. Source spans: EdgeLocalization:5, EdgeLocalization:6, EdgeLocalization:1, EdgeLocalization:4, EdgeLocalization:19, EdgeLocalization:7.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.BruhatGraph
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W) (u b : W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  (hub : BruhatLE cs u b)
  (C : BoundarySheaf (polynomialGrading_negative ℝ σ)
    (graph cs u b) (polynomialLabel cs u b basis) ⟨b,hub,bruhat_refl cs b⟩)
noncomputable section

 theorem boundarySheaf_gradedIso :
    Nonempty (GradedSheaf.Iso (boundarySheaf cs u b basis hub).sheaf C.sheaf) := by
  classical
  let : Finite (Interval cs u b) := interval_finite cs u b
  let : Fintype (Interval cs u b) := Fintype.ofFinite _
  let : Fintype (Edge cs u b) := Fintype.ofFinite _
  exact BoundarySheaf.exists_gradedIso (polynomialGrading_zero ℝ σ)
    (boundarySheaf cs u b basis hub) C (fun x => x.property.2)

 theorem stalkCharacter_eq_character (x : Interval cs u b) :
    let _ := C.free x
    stalkCharacter cs u b basis hub x =
      Graded.character (σ := σ) (C.sheaf.vertex x).piece (C.sheaf.vertex x).nonneg := by
  let _ := C.free x
  let B := boundarySheaf cs u b basis hub
  let _ := B.free x
  obtain ⟨j⟩ := boundarySheaf_gradedIso cs u b basis hub C
  exact ModuleData.character_eq_of_gradedEquiv (j.vertex x) (j.vertex_graded x)

end
end KLInvariance.BruhatGraph
end


section
namespace KLInvariance.BruhatGraph
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W) (u b : W)
noncomputable section

 def upperInclusion : GraphMap (graph cs u b) (graph cs 1 b) where
  vertex x := ⟨x.val,one_bruhat cs x.val,x.property.2⟩
  edge e := ⟨(⟨(source cs u b e).val,one_bruhat cs _,(source cs u b e).property.2⟩,
    ⟨(target cs u b e).val,one_bruhat cs _,(target cs u b e).property.2⟩),e.property⟩
  source _ := rfl
  target _ := rfl

omit [Fintype I] in
 theorem upperInclusion_injective : Function.Injective (upperInclusion cs u b).vertex := by
  intro x y h
  exact Subtype.ext (congrArg (fun z : Interval cs 1 b => z.val) h)

omit [Fintype I] in
 theorem upperInclusion_outgoing (e : Edge cs 1 b) (x : Interval cs u b)
    (hx : (upperInclusion cs u b).vertex x = source cs 1 b e) :
    ∃ a, (upperInclusion cs u b).edge a=e ∧ source cs u b a=x := by
  have hxval := congrArg Subtype.val hx
  let y : Interval cs u b := ⟨(target cs 1 b e).val,
    bruhat_trans cs x.property.1 (hxval.symm ▸ Relation.ReflTransGen.single e.property),
    (target cs 1 b e).property.2⟩
  let a : Edge cs u b := ⟨(x,y),hxval.symm ▸ e.property⟩
  refine ⟨a,?_,rfl⟩
  apply Subtype.ext
  apply Prod.ext
  · exact hx
  · rfl

variable {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  (hub : BruhatLE cs u b)
  (B : BoundarySheaf (polynomialGrading_negative ℝ σ)
    (graph cs 1 b) (polynomialLabel cs 1 b basis) ⟨b,one_bruhat cs b,bruhat_refl cs b⟩)

 def restrictBoundary : BoundarySheaf (polynomialGrading_negative ℝ σ)
    (graph cs u b) (polynomialLabel cs u b basis) ⟨b,hub,bruhat_refl cs b⟩ :=
  B.pullback (upperInclusion cs u b) (upperInclusion_injective cs u b)
    (upperInclusion_outgoing cs u b) ⟨b,hub,bruhat_refl cs b⟩ rfl

 theorem stalkCharacter_upperRestriction (x : Interval cs u b) :
    let _ := B.free ((upperInclusion cs u b).vertex x)
    stalkCharacter cs u b basis hub x =
      Graded.character (σ := σ) (B.sheaf.vertex ((upperInclusion cs u b).vertex x)).piece
        (B.sheaf.vertex ((upperInclusion cs u b).vertex x)).nonneg :=
  stalkCharacter_eq_character cs u b basis hub (restrictBoundary cs u b basis hub B) x

end
end KLInvariance.BruhatGraph
end


section
namespace KLInvariance.BruhatGraph
open TitsSpace SchedulePaths
universe u v u' v'
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {I' : Type u'} [Fintype I'] {M' : CoxeterMatrix I'}
  {W' : Type v'} [Group W'] {cs' : CoxeterSystem M' W'}
  {u b : W} {u' b' : W'}
  (φ : Interval cs u b ≃o Interval cs' u' b')
noncomputable section
local instance _root_.OAI.KLInvariance.BruhatGraph.instDecidable_oAI_6 (p : Prop) : Decidable p := Classical.propDecidable p

 def transportedEdge (e : Edge cs u b) : AdaptedDyer.Edge cs' :=
  ⟨((φ (source cs u b e)).val,(φ (target cs u b e)).val),
    (intervalIso_bruhatStep_iff_general cs cs' φ _ _).mpr e.property⟩

omit [Fintype I] [Fintype I'] in
 theorem transportedEdge_injective : Function.Injective (transportedEdge φ) := by
  intro e f h
  apply Subtype.ext
  have hh := congrArg Subtype.val h
  exact Prod.ext (φ.injective (Subtype.ext (congrArg Prod.fst hh)))
    (φ.injective (Subtype.ext (congrArg Prod.snd hh)))

 def transportedScore (e : Edge cs u b) : ℝ ×ₗ ℝ :=
  lexEdgeScore (geometricFunctional (M := M') (cs := cs')) (transportedEdge φ e)

 /-- Decreasing list, in the convention for the outermost-first matrix
 product. Its reverse is chronological increasing reflection order. -/
 def transportedSchedule : List (Edge cs u b) := by
  letI := Fintype.ofFinite (Edge cs u b)
  exact sortedSchedule Finset.univ (transportedScore φ)

omit [Fintype I] in
 theorem transportedSchedule_nodup : (transportedSchedule φ).Nodup := by
  unfold transportedSchedule
  exact sortedSchedule_nodup _ _

omit [Fintype I] in
 theorem transportedSchedule_full (e : Edge cs u b) : e ∈ transportedSchedule φ := by
  let := Fintype.ofFinite (Edge cs u b)
  unfold transportedSchedule
  exact (mem_sortedSchedule _ _ _).mpr (Finset.mem_univ _)

omit [Fintype I] in
 theorem transportedSchedule_pairwise : (transportedSchedule φ).Pairwise
     (fun e f => transportedScore φ f ≤ transportedScore φ e) := by
  unfold transportedSchedule
  exact sortedSchedule_pairwise _ _

omit [Fintype I] [Fintype I'] in
 theorem transportedEdge_lift (e : AdaptedDyer.Edge cs')
    (hu : BruhatLE cs' u' (AdaptedDyer.source cs' e))
    (hb : BruhatLE cs' (AdaptedDyer.target cs' e) b') : ∃ f, transportedEdge φ f=e := by
  let x : Interval cs' u' b' := ⟨AdaptedDyer.source cs' e,hu,
    (show BruhatLE cs' (AdaptedDyer.source cs' e) (AdaptedDyer.target cs' e) from
      .single e.property).trans hb⟩
  let y : Interval cs' u' b' := ⟨AdaptedDyer.target cs' e,
    hu.trans (.single e.property),hb⟩
  let f : Edge cs u b := ⟨(φ.symm x,φ.symm y),
    (intervalIso_bruhatStep_iff_general cs' cs φ.symm x y).mpr e.property⟩
  refine ⟨f,?_⟩
  apply Subtype.ext
  change ((φ (φ.symm x)).val,(φ (φ.symm y)).val)=e.val
  rw [φ.apply_symm_apply,φ.apply_symm_apply]
  rfl

omit [Fintype I'] in
/-- Every edge source on an increasing Bruhat path lies above its start.
This is the source-side path bound used when lifting a path into a transported
interval; it needs no schedule or interval isomorphism. -/
theorem adapted_path_sources_le {z w : W'} {p : List (AdaptedDyer.Edge cs')}
    (hp : IsPath (AdaptedDyer.source cs') (AdaptedDyer.target cs') z w p) :
    ∀ e ∈ p, BruhatLE cs' z (AdaptedDyer.source cs' e) := by
  induction p generalizing z with
  | nil => simp
  | cons e p ih =>
    intro f hf
    rcases List.mem_cons.mp hf with rfl | hf
    · exact hp.1 ▸ bruhat_refl cs' z
    · rw [← hp.1]
      exact (show BruhatLE cs' (AdaptedDyer.source cs' e)
        (AdaptedDyer.target cs' e) from .single e.property).trans (ih hp.2 f hf)

omit [Fintype I] in
 theorem transported_dispatch_entry {R : Type*} [Semiring R] (T : R)
    (x y : Interval cs u b) :
    dispatch (source cs u b) (target cs u b) T (fun z => if z=y then 1 else 0)
      (transportedSchedule φ) x =
    WallDyer.entry (cs := cs') T (geometricFunctional (M := M') (cs := cs'))
      b' (φ x).val (φ y).val := by
  symm
  apply dispatch_entry_graph_embedding (AdaptedDyer.source cs') (AdaptedDyer.target cs')
    (source cs u b) (target cs u b) T
    (lexEdgeScore (geometricFunctional (M := M') (cs := cs')))
    (lexEdgeScore_ties _) (fun z : Interval cs u b => (φ z).val)
    (fun _ _ h => φ.injective (Subtype.ext h)) (transportedEdge φ)
    (transportedEdge_injective φ) (fun _ => rfl) (fun _ => rfl)
    (WallDyer.schedule (geometricFunctional (M := M') (cs := cs')) b')
    (transportedSchedule φ) (sortedSchedule_nodup _ _)
    (transportedSchedule_nodup φ) (sortedSchedule_pairwise _ _)
    (transportedSchedule_pairwise φ) (transportedSchedule_full φ)
  · intro e
    exact (mem_sortedSchedule _ _ _).mpr ((AdaptedDyer.mem_edgeFinset cs' b' _).mpr
      (φ (target cs u b e)).property.2)
  · intro r hr e he
    have hp := ((mem_subpaths _ _ _ _ _ r).mp hr).2
    exact transportedEdge_lift φ e ((φ x).property.1.trans (adapted_path_sources_le hp e he))
      ((AdaptedDyer.path_targets_le cs' hp e he).trans (φ y).property.2)

omit [Fintype I] in

 theorem transported_entry_eq_rTilde (x y : Interval cs u b) :
    dispatch (source cs u b) (target cs u b) (Polynomial.X : Polynomial ℤ)
      (fun z => if z=y then 1 else 0) (transportedSchedule φ) x =
      Hecke.rTilde cs' (φ x).val (φ y).val := by
  rw [transported_dispatch_entry]
  exact WallDyer.geometric_entry_eq_rTilde b' (φ x).val (φ y).val
    (φ x).property.2 (φ y).property.2

end
end KLInvariance.BruhatGraph
end


section
namespace KLInvariance.BruhatGraph
open TitsSpace SchedulePaths
universe u v u' v'
variable {I : Type u} {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {I' : Type u'} [Fintype I'] {M' : CoxeterMatrix I'}
  {W' : Type v'} [Group W'] {cs' : CoxeterSystem M' W'}
  {u b : W} {u' b' : W'}
  (φ : Interval cs u b ≃o Interval cs' u' b')
noncomputable section
local instance _root_.OAI.KLInvariance.BruhatGraph.instDecidable_oAI_7 (p : Prop) : Decidable p := Classical.propDecidable p

 theorem transported_entry_eval {C : Type*} [CommSemiring C] (T : C)
    (x y : Interval cs u b) (f : ℤ →+* C) :
    dispatch (source cs u b) (target cs u b) T
      (fun z => if z=y then 1 else 0) (transportedSchedule φ) x =
      Polynomial.eval₂ f T (Hecke.rTilde cs' (φ x).val (φ y).val) := by
  rw [← transported_entry_eq_rTilde φ x y]
  have h := dispatch_map (source cs u b) (target cs u b) (Polynomial.eval₂RingHom f T)
    Polynomial.X (fun z : Interval cs u b => if z=y then 1 else 0) (transportedSchedule φ) x
  simpa using h.symm

 theorem transported_dispatch_matrix {C : Type*} [CommSemiring C] (T : C)
    (f : ℤ →+* C) (v : Interval cs u b → C) (x : Interval cs u b) :
    dispatch (source cs u b) (target cs u b) T v (transportedSchedule φ) x =
      ∑ᶠ y : Interval cs u b,
        Polynomial.eval₂ f T (Hecke.rTilde cs' (φ x).val (φ y).val) * v y := by
  let := interval_finite cs u b
  let := Fintype.ofFinite (Interval cs u b)
  rw [dispatch_eq_sum_entries,finsum_eq_sum_of_fintype]
  exact Finset.sum_congr rfl (fun y _ => congrArg (fun a => a*v y)
    (transported_entry_eval φ T x y f))

 theorem transported_reciprocal_vector {C : Type*} [Field C]
    (t : C) (ht : t ≠ 0) (x : Interval cs u b) :
    scaledKL cs' t (φ x).val b' =
      dispatch (source cs u b) (target cs u b) (t⁻¹-t)
        (fun y => scaledKL cs' t⁻¹ (φ y).val b') (transportedSchedule φ) x := by
  let := interval_finite cs u b
  let := Fintype.ofFinite (Interval cs u b)
  let := interval_finite cs' u' b'
  let := Fintype.ofFinite (Interval cs' u' b')
  rw [transported_dispatch_matrix φ _ (Int.castRingHom C),
    scaledKL_reciprocity_upper cs' t ht u' b' (φ x),
    finsum_eq_sum_of_fintype,finsum_eq_sum_of_fintype]
  exact (φ.toEquiv.sum_comp _).symm

end
end KLInvariance.BruhatGraph
end


section
namespace KLInvariance.BruhatGraph
open Module _root_.OAI.KLInvariance.Graded MomentGraph TitsSpace
universe u
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W) (b : W)
  {σ : Type u} [Fintype σ] (basis : Basis σ ℝ (Extended M))
noncomputable section

 theorem boundarySheaf_symmetricPairing :
    Nonempty (GradedSheaf.SymmetricPerfectPairing
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
  obtain ⟨p⟩ := symmetricBoundarySheaf_symmetricPairing cs basis b
  obtain ⟨j⟩ := BoundarySheaf.iso_coefficientChange e he S T
    (polynomialGrading_zero ℝ σ) (fun x => x.property.2)
  exact ⟨(p.coefficientChange e he).pullback j⟩

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
local instance scaledInterval : Fintype (Interval cs 1 b) := by
  let := interval_finite cs 1 b
  exact Fintype.ofFinite _

 theorem stalkCharacter_natDegree_le (x : Interval cs 1 b) :
    (stalkCharacter cs 1 b basis (one_bruhat cs b) x).natDegree≤rankDifference cs x.val b := by
  classical
  let B := boundarySheaf cs 1 b basis (one_bruhat cs b)
  let := B.free x
  let c := (exists_nonnegativeBasis (σ := σ) (B.sheaf.vertex x).piece
    (B.sheaf.vertex x).nonneg).some
  rw [stalkCharacter_eq_character cs 1 b basis (one_bruhat cs b) B x,
    character_eq (B.sheaf.vertex x).piece (B.sheaf.vertex x).nonneg c]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i _
  simpa only [Polynomial.natDegree_X_pow] using stalkBasis_degree_le cs b basis x c i

 def scaledStalk {C : Type*} [Field C] (t : C) (x : Interval cs 1 b) : C :=
  t^((cs.length x.val : ℤ)-cs.length b)*
    eval₂ (Int.castRingHom C) (t^2) (stalkCharacter cs 1 b basis (one_bruhat cs b) x)

/-- A squared reciprocal degree weight reverses the grading exponent.
This field identity is shared by scaled-stalk polynomial reciprocity and the
normalization of the full-kernel Hilbert expression; no positivity is required. -/
theorem reciprocal_square_weight {C : Type*} [Field C] (v : C) (hv : v ≠ 0)
    (m n : ℤ) : v^(m-n) * (v^2)^(n-m) = (v⁻¹)^(m-n) := by
  rw [show (v^2)^(n-m) = v^(2*(n-m)) by rw [zpow_mul]; norm_num,
    ← zpow_add₀ hv,inv_zpow,← zpow_neg]
  congr 1
  omega

/-- Evaluating polynomial stalk reciprocity at the nonzero square gives a
reciprocal-point identity before any degree weights are normalized. The degree
bound justifies evaluating the reflected stalk polynomial. -/
theorem stalkCharacter_reciprocity_eval {C : Type*} [Field C]
    (v : C) (hv : v ≠ 0) (x : Interval cs 1 b) :
    (v^2)^(rankDifference cs x.val b) *
      eval₂ (Int.castRingHom C) ((v⁻¹)^2) (stalkCharacter cs 1 b basis (one_bruhat cs b) x) =
    ∑ z : Interval cs 1 b,
      eval₂ (Int.castRingHom C) (v^2) (OrdinaryR.polynomial cs x.val z.val) *
        eval₂ (Int.castRingHom C) (v^2) (stalkCharacter cs 1 b basis (one_bruhat cs b) z) := by
  classical
  have hrec := stalkCharacter_reciprocity cs basis b x
  let q : Cˣ := Units.mk0 (v^2) (pow_ne_zero 2 hv)
  have heval := congrArg (eval₂ (Int.castRingHom C) (q : C)) hrec
  rw [eval₂_reflect_unit q _ _ (stalkCharacter_natDegree_le cs b basis x)] at heval
  simp only [eval₂_finsetSum,eval₂_mul] at heval
  have hq : (q : C)=v^2 := rfl
  have hqi : (↑q⁻¹ : C)=(v⁻¹)^2 := by simp [q,inv_pow]
  rw [hq,hqi] at heval
  exact heval

/-- Each ordinary R-polynomial summand acquires exactly the target stalk's
weight after normalization. This combines R-tilde normalization and addition of
the two grading exponents, with no extra comparability hypothesis on the vertices. -/
theorem scaledStalk_rTilde_term {C : Type*} [Field C]
    (v : C) (hv : v ≠ 0) (x z : Interval cs 1 b) :
    v^((cs.length x.val : ℤ)-cs.length b) *
      (eval₂ (Int.castRingHom C) (v^2) (OrdinaryR.polynomial cs x.val z.val) *
        eval₂ (Int.castRingHom C) (v^2) (stalkCharacter cs 1 b basis (one_bruhat cs b) z)) =
    eval₂ (Int.castRingHom C) (v-v⁻¹) (Hecke.rTilde cs x.val z.val) *
      scaledStalk cs b basis v z := by
  have hr : OrdinaryR.polynomial cs x.val z.val=rPolynomial cs x.val z.val :=
    (rPolynomial_eq_constructed cs x.val z.val).symm
  rw [hr,rPolynomial_normalization cs v hv]
  unfold scaledStalk
  calc
    _ = (v^((cs.length x.val : ℤ)-cs.length b)*v^((cs.length z.val : ℤ)-cs.length x.val))*
        eval₂ (Int.castRingHom C) (v-v⁻¹) (Hecke.rTilde cs x.val z.val)*
        eval₂ (Int.castRingHom C) (v^2) (stalkCharacter cs 1 b basis (one_bruhat cs b) z) := by ring
    _ = _ := by
      rw [←zpow_add₀ hv,show (cs.length x.val : ℤ)-cs.length b+
        ((cs.length z.val : ℤ)-cs.length x.val)=(cs.length z.val : ℤ)-cs.length b by ring]
      ring

 theorem scaledStalk_reciprocity_inverse {C : Type*} [Field C]
    (v : C) (hv : v≠0) (x : Interval cs 1 b) :
    scaledStalk cs b basis v⁻¹ x=∑ z : Interval cs 1 b,
      eval₂ (Int.castRingHom C) (v-v⁻¹) (Hecke.rTilde cs x.val z.val)*
        scaledStalk cs b basis v z := by
  classical
  have heval := stalkCharacter_reciprocity_eval cs b basis v hv x
  have heq := congrArg (fun a : C => v^((cs.length x.val : ℤ)-cs.length b)*a) heval
  have hd : (rankDifference cs x.val b : ℤ)=(cs.length b : ℤ)-cs.length x.val := by
    simp [rankDifference,Int.ofNat_sub (length_le_of_bruhat cs x.property.2)]
  have hscale : v^((cs.length x.val : ℤ)-cs.length b)*(v^2)^(rankDifference cs x.val b)=
      (v⁻¹)^((cs.length x.val : ℤ)-cs.length b) := by
    rw [← zpow_natCast (v^2) (rankDifference cs x.val b),hd]
    exact reciprocal_square_weight v hv _ _
  rw [←mul_assoc,hscale,Finset.mul_sum] at heq
  change (v⁻¹)^((cs.length x.val : ℤ)-cs.length b)*
    eval₂ (Int.castRingHom C) ((v⁻¹)^2) (stalkCharacter cs 1 b basis (one_bruhat cs b) x)=_
  rw [heq]
  apply Finset.sum_congr rfl
  intro z _
  exact scaledStalk_rTilde_term cs b basis v hv x z

 theorem scaledStalk_reciprocity {C : Type*} [Field C]
    (t : C) (ht : t≠0) (x : Interval cs 1 b) :
    scaledStalk cs b basis t x=∑ z : Interval cs 1 b,
      eval₂ (Int.castRingHom C) (t⁻¹-t) (Hecke.rTilde cs x.val z.val)*
        scaledStalk cs b basis t⁻¹ z := by
  simpa only [inv_inv] using scaledStalk_reciprocity_inverse cs b basis t⁻¹ (inv_ne_zero ht) x

omit [Fintype I] in
/-- Triangular R-tilde support restricts any weighted row sum to an upper
interval. The weights are arbitrary and the coefficient ring need not be a field;
scaled-stalk reciprocity uses this after its algebraic reciprocal identity. -/
theorem rTilde_weighted_sum_upper {C : Type*} [CommRing C] (T : C)
    (a : W) (x : Interval cs a b) (w : Interval cs 1 b → C) :
    (∑ z : Interval cs 1 b,
      eval₂ (Int.castRingHom C) T (Hecke.rTilde cs x.val z.val) * w z) =
    ∑ᶠ z : Interval cs a b,
      eval₂ (Int.castRingHom C) T (Hecke.rTilde cs x.val z.val) *
        w ((upperInclusion cs a b).vertex z) := by
  classical
  let := interval_finite cs a b
  let := Fintype.ofFinite (Interval cs a b)
  rw [finsum_eq_sum_of_fintype]
  let e : {z : Interval cs 1 b // BruhatLE cs a z.val} ≃ Interval cs a b :=
    ⟨fun z => ⟨z.val.val,z.property,z.val.property.2⟩,
      fun z => ⟨(upperInclusion cs a b).vertex z,z.property.1⟩,fun _ => rfl,fun _ => rfl⟩
  let g (z : Interval cs 1 b) := eval₂ (Int.castRingHom C) T
    (Hecke.rTilde cs x.val z.val) * w z
  change (∑ z : Interval cs 1 b, g z)=_
  calc
    _ = ∑ z ∈ Finset.univ.filter (fun z : Interval cs 1 b => BruhatLE cs a z.val),g z := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro z _ hz
      have hnot : ¬BruhatLE cs x.val z.val := by
        intro hxz
        exact hz (Finset.mem_filter.mpr ⟨Finset.mem_univ _,bruhat_trans cs x.property.1 hxz⟩)
      simp [g,Hecke.rTilde_zero cs x.val z.val hnot]
    _ = ∑ z : {z : Interval cs 1 b // BruhatLE cs a z.val}, g z.val :=
      Finset.sum_subtype _ (by simp) g
    _ = _ := Equiv.sum_comp e (fun z => eval₂ (Int.castRingHom C) T
      (Hecke.rTilde cs x.val z.val) * w ((upperInclusion cs a b).vertex z))

 theorem scaledStalk_reciprocity_upper {C : Type*} [Field C]
    (t : C) (ht : t≠0) (a : W) (x : Interval cs a b) :
    scaledStalk cs b basis t ((upperInclusion cs a b).vertex x)=
      ∑ᶠ z : Interval cs a b,
        eval₂ (Int.castRingHom C) (t⁻¹-t) (Hecke.rTilde cs x.val z.val)*
          scaledStalk cs b basis t⁻¹ ((upperInclusion cs a b).vertex z) := by
  rw [scaledStalk_reciprocity cs b basis t ht]
  exact rTilde_weighted_sum_upper cs b (t⁻¹-t) a x
    (fun z => scaledStalk cs b basis t⁻¹ z)

end
end KLInvariance.BruhatGraph
end

end OAI
