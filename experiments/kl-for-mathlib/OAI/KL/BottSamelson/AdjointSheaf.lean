import Mathlib
import ForMathlib.Algebra.Module.Graded.Adjoint
import ForMathlib.Algebra.Module.Localization.Lattice
import ForMathlib.Combinatorics.MomentGraph.Boundary.Summand
import ForMathlib.LinearAlgebra.ConjugateRange
import ForMathlib.LinearAlgebra.Dual.TransportPairing
import OAI.KL.BottSamelson.UpperSections

/-! Semantic home: OAI.KL.BottSamelson.AdjointSheaf. Source spans: BalancedPairings:20, BalancedPairings:3, BalancedPairings:5, BalancedPairings:1, BalancedPairings:6, BalancedPairings:2, BalancedPairings:35, BalancedPairings:8, BalancedPairings:11, BalancedPairings:12, BalancedPairings:21, BalancedPairings:24, BalancedPairings:27, BalancedPairings:23, BalancedPairings:30, BalancedPairings:34.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.TitsSpace
open Module
universe u us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))

include basis in
 theorem symmetricCoefficientNoetherian : IsNoetherianRing (SymmetricCoefficient (M := M)) :=
  isNoetherianRing_of_surjective (MvPolynomial σ ℝ) (SymmetricCoefficient (M := M))
    (SymmetricAlgebra.equivMvPolynomial basis).symm.toRingHom
    (SymmetricAlgebra.equivMvPolynomial basis).symm.surjective

end KLInvariance.TitsSpace
end


section
namespace KLInvariance.TitsSpace
open Module MomentGraph BruhatGraph FiniteCharacterLocalization
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

 def bottVertexProjection (l : List I) (u b : W) : BottSamelsonModule cs l →ₗ[
    SymmetricCoefficient (M := M)]
    (∀ x : Interval cs u b, bottStalk cs l x.val) :=
  LinearMap.pi (fun x => bottStalkProjection cs l x.val)

 theorem bottVertexProjection_injective (l : List I) (hl : cs.IsReduced l) :
    Function.Injective (bottVertexProjection cs l 1 (cs.wordProd l)) := by
  intro m n h
  apply bottSection_injective cs l hl
  exact Subtype.ext h

 theorem bottVertexProjection_stable (l : List I) (u b : W)
    (a : SymmetricCoefficient (M := M)) :
    (fun x : Interval cs u b => coefficientAction cs x.val a) ∈
      stabilizer (LinearMap.range (bottVertexProjection cs l u b)) := by
  rintro z ⟨m,rfl⟩
  refine ⟨bottSamelsonRight cs l a m,?_⟩
  funext x
  exact bottStalkProjection_right cs l x.val a m

 theorem bottVertexProjection_scaled (l : List I) (hl : cs.IsReduced l)
    (z : ∀ x : Interval cs 1 (cs.wordProd l), bottStalk cs l x.val) :
    bottCoordinateDenominator cs l • z ∈
      LinearMap.range (bottVertexProjection cs l 1 (cs.wordProd l)) := by
  let c (e : BottIndex l) : SymmetricCoefficient (M := M) :=
    (z ⟨bottWeight cs l e,one_bruhat cs _,bottWeight_bruhat cs l hl e⟩).val ⟨e,rfl⟩
  obtain ⟨m,hm⟩ := bottEvaluation_contains_scaled_coordinates cs l c
  refine ⟨m,?_⟩
  funext x
  apply Subtype.ext
  funext e
  rcases x with ⟨x,hx⟩
  rcases e with ⟨e,he⟩
  change bottWeight cs l e=x at he
  subst x
  exact hm e


 theorem bottSection_pair_lift (l : List I) (u b : W)
    (s : (bottProjectionSheaf cs l u b).sections Set.univ)
    (x y : Interval cs u b) (t : W) (ht : cs.IsReflection t) (he : t*x.val=y.val) :
    ∃ m : BottSamelsonModule cs l,
      bottStalkProjection cs l x.val m=s.val x ∧ bottStalkProjection cs l y.val m=s.val y := by
  have he' : t*y.val=x.val := by
    rw [← he,← mul_assoc,ht.mul_self,one_mul]
  have hne : cs.length y.val ≠ cs.length x.val := by
    rw [← he]
    exact ht.length_mul_right_ne x.val
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · let e : Edge cs u b := ⟨(y,x),hlt,⟨t,ht,he'.symm⟩⟩
    have hs := s.property e (Set.mem_univ _) (Set.mem_univ _)
    obtain ⟨m,hm,hn⟩ := (PairProjection.compatible_iff _ _ _ _).mp hs
    exact ⟨m,hn,hm⟩
  · let e : Edge cs u b := ⟨(x,y),hlt,⟨t,ht,he.symm⟩⟩
    have hs := s.property e (Set.mem_univ _) (Set.mem_univ _)
    exact (PairProjection.compatible_iff _ _ _ _).mp hs

 theorem bottSection_prime_lift (l : List I) (u b : W)
    (s : (bottProjectionSheaf cs l u b).sections Set.univ)
    (p : SymmetricCoefficient (M := M)) (hp : Prime p) (x : Interval cs u b) :
    ∃ m : BottSamelsonModule cs l, ∀ y : Interval cs u b,
      (∀ a, p ∣ coefficientAction cs x.val a-coefficientAction cs y.val a) →
      bottStalkProjection cs l y.val m=s.val y := by
  classical
  by_cases hx : ∃ y : Interval cs u b, x ≠ y ∧
      ∀ a, p ∣ coefficientAction cs x.val a-coefficientAction cs y.val a
  · obtain ⟨y,hxy,hcon⟩ := hx
    obtain ⟨t,ht,he,hclass⟩ := prime_character_class cs p hp
      (fun h => hxy (Subtype.ext h)) hcon
    obtain ⟨m,hm,hn⟩ := bottSection_pair_lift cs l u b s x y t ht he.symm
    refine ⟨m,?_⟩
    intro z hz
    rcases (hclass z.val).mp hz with hxz | hzy
    · have h : z=x := Subtype.ext hxz.symm
      subst z
      exact hm
    · have h : z=y := Subtype.ext (hzy.trans he.symm)
      subst z
      exact hn
  · obtain ⟨m,hm⟩ := bottStalkProjection_surjective cs l x.val (s.val x)
    refine ⟨m,?_⟩
    intro y hy
    have h : y=x := by
      by_contra h
      exact hx ⟨y,Ne.symm h,hy⟩
    subst y
    exact hm

 theorem bottSection_local_denominator (l : List I) (u b : W)
    (s : (bottProjectionSheaf cs l u b).sections Set.univ)
    (p : SymmetricCoefficient (M := M)) (hp : Prime p) :
    ∃ a : SymmetricCoefficient (M := M), ¬ p ∣ a ∧ a • s.val ∈
      LinearMap.range (bottVertexProjection cs l u b) := by
  classical
  let : Finite (Interval cs u b) := interval_finite cs u b
  let : Fintype (Interval cs u b) := Fintype.ofFinite _
  apply character_local_denominator (E := fun x : Interval cs u b => bottStalk cs l x.val)
    (LinearMap.range (bottVertexProjection cs l u b)) p hp
    (fun a x => coefficientAction cs x.val a) (fun a => bottVertexProjection_stable cs l u b a) s.val
  intro x
  obtain ⟨m,hm⟩ := bottSection_prime_lift cs l u b s p hp x
  exact ⟨bottVertexProjection cs l u b m,⟨m,rfl⟩,hm⟩

 theorem bottSection_surjective (l : List I) (hl : cs.IsReduced l) :
    Function.Surjective (bottSection cs l 1 (cs.wordProd l)) := by
  intro s
  let L := LinearMap.range (bottVertexProjection cs l 1 (cs.wordProd l))
  let : Module.Free (SymmetricCoefficient (M := M)) L :=
    Module.Free.of_equiv (LinearEquiv.ofInjective _ (bottVertexProjection_injective cs l hl))
  let : UniqueFactorizationMonoid (SymmetricCoefficient (M := M)) :=
    (SymmetricAlgebra.equivMvPolynomial (Module.Free.chooseBasis ℝ (Extended M))).symm.toRingEquiv.toMulEquiv.uniqueFactorizationMonoid inferInstance
  have h : s.val ∈ L := EdgeLattice.mem_of_prime_local_membership L s.val
    ⟨bottCoordinateDenominator cs l,bottCoordinateDenominator_ne_zero cs l,
      bottVertexProjection_scaled cs l hl s.val⟩
    (fun p hp => bottSection_local_denominator cs l 1 (cs.wordProd l) s p hp)
  obtain ⟨m,hm⟩ := h
  exact ⟨m,Subtype.ext hm⟩

 def bottSectionEquiv (l : List I) (hl : cs.IsReduced l) :
    BottSamelsonModule cs l ≃ₗ[SymmetricCoefficient (M := M)]
      (bottProjectionSheaf cs l 1 (cs.wordProd l)).sections Set.univ :=
  LinearEquiv.ofBijective (bottSection cs l 1 (cs.wordProd l))
    ⟨bottSection_injective cs l hl,bottSection_surjective cs l hl⟩

end
end KLInvariance.TitsSpace
end


section
namespace KLInvariance.TitsSpace
open Module MomentGraph BruhatGraph
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

 def bottSectionDuality (l : List I) (hl : cs.IsReduced l) :
    (bottProjectionSheaf cs l 1 (cs.wordProd l)).sections Set.univ ≃ₗ[
      SymmetricCoefficient (M := M)]
      Dual (SymmetricCoefficient (M := M))
        ((bottProjectionSheaf cs l 1 (cs.wordProd l)).sections Set.univ) :=
  (bottSectionEquiv cs l hl).symm.trans
    ((bottSamelsonDuality cs l).trans (bottSectionEquiv cs l hl).symm.dualMap)

 theorem bottSectionDuality_apply (l : List I) (hl : cs.IsReduced l)
    (m n : BottSamelsonModule cs l) :
    bottSectionDuality cs l hl (bottSection cs l 1 (cs.wordProd l) m)
      (bottSection cs l 1 (cs.wordProd l) n) = bottSamelsonDuality cs l m n := by
  change bottSamelsonDuality cs l
    ((bottSectionEquiv cs l hl).symm ((bottSectionEquiv cs l hl) m))
    ((bottSectionEquiv cs l hl).symm ((bottSectionEquiv cs l hl) n))= _
  simp only [LinearEquiv.symm_apply_apply]

 def bottSectionRight (l : List I) (hl : cs.IsReduced l)
    (a : SymmetricCoefficient (M := M)) :
    End (SymmetricCoefficient (M := M))
      ((bottProjectionSheaf cs l 1 (cs.wordProd l)).sections Set.univ) :=
  (bottSectionEquiv cs l hl).toLinearMap.comp
    ((bottSamelsonRight cs l a).comp (bottSectionEquiv cs l hl).symm.toLinearMap)

 theorem bottSectionRight_apply (l : List I) (hl : cs.IsReduced l)
    (a : SymmetricCoefficient (M := M)) (m : BottSamelsonModule cs l) :
    bottSectionRight cs l hl a (bottSection cs l 1 (cs.wordProd l) m) =
      bottSection cs l 1 (cs.wordProd l) (bottSamelsonRight cs l a m) := by
  change (bottSectionEquiv cs l hl) (bottSamelsonRight cs l a
    ((bottSectionEquiv cs l hl).symm ((bottSectionEquiv cs l hl) m))) = _
  rw [LinearEquiv.symm_apply_apply]
  rfl

 theorem bottSectionRight_coordinates (l : List I) (hl : cs.IsReduced l)
    (a : SymmetricCoefficient (M := M))
    (s : (bottProjectionSheaf cs l 1 (cs.wordProd l)).sections Set.univ)
    (x : Interval cs 1 (cs.wordProd l)) :
    (bottSectionRight cs l hl a s).val x=coefficientAction cs x.val a • s.val x := by
  obtain ⟨m,rfl⟩ := bottSection_surjective cs l hl s
  rw [bottSectionRight_apply]
  exact bottStalkProjection_right cs l x.val a m

 theorem bottSection_balanced (l : List I) (hl : cs.IsReduced l)
    (a : SymmetricCoefficient (M := M))
    (s z : (bottProjectionSheaf cs l 1 (cs.wordProd l)).sections Set.univ) :
    bottSectionDuality cs l hl (bottSectionRight cs l hl a s) z =
      bottSectionDuality cs l hl s (bottSectionRight cs l hl a z) := by
  exact TransportPerfectPairing.balanced (bottSectionEquiv cs l hl)
    (bottSamelsonDuality cs l) (bottSamelsonRight cs l a)
    (bottSamelson_balanced cs l a) s z

 theorem bottSection_symmetric (l : List I) (hl : cs.IsReduced l)
    (s z : (bottProjectionSheaf cs l 1 (cs.wordProd l)).sections Set.univ) :
    bottSectionDuality cs l hl s z=bottSectionDuality cs l hl z s := by
  exact TransportPerfectPairing.symmetric (bottSectionEquiv cs l hl)
    (bottSamelsonDuality cs l) (bottSamelson_symmetric cs l) s z

end
end KLInvariance.TitsSpace
end


section
namespace KLInvariance.TitsSpace
open Module _root_.OAI.KLInvariance.Graded
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
noncomputable section

 theorem bottPairing_dualToSupport (l : List I) (x : W)
    (lam : Dual (SymmetricCoefficient (M := M)) (bottStalk cs l x))
    (m : BottSamelsonModule cs l) :
    bottSamelsonDuality cs l (bottStalkDualToSupport cs l x lam).val m =
      lam (bottStalkProjection cs l x m) := by
  change bottSamelsonDuality cs l
    ((bottSamelsonDuality cs l).symm ((bottStalkProjection cs l x).dualMap lam)) m = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

 theorem bottStalkDuality_apply_projection (l : List I) (x : W)
    (s : bottWeightSupported cs l x) (m : BottSamelsonModule cs l) :
    bottStalkDuality cs l x s (bottStalkProjection cs l x m) =
      bottSamelsonDuality cs l s.val m := by
  have he : bottStalkDualToSupport cs l x (bottStalkDuality cs l x s)=s :=
    (LinearEquiv.ofBijective (bottStalkDualToSupport cs l x)
      (bottStalkDualToSupport_bijective cs l x)).apply_symm_apply s
  calc
    _ = bottSamelsonDuality cs l
        (bottStalkDualToSupport cs l x (bottStalkDuality cs l x s)).val m :=
      (bottPairing_dualToSupport cs l x _ m).symm
    _ = _ := by rw [he]

 theorem bottStalkDuality_homogeneous (l : List I) (x : W) (n : ℤ)
    (s : bottWeightSupported cs l x) (hs : s ∈ bottSupportPiece cs basis l x n)
    (j : ℤ) (v : bottStalk cs l x) (hv : v ∈ bottStalkPiece cs basis l x j) :
    bottStalkDuality cs l x s v ∈ symmetricGrading basis (n+j-l.length) := by
  obtain ⟨m,hm,rfl⟩ := bottStalk_homogeneous_lift cs basis l x j v hv
  rw [bottStalkDuality_apply_projection]
  exact bottDuality_homogeneous cs basis l hs hm

 theorem bottDualToSupport_homogeneous (l : List I) (x : W) (r : ℤ)
    (lam : Dual (SymmetricCoefficient (M := M)) (bottStalk cs l x))
    (hlam : ∀ j v, v ∈ bottStalkPiece cs basis l x j →
      lam v ∈ symmetricGrading basis (j+r)) :
    bottStalkDualToSupport cs l x lam ∈ bottSupportPiece cs basis l x (r+l.length) := by
  change (bottSamelsonDuality cs l).symm ((bottStalkProjection cs l x).dualMap lam) ∈
    bottPiece cs basis l (r+l.length)
  apply perfect_inverse_of_homogeneous_functional (symmetricGrading basis) (bottPiece cs basis l)
    (bottSamelsonDuality cs l) l.length
    (fun _ _ _ _ hm hn => bottDuality_homogeneous cs basis l hm hn) r
  intro j m hm
  exact hlam j _ (bottStalkProjection_homogeneous cs basis l x j m hm)

 theorem bottStalkDuality_homogeneous_iff (l : List I) (x : W) (n : ℤ)
    (s : bottWeightSupported cs l x) :
    (∀ j v, v ∈ bottStalkPiece cs basis l x j →
      bottStalkDuality cs l x s v ∈ symmetricGrading basis (n+j-l.length)) ↔
        s ∈ bottSupportPiece cs basis l x n := by
  constructor
  · intro h
    have hh := bottDualToSupport_homogeneous cs basis l x (n-l.length)
      (bottStalkDuality cs l x s) (by
        intro j v hv
        have he : n+j-(l.length:ℤ) = j+(n-l.length) := by omega
        rw [← he]
        exact h j v hv)
    have he : bottStalkDualToSupport cs l x (bottStalkDuality cs l x s)=s :=
      (LinearEquiv.ofBijective (bottStalkDualToSupport cs l x)
        (bottStalkDualToSupport_bijective cs l x)).apply_symm_apply s
    simpa only [he,sub_add_cancel] using hh
  · intro h
    exact bottStalkDuality_homogeneous cs basis l x n s h

end
end KLInvariance.TitsSpace
end


section
namespace KLInvariance.TitsSpace
open Module _root_.OAI.KLInvariance.Graded MomentGraph BruhatGraph
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
noncomputable section

 theorem bottPiece_iff_stalks (l : List I) (hl : cs.IsReduced l) (n : ℤ)
    (m : BottSamelsonModule cs l) : m ∈ bottPiece cs basis l n ↔
      ∀ x : Interval cs 1 (cs.wordProd l),
        bottStalkProjection cs l x.val m ∈ bottStalkPiece cs basis l x.val n := by
  constructor
  · intro hm x
    exact bottStalkProjection_homogeneous cs basis l x.val n m hm
  · intro hm
    have he : component (bottPiece cs basis l) n m=m := by
      apply bottVertexProjection_injective cs l hl
      funext x
      have hh := map_component (bottPiece cs basis l) (bottStalkPiece cs basis l x.val)
        (bottStalkProjection cs l x.val) 0 (by
          simpa only [add_zero] using bottStalkProjection_homogeneous cs basis l x.val) n m
      rw [sub_zero,show component (bottStalkPiece cs basis l x.val) n
        (bottStalkProjection cs l x.val m)=bottStalkProjection cs l x.val m from
        DirectSum.decompose_of_mem_same _ (hm x)] at hh
      exact hh.symm
    rw [← he]
    exact (DirectSum.decompose (bottPiece cs basis l) m n).property

 theorem bottSectionDuality_homogeneous (l : List I) (hl : cs.IsReduced l)
    (i j : ℤ)
    (s z : (bottProjectionSheaf cs l 1 (cs.wordProd l)).sections Set.univ)
    (hs : ∀ x, s.val x ∈ bottStalkPiece cs basis l x.val i)
    (hz : ∀ x, z.val x ∈ bottStalkPiece cs basis l x.val j) :
    bottSectionDuality cs l hl s z ∈ symmetricGrading basis (i+j-l.length) := by
  obtain ⟨m,rfl⟩ := bottSection_surjective cs l hl s
  obtain ⟨n,rfl⟩ := bottSection_surjective cs l hl z
  rw [bottSectionDuality_apply]
  exact bottDuality_homogeneous cs basis l ((bottPiece_iff_stalks cs basis l hl i m).mpr hs)
    ((bottPiece_iff_stalks cs basis l hl j n).mpr hz)

end
end KLInvariance.TitsSpace
end


section
namespace KLInvariance.TitsSpace
open Module _root_.OAI.KLInvariance.Graded
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

 theorem bott_projection_zero_iff_annihilates_support (l : List I) (x : W)
    (m : BottSamelsonModule cs l) :
    bottStalkProjection cs l x m=0 ↔ ∀ s : bottWeightSupported cs l x,
      bottSamelsonDuality cs l s.val m=0 := by
  constructor
  · intro hm s
    exact bott_supported_annihilates cs l x s.property m
      ((bottStalkProjection_eq_zero cs l x m).mp hm)
  · intro h
    apply Subtype.ext
    funext e
    let lam : Dual (SymmetricCoefficient (M := M)) (bottStalk cs l x) :=
      (LinearMap.proj e).comp (bottStalk cs l x).subtype
    have he := h (bottStalkDualToSupport cs l x lam)
    rw [bottPairing_dualToSupport] at he
    exact he

 def bottAdjoint (l : List I) (f : End (SymmetricCoefficient (M := M))
    (BottSamelsonModule cs l)) := PerfectAdjoint.adjoint (bottSamelsonDuality cs l) f

 theorem bottAdjoint_preserves_kernel (l : List I) (x : W)
    (f : End (SymmetricCoefficient (M := M)) (BottSamelsonModule cs l))
    (hf : ∀ s, s ∈ bottWeightSupported cs l x → f s ∈ bottWeightSupported cs l x)
    (m : BottSamelsonModule cs l) (hm : bottStalkProjection cs l x m=0) :
    bottStalkProjection cs l x (bottAdjoint cs l f m)=0 := by
  apply (bott_projection_zero_iff_annihilates_support cs l x _).mpr
  intro s
  change bottSamelsonDuality cs l s.val (PerfectAdjoint.adjoint (bottSamelsonDuality cs l) f m)=0
  rw [PerfectAdjoint.symmetric_pairing (bottSamelsonDuality cs l)
    (bottSamelson_symmetric cs l)]
  exact (bott_projection_zero_iff_annihilates_support cs l x m).mp hm ⟨f s.val,hf s.val s.property⟩

 theorem bottAdjoint_preserves_support (l : List I) (x : W)
    (f : End (SymmetricCoefficient (M := M)) (BottSamelsonModule cs l))
    (hf : ∀ m, bottStalkProjection cs l x m=0 → bottStalkProjection cs l x (f m)=0)
    (m : BottSamelsonModule cs l) (hm : m ∈ bottWeightSupported cs l x) :
    bottAdjoint cs l f m ∈ bottWeightSupported cs l x := by
  apply bott_annihilates_supported cs l x
  intro n hn
  change bottSamelsonDuality cs l (PerfectAdjoint.adjoint (bottSamelsonDuality cs l) f m) n=0
  rw [PerfectAdjoint.pairing]
  apply bott_supported_annihilates cs l x hm
  exact (bottStalkProjection_eq_zero cs l x (f n)).mp
    (hf n ((bottStalkProjection_eq_zero cs l x n).mpr hn))

 theorem bottAdjoint_homogeneous
    {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
    (l : List I) (f : End (SymmetricCoefficient (M := M)) (BottSamelsonModule cs l))
    (hf : ∀ n m, m ∈ bottPiece cs basis l n → f m ∈ bottPiece cs basis l n)
    (n : ℤ) (m : BottSamelsonModule cs l) (hm : m ∈ bottPiece cs basis l n) :
    bottAdjoint cs l f m ∈ bottPiece cs basis l n :=
  adjoint_homogeneous (symmetricGrading basis) (bottPiece cs basis l)
    (bottSamelsonDuality cs l) l.length
    (fun _ _ _ _ h1 h2 => bottDuality_homogeneous cs basis l h1 h2) f hf n m hm

end
end KLInvariance.TitsSpace
end


section
namespace KLInvariance.TitsSpace
open Module _root_.OAI.KLInvariance.Graded
universe u us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  (l : List I) (hl : cs.IsReduced l)
noncomputable section

omit [Fintype σ] in
 theorem bottTopStalkEquiv_homogeneous_iff (n : ℤ)
    (s : bottStalk cs l (cs.wordProd l)) :
    bottTopStalkEquiv cs l hl s ∈ symmetricGrading basis n ↔
      s ∈ bottStalkPiece cs basis l (cs.wordProd l) n := by
  constructor
  · intro hs e _
    have he : e=⟨bottFullIndex l,bottWeight_full cs l⟩ :=
      Subtype.ext (bottWeight_eq_top cs l hl e.val e.property)
    subst e
    exact hs
  · intro hs
    exact hs ⟨bottFullIndex l,bottWeight_full cs l⟩ (Set.mem_univ _)

 def bottTopHom : ModuleData.Hom (bottStalkData cs basis l (cs.wordProd l))
    (ModuleData.unit (symmetricGrading_negative basis)) where
  map := LinearMap.pi (fun _ => (bottTopStalkEquiv cs l hl).toLinearMap)
  graded := by
    intro n s hs j
    change bottTopStalkEquiv cs l hl s ∈ symmetricGrading basis (n-0)
    simpa only [sub_zero] using
      (bottTopStalkEquiv_homogeneous_iff cs basis l hl n s).mpr hs

 def bottTopInvHom : ModuleData.Hom (ModuleData.unit (symmetricGrading_negative basis))
    (bottStalkData cs basis l (cs.wordProd l)) where
  map := (bottTopStalkEquiv cs l hl).symm.toLinearMap.comp (LinearMap.proj PUnit.unit)
  graded := by
    intro n a ha
    apply (bottTopStalkEquiv_homogeneous_iff cs basis l hl n _).mp
    change bottTopStalkEquiv cs l hl ((bottTopStalkEquiv cs l hl).symm (a PUnit.unit)) ∈ _
    rw [LinearEquiv.apply_symm_apply]
    have h := ha PUnit.unit
    change a PUnit.unit ∈ symmetricGrading basis (n-0) at h
    simpa only [sub_zero] using h

 theorem bottTopHom_inv (a : ModuleData.unit (symmetricGrading_negative basis)) :
    (bottTopHom cs basis l hl).map ((bottTopInvHom cs basis l hl).map a)=a := by
  funext j
  change bottTopStalkEquiv cs l hl ((bottTopStalkEquiv cs l hl).symm (a PUnit.unit))=a j
  rw [LinearEquiv.apply_symm_apply]

 theorem bottTopInvHom_top (s : bottStalk cs l (cs.wordProd l)) :
    (bottTopInvHom cs basis l hl).map ((bottTopHom cs basis l hl).map s)=s :=
  (bottTopStalkEquiv cs l hl).symm_apply_apply s

end
end KLInvariance.TitsSpace
end


section
namespace KLInvariance.TitsSpace
open Module _root_.OAI.KLInvariance.Graded MomentGraph BruhatGraph
universe u us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  (l : List I) (hl : cs.IsReduced l)
noncomputable section

 def bottEndOfSheaf (h : GradedSheaf.Hom
    (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l))
    (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l))) :
    End (SymmetricCoefficient (M := M)) (BottSamelsonModule cs l) :=
  (bottSectionEquiv cs l hl).symm.toLinearMap.comp
    ((h.sectionMap Set.univ).comp (bottSectionEquiv cs l hl).toLinearMap)

 theorem bottEndOfSheaf_coordinates (h : GradedSheaf.Hom
    (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l))
    (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l)))
    (m : BottSamelsonModule cs l) (x : Interval cs 1 (cs.wordProd l)) :
    bottStalkProjection cs l x.val (bottEndOfSheaf cs basis l hl h m)=
      (h.vertex x).map (bottStalkProjection cs l x.val m) := by
  have he := congrArg (fun s : (bottProjectionSheaf cs l 1 (cs.wordProd l)).sections Set.univ =>
    s.val x) ((bottSectionEquiv cs l hl).apply_symm_apply
      (h.sectionMap Set.univ ((bottSectionEquiv cs l hl) m)))
  exact he

 theorem bottEndOfSheaf_homogeneous (h : GradedSheaf.Hom
    (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l))
    (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l)))
    (n : ℤ) (m : BottSamelsonModule cs l) (hm : m ∈ bottPiece cs basis l n) :
    bottEndOfSheaf cs basis l hl h m ∈ bottPiece cs basis l n := by
  apply (bottPiece_iff_stalks cs basis l hl n _).mpr
  intro x
  rw [bottEndOfSheaf_coordinates]
  exact (h.vertex x).graded n _ (bottStalkProjection_homogeneous cs basis l x.val n m hm)

 theorem bottEndOfSheaf_preserves_kernel (h : GradedSheaf.Hom
    (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l))
    (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l)))
    (x : Interval cs 1 (cs.wordProd l)) (m : BottSamelsonModule cs l)
    (hm : bottStalkProjection cs l x.val m=0) :
    bottStalkProjection cs l x.val (bottEndOfSheaf cs basis l hl h m)=0 := by
  rw [bottEndOfSheaf_coordinates,hm]
  exact (h.vertex x).map.map_zero

 theorem bottEndOfSheaf_preserves_support (h : GradedSheaf.Hom
    (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l))
    (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l)))
    (x : Interval cs 1 (cs.wordProd l)) (m : BottSamelsonModule cs l)
    (hm : m ∈ bottWeightSupported cs l x.val) :
    bottEndOfSheaf cs basis l hl h m ∈ bottWeightSupported cs l x.val := by
  intro e he
  let y : Interval cs 1 (cs.wordProd l) :=
    ⟨bottWeight cs l e,one_bruhat cs _,bottWeight_bruhat cs l hl e⟩
  have hmy : bottStalkProjection cs l y.val m=0 := by
    apply Subtype.ext
    funext f
    exact hm f.val (fun hx => he (f.property.symm.trans hx))
  have hfy := bottEndOfSheaf_preserves_kernel cs basis l hl h y m hmy
  exact congrFun (congrArg Subtype.val hfy) ⟨e,rfl⟩

end
end KLInvariance.TitsSpace
end


section
namespace KLInvariance.TitsSpace
open Module _root_.OAI.KLInvariance.Graded MomentGraph BruhatGraph
universe u us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  (l : List I) (hl : cs.IsReduced l)
noncomputable section

 def bottAdjointWordHom (h : GradedSheaf.Hom
    (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l))
    (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l))) :
    ModuleData.Hom (bottWordData cs basis l) (bottWordData cs basis l) where
  map := bottAdjoint cs l (bottEndOfSheaf cs basis l hl h)
  graded := bottAdjoint_homogeneous cs basis l _
    (bottEndOfSheaf_homogeneous cs basis l hl h)

 theorem bottAdjointWordHom_kernel (h : GradedSheaf.Hom
    (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l))
    (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l)))
    (x : Interval cs 1 (cs.wordProd l)) (m : BottSamelsonModule cs l)
    (hm : bottStalkProjection cs l x.val m=0) :
    bottStalkProjection cs l x.val ((bottAdjointWordHom cs basis l hl h).map m)=0 :=
  bottAdjoint_preserves_kernel cs l x.val _
    (bottEndOfSheaf_preserves_support cs basis l hl h x) m hm

 def bottAdjointSheaf (h : GradedSheaf.Hom
    (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l))
    (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l))) : GradedSheaf.Hom
    (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l))
    (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l)) where
  vertex x := ModuleData.descended (bottAdjointWordHom cs basis l hl h)
    (bottStalkHom cs basis l x.val) (bottStalkHom_surjective cs basis l x.val)
    (bottAdjointWordHom_kernel cs basis l hl h x)
  edge e := ModuleData.descendedEdge (bottAdjointWordHom cs basis l hl h)
    (bottStalkHom cs basis l (source cs 1 (cs.wordProd l) e).val)
    (bottStalkHom cs basis l (target cs 1 (cs.wordProd l) e).val)
    (bottStalkHom_surjective cs basis l _)
    (bottStalkHom_surjective cs basis l _)
    (bottAdjointWordHom_kernel cs basis l hl h _)
    (bottAdjointWordHom_kernel cs basis l hl h _)
  lower _ x := ModuleData.descendedEdge_lower _ _ _ _ _ _ _ x
  upper _ y := ModuleData.descendedEdge_upper _ _ _ _ _ _ _ y

 theorem bottAdjointSheaf_vertex (h : GradedSheaf.Hom
    (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l))
    (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l)))
    (x : Interval cs 1 (cs.wordProd l)) (m : BottSamelsonModule cs l) :
    ((bottAdjointSheaf cs basis l hl h).vertex x).map (bottStalkProjection cs l x.val m)=
      bottStalkProjection cs l x.val (bottAdjoint cs l (bottEndOfSheaf cs basis l hl h) m) :=
  LinearDescent.descend_apply _ _ _ _ m

 theorem bottEndOfAdjointSheaf (h : GradedSheaf.Hom
    (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l))
    (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l))) :
    bottEndOfSheaf cs basis l hl (bottAdjointSheaf cs basis l hl h)=
      bottAdjoint cs l (bottEndOfSheaf cs basis l hl h) := by
  apply LinearMap.ext
  intro m
  apply bottVertexProjection_injective cs l hl
  funext x
  exact (bottEndOfSheaf_coordinates cs basis l hl _ m x).trans
    (bottAdjointSheaf_vertex cs basis l hl h x m)

end
end KLInvariance.TitsSpace
end


section
namespace KLInvariance.TitsSpace
open Module _root_.OAI.KLInvariance.Graded MomentGraph BruhatGraph
universe u us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  (l : List I) (hl : cs.IsReduced l)
  (h : GradedSheaf.Hom
    (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l))
    (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l)))
noncomputable section

 theorem bottEndOfSheaf_idempotent
    (hh : ∀ x v, (h.vertex x).map ((h.vertex x).map v)=(h.vertex x).map v)
    (m : BottSamelsonModule cs l) :
    bottEndOfSheaf cs basis l hl h (bottEndOfSheaf cs basis l hl h m)=
      bottEndOfSheaf cs basis l hl h m := by
  apply bottVertexProjection_injective cs l hl
  funext x
  change bottStalkProjection cs l x.val _=bottStalkProjection cs l x.val _
  simp only [bottEndOfSheaf_coordinates]
  exact hh x _

 theorem bottAdjointSheaf_vertex_idempotent
    (hh : ∀ x v, (h.vertex x).map ((h.vertex x).map v)=(h.vertex x).map v)
    (x : Interval cs 1 (cs.wordProd l))
    (v : bottStalk cs l x.val) :
    ((bottAdjointSheaf cs basis l hl h).vertex x).map
      (((bottAdjointSheaf cs basis l hl h).vertex x).map v)=
      ((bottAdjointSheaf cs basis l hl h).vertex x).map v := by
  obtain ⟨m,rfl⟩ := bottStalkProjection_surjective cs l x.val v
  simp only [bottAdjointSheaf_vertex]
  exact congrArg (bottStalkProjection cs l x.val)
    (PerfectAdjoint.adjoint_idempotent (bottSamelsonDuality cs l) _
      (bottEndOfSheaf_idempotent cs basis l hl h hh) m)

 theorem bottAdjointSheaf_edge_idempotent
    (hh : ∀ x v, (h.vertex x).map ((h.vertex x).map v)=(h.vertex x).map v)
    (e : Edge cs 1 (cs.wordProd l))
    (v : (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l)).edge e) :
    ((bottAdjointSheaf cs basis l hl h).edge e).map
      (((bottAdjointSheaf cs basis l hl h).edge e).map v)=
      ((bottAdjointSheaf cs basis l hl h).edge e).map v := by
  have hs : Function.Surjective
      ((bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l)).lower e).map :=
    bottProjectionSheaf_lower_surjective cs l 1 (cs.wordProd l) e
  obtain ⟨m,rfl⟩ := hs v
  simp only [(bottAdjointSheaf cs basis l hl h).lower]
  exact congrArg ((bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l)).lower e).map
    (bottAdjointSheaf_vertex_idempotent cs basis l hl h hh _ m)

 theorem bottAdjointSheaf_twice_vertex (x : Interval cs 1 (cs.wordProd l))
    (v : bottStalk cs l x.val) :
    ((bottAdjointSheaf cs basis l hl (bottAdjointSheaf cs basis l hl h)).vertex x).map v=
      (h.vertex x).map v := by
  obtain ⟨m,rfl⟩ := bottStalkProjection_surjective cs l x.val v
  rw [bottAdjointSheaf_vertex,bottEndOfAdjointSheaf]
  change bottStalkProjection cs l x.val
    (PerfectAdjoint.adjoint (bottSamelsonDuality cs l)
      (PerfectAdjoint.adjoint (bottSamelsonDuality cs l) (bottEndOfSheaf cs basis l hl h)) m)=_
  rw [PerfectAdjoint.adjoint_adjoint _ (bottSamelson_symmetric cs l)]
  exact bottEndOfSheaf_coordinates cs basis l hl h m x

end
end KLInvariance.TitsSpace
end


section
namespace KLInvariance.TitsSpace
open Module _root_.OAI.KLInvariance.Graded MomentGraph BruhatGraph
universe u us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  (l : List I) (hl : cs.IsReduced l)
  (h : GradedSheaf.Hom
    (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l))
    (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l)))
noncomputable section

 def bottImageSheaf : GradedSheaf (𝓐 := symmetricGrading basis)
    (graph cs 1 (cs.wordProd l)) := by
  letI := symmetricCoefficientNoetherian basis
  exact h.image

 def bottImageSectionWordEquiv
    (hh : ∀ x v, (h.vertex x).map ((h.vertex x).map v)=(h.vertex x).map v) :
    (bottImageSheaf cs basis l h).forget.sections Set.univ ≃ₗ[
      SymmetricCoefficient (M := M)] LinearMap.range (bottEndOfSheaf cs basis l hl h) := by
  letI := symmetricCoefficientNoetherian basis
  exact (h.imageSectionEquiv hh Set.univ).trans
    (ConjugateRange.equiv (bottSectionEquiv cs l hl) (h.sectionMap Set.univ))

 def bottAdjointImageEquivDual
    (hh : ∀ x v, (h.vertex x).map ((h.vertex x).map v)=(h.vertex x).map v) :
    (bottImageSheaf cs basis l (bottAdjointSheaf cs basis l hl h)).forget.sections Set.univ ≃ₗ[
      SymmetricCoefficient (M := M)]
      Dual (SymmetricCoefficient (M := M))
        ((bottImageSheaf cs basis l h).forget.sections Set.univ) :=
  (bottImageSectionWordEquiv cs basis l hl (bottAdjointSheaf cs basis l hl h)
      (bottAdjointSheaf_vertex_idempotent cs basis l hl h hh)).trans
    ((LinearEquiv.ofEq _ _ (congrArg LinearMap.range
        (bottEndOfAdjointSheaf cs basis l hl h))).trans
      ((PerfectAdjoint.rangeAdjointEquivDualRange (bottSamelsonDuality cs l)
          (bottEndOfSheaf cs basis l hl h)
          (bottEndOfSheaf_idempotent cs basis l hl h hh)).trans
        (bottImageSectionWordEquiv cs basis l hl h hh).dualMap))

 theorem bottImageSectionWordEquiv_coordinates
    (hh : ∀ x v, (h.vertex x).map ((h.vertex x).map v)=(h.vertex x).map v)
    (m : (bottImageSheaf cs basis l h).forget.sections Set.univ)
    (x : Interval cs 1 (cs.wordProd l)) :
    bottStalkProjection cs l x.val ((bottImageSectionWordEquiv cs basis l hl h hh m).val)=
      (m.val x).val := by
  let := symmetricCoefficientNoetherian basis
  exact congrArg (fun s : (bottProjectionSheaf cs l 1 (cs.wordProd l)).sections Set.univ =>
    s.val x) ((bottSectionEquiv cs l hl).apply_symm_apply
      (h.imageInclusion.sectionMap Set.univ m))

 theorem bottImageSectionWordEquiv_homogeneous
    (hh : ∀ x v, (h.vertex x).map ((h.vertex x).map v)=(h.vertex x).map v)
    (n : ℤ) (m : (bottImageSheaf cs basis l h).forget.sections Set.univ)
    (hm : ∀ x, m.val x ∈ ((bottImageSheaf cs basis l h).vertex x).piece n) :
    (bottImageSectionWordEquiv cs basis l hl h hh m).val ∈ bottPiece cs basis l n := by
  apply (bottPiece_iff_stalks cs basis l hl n _).mpr
  intro x
  rw [bottImageSectionWordEquiv_coordinates]
  exact hm x

 theorem bottAdjointImageEquivDual_apply
    (hh : ∀ x v, (h.vertex x).map ((h.vertex x).map v)=(h.vertex x).map v)
    (m : (bottImageSheaf cs basis l (bottAdjointSheaf cs basis l hl h)).forget.sections Set.univ)
    (n : (bottImageSheaf cs basis l h).forget.sections Set.univ) :
    bottAdjointImageEquivDual cs basis l hl h hh m n=bottSamelsonDuality cs l
      (bottImageSectionWordEquiv cs basis l hl (bottAdjointSheaf cs basis l hl h)
        (bottAdjointSheaf_vertex_idempotent cs basis l hl h hh) m).val
      (bottImageSectionWordEquiv cs basis l hl h hh n).val := rfl

 theorem bottAdjointImagePairing_homogeneous
    (hh : ∀ x v, (h.vertex x).map ((h.vertex x).map v)=(h.vertex x).map v)
    (i j : ℤ)
    (m : (bottImageSheaf cs basis l (bottAdjointSheaf cs basis l hl h)).forget.sections Set.univ)
    (n : (bottImageSheaf cs basis l h).forget.sections Set.univ)
    (hm : ∀ x, m.val x ∈
      ((bottImageSheaf cs basis l (bottAdjointSheaf cs basis l hl h)).vertex x).piece i)
    (hn : ∀ x, n.val x ∈ ((bottImageSheaf cs basis l h).vertex x).piece j) :
    bottAdjointImageEquivDual cs basis l hl h hh m n ∈ symmetricGrading basis (i+j-(l.length : ℤ)) := by
  rw [bottAdjointImageEquivDual_apply]
  exact bottDuality_homogeneous cs basis l
    (bottImageSectionWordEquiv_homogeneous cs basis l hl _
      (bottAdjointSheaf_vertex_idempotent cs basis l hl h hh) i m hm)
    (bottImageSectionWordEquiv_homogeneous cs basis l hl h hh j n hn)

end
end KLInvariance.TitsSpace
end


section
namespace KLInvariance.TitsSpace
open Module _root_.OAI.KLInvariance.Graded MomentGraph BruhatGraph
universe u us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  (l : List I) (hl : cs.IsReduced l)
  (h : GradedSheaf.Hom
    (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l))
    (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l)))
noncomputable section

 theorem bottEndOfSheaf_fixed_support (x : Interval cs 1 (cs.wordProd l))
    (hx : ∀ v, (h.vertex x).map v=v)
    (m : BottSamelsonModule cs l) (hm : m ∈ bottWeightSupported cs l x.val) :
    bottEndOfSheaf cs basis l hl h m=m := by
  apply bottEvaluation_injective cs l
  funext e
  by_cases he : bottWeight cs l e=x.val
  · have ho := bottEndOfSheaf_coordinates cs basis l hl h m x
    exact congrFun (congrArg Subtype.val (ho.trans (hx _))) ⟨e,he⟩
  · exact (bottEndOfSheaf_preserves_support cs basis l hl h x m hm e he).trans
      (hm e he).symm

 theorem bottAdjointSheaf_fixed_stalk (x : Interval cs 1 (cs.wordProd l))
    (hx : ∀ v, (h.vertex x).map v=v) (v : bottStalk cs l x.val) :
    ((bottAdjointSheaf cs basis l hl h).vertex x).map v=v := by
  obtain ⟨m,rfl⟩ := bottStalkProjection_surjective cs l x.val v
  rw [bottAdjointSheaf_vertex]
  have hz : bottStalkProjection cs l x.val
      (bottAdjoint cs l (bottEndOfSheaf cs basis l hl h) m-m)=0 := by
    apply (bott_projection_zero_iff_annihilates_support cs l x.val _).mpr
    intro z
    change bottSamelsonDuality cs l z.val
      (PerfectAdjoint.adjoint (bottSamelsonDuality cs l)
        (bottEndOfSheaf cs basis l hl h) m-m)=0
    rw [map_sub,PerfectAdjoint.symmetric_pairing _ (bottSamelson_symmetric cs l)]
    rw [bottEndOfSheaf_fixed_support cs basis l hl h x hx z.val z.property,sub_self]
  rw [map_sub] at hz
  exact sub_eq_zero.mp hz

 theorem bottAdjointSheaf_fixed_stalk_iff (x : Interval cs 1 (cs.wordProd l)) :
    (∀ v, ((bottAdjointSheaf cs basis l hl h).vertex x).map v=v) ↔
      (∀ v, (h.vertex x).map v=v) := by
  constructor
  · intro hx v
    have h' := bottAdjointSheaf_fixed_stalk cs basis l hl
      (bottAdjointSheaf cs basis l hl h) x hx v
    exact (bottAdjointSheaf_twice_vertex cs basis l hl h x v).symm.trans h'
  · exact fun hx v => bottAdjointSheaf_fixed_stalk cs basis l hl h x hx v

end
end KLInvariance.TitsSpace
end


section
namespace KLInvariance.TitsSpace
open Module _root_.OAI.KLInvariance.Graded MomentGraph BruhatGraph
universe u us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  (l : List I) (hl : cs.IsReduced l)
noncomputable section

 theorem bottEndOfSheaf_comp
    (h g : GradedSheaf.Hom
      (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l))
      (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l))) :
    bottEndOfSheaf cs basis l hl (h.comp g)=
      (bottEndOfSheaf cs basis l hl h).comp (bottEndOfSheaf cs basis l hl g) := by
  apply LinearMap.ext
  intro m
  apply bottVertexProjection_injective cs l hl
  funext x
  exact (bottEndOfSheaf_coordinates cs basis l hl (h.comp g) m x).trans
    ((congrArg (h.vertex x).map (bottEndOfSheaf_coordinates cs basis l hl g m x)).symm.trans
      (bottEndOfSheaf_coordinates cs basis l hl h (bottEndOfSheaf cs basis l hl g m) x).symm)

 theorem bottAdjointSheaf_comp
    (h g : GradedSheaf.Hom
      (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l))
      (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l))) :
    bottAdjointSheaf cs basis l hl (h.comp g)=
      (bottAdjointSheaf cs basis l hl g).comp (bottAdjointSheaf cs basis l hl h) := by
  apply GradedSheaf.Hom.eq_of_vertex
  · exact fun e => bottProjectionSheaf_lower_surjective cs l 1 (cs.wordProd l) e
  · intro x v
    have hs : Function.Surjective (bottStalkProjection cs l x.val) :=
      bottStalkProjection_surjective cs l x.val
    obtain ⟨m,rfl⟩ := hs v
    change ((bottAdjointSheaf cs basis l hl (h.comp g)).vertex x).map
      (bottStalkProjection cs l x.val m)=
        ((bottAdjointSheaf cs basis l hl g).vertex x).map
          (((bottAdjointSheaf cs basis l hl h).vertex x).map (bottStalkProjection cs l x.val m))
    simp only [bottAdjointSheaf_vertex]
    change bottStalkProjection cs l x.val
      (PerfectAdjoint.adjoint (bottSamelsonDuality cs l) (bottEndOfSheaf cs basis l hl (h.comp g)) m)=
      bottStalkProjection cs l x.val
        (PerfectAdjoint.adjoint (bottSamelsonDuality cs l) (bottEndOfSheaf cs basis l hl g)
          (PerfectAdjoint.adjoint (bottSamelsonDuality cs l) (bottEndOfSheaf cs basis l hl h) m))
    rw [bottEndOfSheaf_comp,PerfectAdjoint.adjoint_comp]
    rfl

 theorem bottAdjointSheaf_involutive : Function.Involutive (bottAdjointSheaf cs basis l hl) := by
  intro h
  apply GradedSheaf.Hom.eq_of_vertex
  · exact fun e => bottProjectionSheaf_lower_surjective cs l 1 (cs.wordProd l) e
  · exact bottAdjointSheaf_twice_vertex cs basis l hl h

 theorem bottAdjointSheaf_injective : Function.Injective (bottAdjointSheaf cs basis l hl) :=
  (bottAdjointSheaf_involutive cs basis l hl).injective

end
end KLInvariance.TitsSpace
end


section
namespace KLInvariance.TitsSpace
open Module _root_.OAI.KLInvariance.Graded MomentGraph BruhatGraph
universe u us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  (l : List I) (hl : cs.IsReduced l)
  (B : GradedSheaf (𝓐 := symmetricGrading basis) (graph cs 1 (cs.wordProd l)))
  (s : GradedSheaf.SplitIn B (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l)))
noncomputable section

 def bottSplitAdjointSheaf : GradedSheaf (𝓐 := symmetricGrading basis)
    (graph cs 1 (cs.wordProd l)) :=
  bottImageSheaf cs basis l (bottAdjointSheaf cs basis l hl s.projector)

 def bottSplitAdjointEquivDual :
    (bottSplitAdjointSheaf cs basis l hl B s).forget.sections Set.univ ≃ₗ[
      SymmetricCoefficient (M := M)]
      Dual (SymmetricCoefficient (M := M)) (B.forget.sections Set.univ) := by
  letI := symmetricCoefficientNoetherian basis
  exact (bottAdjointImageEquivDual cs basis l hl s.projector s.projector_vertex).trans
    (s.imageSectionEquiv Set.univ).symm.dualMap

 theorem bottSplitAdjointPairing_homogeneous
    (i j : ℤ)
    (m : (bottSplitAdjointSheaf cs basis l hl B s).forget.sections Set.univ)
    (n : B.forget.sections Set.univ)
    (hm : ∀ x, m.val x ∈ ((bottSplitAdjointSheaf cs basis l hl B s).vertex x).piece i)
    (hn : ∀ x, n.val x ∈ (B.vertex x).piece j) :
    bottSplitAdjointEquivDual cs basis l hl B s m n ∈
      symmetricGrading basis (i+j-(l.length : ℤ)) := by
  let := symmetricCoefficientNoetherian basis
  exact bottAdjointImagePairing_homogeneous cs basis l hl s.projector s.projector_vertex i j m
    ((s.imageSectionEquiv Set.univ).symm n) hm
    (s.imageSectionEquiv_symm_homogeneous Set.univ j n hn)

end
end KLInvariance.TitsSpace
end


section
namespace KLInvariance.TitsSpace
open Module _root_.OAI.KLInvariance.Graded MomentGraph BruhatGraph
universe u us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  (l : List I) (hl : cs.IsReduced l)
noncomputable section

 theorem bottEndOfSheaf_zero :
    bottEndOfSheaf cs basis l hl GradedSheaf.Hom.zero=0 := by
  apply LinearMap.ext
  intro m
  apply bottVertexProjection_injective cs l hl
  funext x
  change bottStalkProjection cs l x.val _=bottStalkProjection cs l x.val 0
  rw [map_zero]
  exact bottEndOfSheaf_coordinates cs basis l hl GradedSheaf.Hom.zero m x

 theorem bottAdjointSheaf_zero :
    bottAdjointSheaf cs basis l hl GradedSheaf.Hom.zero=GradedSheaf.Hom.zero := by
  apply GradedSheaf.Hom.eq_of_vertex
  · exact fun e => bottProjectionSheaf_lower_surjective cs l 1 (cs.wordProd l) e
  · intro x v
    have hs : Function.Surjective (bottStalkProjection cs l x.val) :=
      bottStalkProjection_surjective cs l x.val
    obtain ⟨m,rfl⟩ := hs v
    change ((bottAdjointSheaf cs basis l hl GradedSheaf.Hom.zero).vertex x).map
      (bottStalkProjection cs l x.val m)=0
    rw [bottAdjointSheaf_vertex,bottEndOfSheaf_zero]
    change bottStalkProjection cs l x.val
      (PerfectAdjoint.adjoint (bottSamelsonDuality cs l) 0 m)=0
    rw [PerfectAdjoint.adjoint_zero]
    exact map_zero _

 theorem bottAdjointSheaf_primitive
    (p : GradedSheaf.Hom
      (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l))
      (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l)))
    (hp : p.PrimitiveProjector) :
    (bottAdjointSheaf cs basis l hl p).PrimitiveProjector :=
  GradedSheaf.Hom.primitive_of_antiInvolution _
    (bottAdjointSheaf_involutive cs basis l hl)
    (bottAdjointSheaf_comp cs basis l hl)
    (bottAdjointSheaf_zero cs basis l hl) p hp

 theorem bottAdjointSheaf_primitive_iff
    (p : GradedSheaf.Hom
      (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l))
      (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l))) :
    (bottAdjointSheaf cs basis l hl p).PrimitiveProjector ↔ p.PrimitiveProjector := by
  constructor
  · intro hp
    have hh := bottAdjointSheaf_primitive cs basis l hl _ hp
    rw [bottAdjointSheaf_involutive cs basis l hl p] at hh
    exact hh
  · exact bottAdjointSheaf_primitive cs basis l hl p

end
end KLInvariance.TitsSpace
end


section
namespace KLInvariance.TitsSpace
open Module _root_.OAI.KLInvariance.Graded MomentGraph BruhatGraph
universe u us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  (l : List I) (hl : cs.IsReduced l)
  (α : Edge cs 1 (cs.wordProd l) → SymmetricCoefficient (M := M))
  (B : BoundarySheaf (symmetricGrading_negative basis)
    (graph cs 1 (cs.wordProd l)) α
    ⟨cs.wordProd l,one_bruhat cs _,bruhat_refl cs _⟩)
  (s : GradedSheaf.SplitIn B.sheaf (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l)))
noncomputable section

 theorem bottBoundarySplitAdjoint_primitive :
    (GradedSheaf.Hom.id (bottSplitAdjointSheaf cs basis l hl B.sheaf s)).PrimitiveProjector := by
  let := symmetricCoefficientNoetherian basis
  let := interval_finite cs 1 (cs.wordProd l)
  exact GradedSheaf.Hom.primitive_image _ (bottAdjointSheaf_primitive cs basis l hl
    s.projector (B.split_projector_primitive s))

end
end KLInvariance.TitsSpace
end

end OAI
