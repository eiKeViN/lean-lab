module
public import Mathlib
public import ForMathlib.GroupTheory.Coxeter.Roots.Order
public import ForMathlib.LinearAlgebra.SymmetricAlgebra.RootIdeal

public section

/-! Semantic home: ForMathlib.GroupTheory.Coxeter.Roots.PlaneLength. Source spans: ReflectionSchedules:8, ReflectionSchedules:10, ReflectionSchedules:13.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.TitsSpace
open Module
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
noncomputable section
local instance _root_.OAI.KLInvariance.TitsSpace.instDecidable_oAI_4 (p : Prop) : Decidable p := Classical.propDecidable p

/-- The actual finite count of ambient inversions belonging to a root plane.
No Coxeter presentation of the plane subgroup is assumed here. -/
@[expose] def planeLength (P : Submodule ℝ (I → ℝ)) (w : W) : ℤ :=
  (inversionVector (M := M) (cs := cs) w).sum (fun a n => if a.val ∈ P then n else 0)

theorem rootPlane_grouped_erase (a b : PositiveRoot M cs) (hab : a ≠ b)
    (f : PositiveRoot M cs →₀ ℤ) :
    Finsupp.mapDomain (rootPlane a) (f.erase a) (rootPlane a b) =
      f.sum (fun c n => if c.val ∈ rootPlane a b then n else 0) - f a := by
  classical
  have haP : a.val ∈ rootPlane a b := Submodule.subset_span (Set.mem_insert _ _)
  have heq : Finsupp.mapDomain (rootPlane a) (f.erase a) (rootPlane a b) =
      (f.erase a).sum (fun c n => if c.val ∈ rootPlane a b then n else 0) := by
    rw [Finsupp.mapDomain,Finsupp.sum_apply]
    apply Finset.sum_congr rfl
    intro c hc
    have hca : c ≠ a := by
      intro h
      subst c
      simp only [Finsupp.mem_support_iff,Finsupp.erase_same,ne_eq,not_true_eq_false] at hc
    change (Finsupp.single (rootPlane a c) ((f.erase a) c)) (rootPlane a b) =
      (if c.val ∈ rootPlane a b then (f.erase a) c else 0)
    rw [Finsupp.single_apply]
    by_cases hm : c.val ∈ rootPlane a b
    · rw [ite_eq_left ((rootPlane_eq_iff a b c hab).mpr ⟨hca,hm⟩),ite_eq_left hm]
    · rw [ite_eq_right (fun heq => hm ((rootPlane_eq_iff a b c hab).mp heq).2),ite_eq_right hm]
  rw [heq,Finsupp.erase_eq_sub_single,
    Finsupp.sum_sub_index (fun c m n => by split_ifs <;> simp),
    Finsupp.sum_single_index (by simp),ite_eq_left haP]

theorem planeDefect_eq_relative_difference (x : W) (a b : PositiveRoot M cs)
    (hab : a ≠ b) (hx : ¬ rootInverted x a) :
    planeDefect x (rootRef a*x) a (rootPlane a b) =
      planeLength (M := M) (cs := cs) (rootPlane a b) (rootRef a*x) - planeLength (M := M) (cs := cs) (rootPlane a b) x - 1 := by
  rw [planeDefect,rootPlane_grouped_erase a b hab,rootChange_distinguished x a hx,
    rootChange,Finsupp.sum_sub_index (fun c m n => by split_ifs <;> simp)]
  rfl


theorem planeWeight_relative_degree (x : W) (a b : PositiveRoot M cs)
    (hab : a ≠ b) (hx : ¬ rootInverted x a) :
    2 * planeWeight x a (rootPlane a b) =
      planeLength (M := M) (cs := cs) (rootPlane a b) (rootRef a*x) - planeLength (M := M) (cs := cs) (rootPlane a b) x - 1 := by
  have h := planeDefect_eq_relative_difference x a b hab hx
  rw [planeDefect_eq_double_weight x a hx,Finsupp.add_apply] at h
  linarith

end
end KLInvariance.TitsSpace
end


section
namespace KLInvariance.TitsSpace
open Module EdgeAlgebra
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
noncomputable section
local instance _root_.OAI.KLInvariance.TitsSpace.instDecidable_oAI_5 (p : Prop) : Decidable p := Classical.propDecidable p

theorem planeWeight_support_root (x : W) (a : PositiveRoot M cs)
    (P : Submodule ℝ (I → ℝ)) (hP : P ∈ (planeWeight x a).support) :
    ∃ b : PositiveRoot M cs, b ≠ a ∧ rootPlane a b = P := by
  obtain ⟨b,hb,hbP⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hP)
  refine ⟨b,?_,hbP⟩
  have hb' := Finsupp.mem_support_iff.mp hb
  change halfVector x a b ≠ 0 at hb'
  simp only [halfVector,rootIndicator_apply] at hb'
  have hh : halfRoot x a b := by
    by_contra hn
    exact hb' (ite_eq_right hn)
  exact hh.1.1

@[expose] def planeRoot (x : W) (a : PositiveRoot M cs)
    (P : (planeWeight x a).support) : PositiveRoot M cs :=
  (planeWeight_support_root x a P.val P.property).choose

theorem planeRoot_ne (x : W) (a : PositiveRoot M cs)
    (P : (planeWeight x a).support) : planeRoot x a P ≠ a :=
  (planeWeight_support_root x a P.val P.property).choose_spec.1

theorem planeRoot_plane (x : W) (a : PositiveRoot M cs)
    (P : (planeWeight x a).support) : rootPlane a (planeRoot x a P) = P.val :=
  (planeWeight_support_root x a P.val P.property).choose_spec.2

theorem embed_not_rootLine (a b : PositiveRoot M cs) (hab : b ≠ a) :
    embed M b.val ∉ rootLine (k := ℝ) (embed M a.val) := by
  intro h
  obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp h
  have hli := (linearIndependent_fin2.mp (positiveRoots_independent b a hab)).2 c
  change c • a.val ≠ b.val at hli
  apply hli
  have hh := congrArg Prod.fst hc
  simpa only [embed,Prod.smul_fst] using hh

abbrev EdgeCoefficient (a : PositiveRoot M cs) :=
  SymmetricAlgebra ℝ (Extended M) ⧸ rootIdeal (k := ℝ) (embed M a.val)

@[expose] def reducedPlaneRoot (x : W) (a : PositiveRoot M cs)
    (P : (planeWeight x a).support) : EdgeCoefficient a :=
  Ideal.Quotient.mk (rootIdeal (k := ℝ) (embed M a.val))
    (SymmetricAlgebra.ι ℝ (Extended M) (embed M (planeRoot x a P).val))

theorem reducedPlaneRoot_ne_zero (x : W) (a : PositiveRoot M cs)
    (P : (planeWeight x a).support) : reducedPlaneRoot x a P ≠ 0 :=
  reducedRoot_ne_zero _ _ (embed_not_rootLine a _ (planeRoot_ne x a P))

/-- The manuscript's actual product of reduced root forms, with its proved
nonnegative integral plane exponents. No abstract invariant is substituted. -/
@[expose] def edgeFactor (x : W) (a : PositiveRoot M cs) : EdgeCoefficient a :=
  ∏ P : (planeWeight x a).support, reducedPlaneRoot x a P ^ (planeWeight x a P.val).toNat

@[expose] def edgeFactorDegree (x : W) (a : PositiveRoot M cs) : ℕ :=
  ∑ P : (planeWeight x a).support, (planeWeight x a P.val).toNat

@[expose] def edgePolynomial (a : PositiveRoot M cs) : EdgeCoefficient a ≃ₐ[ℝ]
    MvPolynomial (Fin (Module.finrank ℝ (Extended M ⧸ rootLine (k := ℝ) (embed M a.val)))) ℝ :=
  rootQuotientPolynomial (embed M a.val) (Module.finBasis ℝ _)

theorem edgeFactor_nonzero (x : W) (a : PositiveRoot M cs) : edgeFactor x a ≠ 0 := by
  intro h
  have hp := congrArg (edgePolynomial a) h
  simp only [edgeFactor,map_prod,map_pow,map_zero] at hp
  apply (Finset.prod_ne_zero_iff.mpr ?_) hp
  intro P _
  apply pow_ne_zero
  intro h0
  apply reducedPlaneRoot_ne_zero x a P
  apply (edgePolynomial a).injective
  simpa only [map_zero] using h0

theorem edgeFactor_homogeneous (x : W) (a : PositiveRoot M cs) :
    (edgePolynomial a (edgeFactor x a)).IsHomogeneous (edgeFactorDegree x a) := by
  simp only [edgeFactor,map_prod,map_pow,edgeFactorDegree]
  apply MvPolynomial.IsHomogeneous.prod
  intro P _
  have h : (edgePolynomial a (reducedPlaneRoot x a P)).IsHomogeneous 1 :=
    reducedRoot_homogeneous _ _ _
  simpa only [one_mul] using h.pow (planeWeight x a P.val).toNat

theorem edgeFactor_totalDegree (x : W) (a : PositiveRoot M cs) :
    (edgePolynomial a (edgeFactor x a)).totalDegree = edgeFactorDegree x a :=
  (edgeFactor_homogeneous x a).totalDegree
    (by
      intro h0
      apply edgeFactor_nonzero x a
      apply (edgePolynomial a).injective
      simpa only [map_zero] using h0)


theorem edgeFactorDegree_cast (x : W) (a : PositiveRoot M cs) :
    (edgeFactorDegree x a : ℤ) = (planeWeight x a).sum (fun _ n => n) := by
  classical
  simp only [edgeFactorDegree,Nat.cast_sum]
  simp_rw [Int.toNat_of_nonneg (planeWeight_nonneg x a _)]
  exact Finset.sum_coe_sort (planeWeight x a).support (fun P => planeWeight x a P)


theorem edgeFactor_degree_formula (x : W) (a : PositiveRoot M cs)
    (hx : ¬ rootInverted x a) :
    2 * ((edgePolynomial a (edgeFactor x a)).totalDegree : ℤ) =
      (cs.length (rootRef a*x) : ℤ) - cs.length x - 1 := by
  rw [edgeFactor_totalDegree,edgeFactorDegree_cast]
  exact sum_planeWeight x a hx

end
end KLInvariance.TitsSpace
end


section
namespace KLInvariance.TitsSpace
open Module EdgeAlgebra
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
noncomputable section
local instance _root_.OAI.KLInvariance.TitsSpace.instDecidable_oAI_6 (p : Prop) : Decidable p := Classical.propDecidable p

theorem embed_mem_span_pair (a b c : I → ℝ) :
    embed M c ∈ Submodule.span ℝ {embed M a,embed M b} ↔
      c ∈ Submodule.span ℝ {a,b} := by
  constructor
  · intro h
    obtain ⟨r,s,h⟩ := Submodule.mem_span_pair.mp h
    refine Submodule.mem_span_pair.mpr ⟨r,s,?_⟩
    exact congrArg Prod.fst h
  · intro h
    obtain ⟨r,s,h⟩ := Submodule.mem_span_pair.mp h
    refine Submodule.mem_span_pair.mpr ⟨r,s,?_⟩
    apply Prod.ext
    · exact h
    · simp only [embed,Prod.snd_add,Prod.smul_snd,smul_zero,add_zero]

theorem reducedPlaneRoot_prime (x : W) (a : PositiveRoot M cs)
    (P : (planeWeight x a).support) : Prime (reducedPlaneRoot x a P) :=
  reducedRoot_prime _ _ (embed_not_rootLine a _ (planeRoot_ne x a P))


theorem reducedPlaneRoot_dvd_iff (x : W) (a : PositiveRoot M cs)
    (P Q : (planeWeight x a).support) :
    reducedPlaneRoot x a P ∣ reducedPlaneRoot x a Q ↔ P = Q := by
  rw [reducedPlaneRoot,reducedPlaneRoot,reducedRoot_dvd_iff,embed_mem_span_pair]
  change (planeRoot x a Q).val ∈ rootPlane a (planeRoot x a P) ↔ P = Q
  have h := rootPlane_eq_iff a (planeRoot x a P) (planeRoot x a Q)
    (planeRoot_ne x a P).symm
  rw [planeRoot_plane,planeRoot_plane] at h
  rw [planeRoot_plane]
  constructor
  · intro hm
    apply Subtype.ext
    exact (h.mpr ⟨planeRoot_ne x a Q,hm⟩).symm
  · intro heq
    exact (h.mp (congrArg Subtype.val heq).symm).2

end
end KLInvariance.TitsSpace
end

end OAI
