import Mathlib

/-! Semantic home: ForMathlib.LinearAlgebra.SymmetricAlgebra.RootIdeal. Source spans: ReflectionSchedules:9, ReflectionSchedules:11, ReflectionSchedules:12.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.EdgeAlgebra
open Module
universe u v
variable {k : Type u} [Field k] {V : Type v} [AddCommGroup V] [Module k V]
noncomputable section

theorem symmetric_ι_injective : Function.Injective (SymmetricAlgebra.ι k V) := by
  apply LinearMap.ker_eq_bot.mp
  apply eq_bot_iff.mpr
  intro v hv
  change v = 0
  by_contra hn
  obtain ⟨f,hf⟩ := Module.Projective.exists_dual_ne_zero k hn
  have h := congrArg (SymmetricAlgebra.lift f) (LinearMap.mem_ker.mp hv)
  rw [SymmetricAlgebra.lift_ι_apply,map_zero] at h
  exact hf h


def rootIdeal (a : V) : Ideal (SymmetricAlgebra k V) :=
  Ideal.span {SymmetricAlgebra.ι k V a}

def rootLine (a : V) : Submodule k V := Submodule.span k {a}

def symQuotientMap (a : V) : SymmetricAlgebra k V →ₐ[k] SymmetricAlgebra k (V ⧸ rootLine (k := k) a) :=
  SymmetricAlgebra.lift ((SymmetricAlgebra.ι k (V ⧸ rootLine (k := k) a)).comp (rootLine (k := k) a).mkQ)

@[simp] theorem symQuotientMap_ι (a v : V) :
    symQuotientMap a (SymmetricAlgebra.ι k V v) =
      SymmetricAlgebra.ι k (V ⧸ rootLine (k := k) a) ((rootLine (k := k) a).mkQ v) :=
  SymmetricAlgebra.lift_ι_apply _ _

theorem rootIdeal_le_ker (a : V) : rootIdeal (k := k) a ≤ RingHom.ker (symQuotientMap a) := by
  apply Ideal.span_le.mpr
  intro z hz
  have hz' := Set.mem_singleton_iff.mp hz
  subst z
  change symQuotientMap a (SymmetricAlgebra.ι k V a) = 0
  rw [symQuotientMap_ι]
  have ha : (rootLine (k := k) a).mkQ a = 0 := by
    exact (Submodule.Quotient.mk_eq_zero (rootLine (k := k) a)).mpr (Submodule.subset_span (Set.mem_singleton a))
  rw [ha,map_zero]

def quotientForward (a : V) : (SymmetricAlgebra k V ⧸ rootIdeal (k := k) a) →ₐ[k]
    SymmetricAlgebra k (V ⧸ rootLine (k := k) a) :=
  Ideal.Quotient.liftₐ _ (symQuotientMap a) (fun _ hz => rootIdeal_le_ker a hz)

def quotientRootMap (a : V) : V ⧸ rootLine (k := k) a →ₗ[k]
    (SymmetricAlgebra k V ⧸ rootIdeal (k := k) a) :=
  (rootLine (k := k) a).liftQ ((Ideal.Quotient.mkₐ k (rootIdeal (k := k) a)).toLinearMap.comp (SymmetricAlgebra.ι k V)) (by
    apply Submodule.span_le.mpr
    intro v hv
    have hv' := Set.mem_singleton_iff.mp hv
    subst v
    apply LinearMap.mem_ker.mpr
    change Ideal.Quotient.mk (rootIdeal (k := k) a) (SymmetricAlgebra.ι k V a) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _)))

def quotientBackward (a : V) : SymmetricAlgebra k (V ⧸ rootLine (k := k) a) →ₐ[k]
    (SymmetricAlgebra k V ⧸ rootIdeal (k := k) a) := SymmetricAlgebra.lift (quotientRootMap a)

@[simp] theorem quotientForward_mk (a : V) (z : SymmetricAlgebra k V) :
    quotientForward a (Ideal.Quotient.mk (rootIdeal (k := k) a) z) = symQuotientMap a z := rfl

@[simp] theorem quotientBackward_ι_mk (a v : V) :
    quotientBackward a (SymmetricAlgebra.ι k (V ⧸ rootLine (k := k) a) ((rootLine (k := k) a).mkQ v)) =
      Ideal.Quotient.mk (rootIdeal (k := k) a) (SymmetricAlgebra.ι k V v) := by
  rw [quotientBackward,SymmetricAlgebra.lift_ι_apply]
  rfl

/-- Exact coefficient-ring identification used for the manuscript's C=A/(alpha).
This is an isomorphism of the actual quotient, not a replacement invariant. -/
def rootQuotientEquiv (a : V) : (SymmetricAlgebra k V ⧸ rootIdeal (k := k) a) ≃ₐ[k]
    SymmetricAlgebra k (V ⧸ rootLine (k := k) a) :=
  AlgEquiv.ofAlgHom (quotientForward a) (quotientBackward a)
    (by
      apply SymmetricAlgebra.algHom_ext
      apply LinearMap.ext
      intro v
      obtain ⟨v,rfl⟩ := (rootLine (k := k) a).mkQ_surjective v
      change quotientForward a (quotientBackward a (SymmetricAlgebra.ι k _ ((rootLine (k := k) a).mkQ v))) =
        SymmetricAlgebra.ι k _ ((rootLine (k := k) a).mkQ v)
      rw [quotientBackward_ι_mk,quotientForward_mk,symQuotientMap_ι])
    (by
      apply Ideal.Quotient.algHom_ext
      apply SymmetricAlgebra.algHom_ext
      apply LinearMap.ext
      intro v
      change quotientBackward a (quotientForward a (Ideal.Quotient.mk (rootIdeal (k := k) a)
        (SymmetricAlgebra.ι k V v))) = Ideal.Quotient.mk (rootIdeal (k := k) a) (SymmetricAlgebra.ι k V v)
      rw [quotientForward_mk,symQuotientMap_ι,quotientBackward_ι_mk])


@[simp] theorem rootQuotientEquiv_mk_ι (a v : V) :
    rootQuotientEquiv a (Ideal.Quotient.mk (rootIdeal (k := k) a) (SymmetricAlgebra.ι k V v)) =
      SymmetricAlgebra.ι k (V ⧸ rootLine (k := k) a) ((rootLine (k := k) a).mkQ v) := by
  exact symQuotientMap_ι a v

theorem reducedRoot_ne_zero (a v : V) (hv : v ∉ rootLine (k := k) a) :
    Ideal.Quotient.mk (rootIdeal (k := k) a) (SymmetricAlgebra.ι k V v) ≠ 0 := by
  intro h
  apply hv
  apply (Submodule.Quotient.mk_eq_zero (rootLine (k := k) a)).mp
  change (rootLine (k := k) a).mkQ v = 0
  apply symmetric_ι_injective (k := k)
  have hh := congrArg (rootQuotientEquiv a) h
  simpa only [rootQuotientEquiv_mk_ι,map_zero] using hh

variable {κ : Type*}
theorem linear_homogeneous [Fintype κ] (b : Basis κ k V) (v : V) :
    (SymmetricAlgebra.equivMvPolynomial b (SymmetricAlgebra.ι k V v)).IsHomogeneous 1 := by
  classical
  conv_lhs => rw [← b.sum_repr v]
  simp only [map_sum,map_smul,SymmetricAlgebra.equivMvPolynomial_ι_apply]
  apply MvPolynomial.IsHomogeneous.sum
  intro i _
  simpa only [Algebra.smul_def,MvPolynomial.algebraMap_eq] using (MvPolynomial.isHomogeneous_X k i).C_mul (b.repr v i)

/-- Polynomial coordinates on the actual symmetric-algebra quotient. -/
def rootQuotientPolynomial (a : V) (b : Basis κ k (V ⧸ rootLine (k := k) a)) :
    (SymmetricAlgebra k V ⧸ rootIdeal (k := k) a) ≃ₐ[k] MvPolynomial κ k :=
  (rootQuotientEquiv a).trans (SymmetricAlgebra.equivMvPolynomial b)

theorem reducedRoot_homogeneous [Fintype κ] (a v : V)
    (b : Basis κ k (V ⧸ rootLine (k := k) a)) :
    (rootQuotientPolynomial a b
      (Ideal.Quotient.mk (rootIdeal (k := k) a) (SymmetricAlgebra.ι k V v))).IsHomogeneous 1 := by
  change (SymmetricAlgebra.equivMvPolynomial b
    (rootQuotientEquiv a (Ideal.Quotient.mk (rootIdeal (k := k) a) (SymmetricAlgebra.ι k V v)))).IsHomogeneous 1
  rw [rootQuotientEquiv_mk_ι]
  exact linear_homogeneous b _

end
end KLInvariance.EdgeAlgebra
end


section
namespace KLInvariance.EdgeAlgebra
open Module
universe u v
variable {k : Type u} [Field k] {V : Type v} [AddCommGroup V] [Module k V]
noncomputable section

theorem rootIdeal_eq_ker (a : V) : rootIdeal (k := k) a = RingHom.ker (symQuotientMap (k := k) a) := by
  apply le_antisymm (rootIdeal_le_ker a)
  intro z hz
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  apply (rootQuotientEquiv (k := k) a).injective
  change quotientForward a (Ideal.Quotient.mk (rootIdeal (k := k) a) z) = _
  rw [quotientForward_mk,map_zero]
  exact hz

theorem rootIdeal_isPrime (a : V) : (rootIdeal (k := k) a).IsPrime := by
  rw [rootIdeal_eq_ker]
  exact RingHom.ker_isPrime _

theorem symmetric_ι_prime (a : V) (ha : a ≠ 0) : Prime (SymmetricAlgebra.ι k V a) := by
  have hn : SymmetricAlgebra.ι k V a ≠ 0 := by
    intro h
    apply ha
    apply symmetric_ι_injective (k := k)
    simpa only [map_zero] using h
  exact (Ideal.span_singleton_prime hn).mp (rootIdeal_isPrime a)

theorem reducedRoot_prime (a v : V) (hv : v ∉ rootLine (k := k) a) :
    Prime (Ideal.Quotient.mk (rootIdeal (k := k) a) (SymmetricAlgebra.ι k V v)) := by
  apply (MulEquiv.prime_iff (rootQuotientEquiv (k := k) a)).mp
  rw [rootQuotientEquiv_mk_ι]
  apply symmetric_ι_prime
  intro h
  exact hv ((Submodule.Quotient.mk_eq_zero (rootLine (k := k) a)).mp h)

end
end KLInvariance.EdgeAlgebra
end


section
namespace KLInvariance.EdgeAlgebra
open Module
universe u v
variable {k : Type u} [Field k] {V : Type v} [AddCommGroup V] [Module k V]
noncomputable section

theorem symmetric_ι_dvd_iff (a v : V) :
    SymmetricAlgebra.ι k V a ∣ SymmetricAlgebra.ι k V v ↔ v ∈ rootLine (k := k) a := by
  rw [← Ideal.mem_span_singleton]
  change SymmetricAlgebra.ι k V v ∈ rootIdeal (k := k) a ↔ _
  rw [rootIdeal_eq_ker]
  change symQuotientMap a (SymmetricAlgebra.ι k V v) = 0 ↔ _
  rw [symQuotientMap_ι]
  constructor
  · intro h
    apply (Submodule.Quotient.mk_eq_zero (rootLine (k := k) a)).mp
    change (rootLine (k := k) a).mkQ v = 0
    apply symmetric_ι_injective (k := k)
    simpa only [map_zero] using h
  · intro h
    have h0 : (rootLine (k := k) a).mkQ v = 0 :=
      (Submodule.Quotient.mk_eq_zero (rootLine (k := k) a)).mpr h
    rw [h0,map_zero]

theorem mkQ_mem_span_iff (a b v : V) :
    (rootLine (k := k) a).mkQ v ∈
      Submodule.span k { (rootLine (k := k) a).mkQ b } ↔
      v ∈ Submodule.span k {a,b} := by
  have ha : (rootLine (k := k) a).mkQ a = 0 :=
    (Submodule.Quotient.mk_eq_zero (rootLine (k := k) a)).mpr
      (Submodule.subset_span (Set.mem_singleton _))
  constructor
  · intro h
    obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp h
    have h0 : (rootLine (k := k) a).mkQ (v-c • b) = 0 := by
      rw [map_sub,map_smul,← hc,sub_self]
    have hm := (Submodule.Quotient.mk_eq_zero (rootLine (k := k) a)).mp h0
    obtain ⟨d,hd⟩ := Submodule.mem_span_singleton.mp hm
    apply Submodule.mem_span_pair.mpr
    exact ⟨d,c,by rw [hd]; module⟩
  · intro h
    obtain ⟨d,c,hv⟩ := Submodule.mem_span_pair.mp h
    apply Submodule.mem_span_singleton.mpr
    refine ⟨c,?_⟩
    rw [← hv,map_add,map_smul,map_smul,ha,smul_zero,zero_add]

theorem reducedRoot_dvd_iff (a b v : V) :
    Ideal.Quotient.mk (rootIdeal (k := k) a) (SymmetricAlgebra.ι k V b) ∣
      Ideal.Quotient.mk (rootIdeal (k := k) a) (SymmetricAlgebra.ι k V v) ↔
        v ∈ Submodule.span k {a,b} := by
  let e := rootQuotientEquiv (k := k) a
  have hd (z w : SymmetricAlgebra k V ⧸ rootIdeal (k := k) a) :
      z ∣ w ↔ e z ∣ e w := by
    constructor
    · exact map_dvd e
    · intro h
      simpa only [AlgEquiv.symm_apply_apply] using map_dvd e.symm h
  rw [hd]
  change rootQuotientEquiv a _ ∣ rootQuotientEquiv a _ ↔ _
  rw [rootQuotientEquiv_mk_ι,rootQuotientEquiv_mk_ι,symmetric_ι_dvd_iff]
  exact mkQ_mem_span_iff a b v

end
end KLInvariance.EdgeAlgebra
end

end OAI
