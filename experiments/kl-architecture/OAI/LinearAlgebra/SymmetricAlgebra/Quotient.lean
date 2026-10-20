import Mathlib

/-! Semantic home: OAI.LinearAlgebra.SymmetricAlgebra.Quotient. Source spans: PlaneLocalization:1.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.SymmetricPlaneIdeal
universe uk uv
variable {k : Type uk} [Field k] {V : Type uv} [AddCommGroup V] [Module k V]
noncomputable section

 def ideal (P : Submodule k V) : Ideal (SymmetricAlgebra k V) :=
  Ideal.span ((SymmetricAlgebra.ι k V) '' (P : Set V))

 def quotientMap (P : Submodule k V) :
    SymmetricAlgebra k V →ₐ[k] SymmetricAlgebra k (V ⧸ P) :=
  SymmetricAlgebra.lift ((SymmetricAlgebra.ι k (V ⧸ P)).comp P.mkQ)

@[simp] theorem quotientMap_ι (P : Submodule k V) (v : V) :
    quotientMap P (SymmetricAlgebra.ι k V v) = SymmetricAlgebra.ι k (V ⧸ P) (P.mkQ v) :=
  SymmetricAlgebra.lift_ι_apply _ _

 theorem ideal_le_ker (P : Submodule k V) : ideal P ≤ RingHom.ker (quotientMap P) := by
  apply Ideal.span_le.mpr
  rintro _ ⟨v,hv,rfl⟩
  change quotientMap P (SymmetricAlgebra.ι k V v) = 0
  rw [quotientMap_ι,show P.mkQ v = 0 from (Submodule.Quotient.mk_eq_zero P).mpr hv,map_zero]

 def forward (P : Submodule k V) : (SymmetricAlgebra k V ⧸ ideal P) →ₐ[k]
    SymmetricAlgebra k (V ⧸ P) :=
  Ideal.Quotient.liftₐ _ (quotientMap P) (fun _ hz => ideal_le_ker P hz)

 def linearQuotient (P : Submodule k V) : V ⧸ P →ₗ[k]
    (SymmetricAlgebra k V ⧸ ideal P) :=
  P.liftQ ((Ideal.Quotient.mkₐ k (ideal P)).toLinearMap.comp (SymmetricAlgebra.ι k V)) (by
    intro v hv
    apply LinearMap.mem_ker.mpr
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨v,hv,rfl⟩))

 def backward (P : Submodule k V) : SymmetricAlgebra k (V ⧸ P) →ₐ[k]
    (SymmetricAlgebra k V ⧸ ideal P) := SymmetricAlgebra.lift (linearQuotient P)

@[simp] theorem forward_mk (P : Submodule k V) (z : SymmetricAlgebra k V) :
    forward P (Ideal.Quotient.mk (ideal P) z) = quotientMap P z := rfl

@[simp] theorem backward_ι_mk (P : Submodule k V) (v : V) :
    backward P (SymmetricAlgebra.ι k (V ⧸ P) (P.mkQ v)) =
      Ideal.Quotient.mk (ideal P) (SymmetricAlgebra.ι k V v) := by
  rw [backward,SymmetricAlgebra.lift_ι_apply]
  rfl

 def quotientEquiv (P : Submodule k V) : (SymmetricAlgebra k V ⧸ ideal P) ≃ₐ[k]
    SymmetricAlgebra k (V ⧸ P) :=
  AlgEquiv.ofAlgHom (forward P) (backward P)
    (by
      apply SymmetricAlgebra.algHom_ext
      apply LinearMap.ext
      intro v
      obtain ⟨v,rfl⟩ := P.mkQ_surjective v
      change forward P (backward P (SymmetricAlgebra.ι k _ (P.mkQ v))) = _
      rw [backward_ι_mk,forward_mk,quotientMap_ι]
      rfl)
    (by
      apply Ideal.Quotient.algHom_ext
      apply SymmetricAlgebra.algHom_ext
      apply LinearMap.ext
      intro v
      change backward P (forward P (Ideal.Quotient.mk (ideal P) (SymmetricAlgebra.ι k V v))) = _
      rw [forward_mk,quotientMap_ι,backward_ι_mk]
      rfl)

@[simp] theorem quotientEquiv_mk_ι (P : Submodule k V) (v : V) :
    quotientEquiv P (Ideal.Quotient.mk (ideal P) (SymmetricAlgebra.ι k V v)) =
      SymmetricAlgebra.ι k (V ⧸ P) (P.mkQ v) := quotientMap_ι P v

 theorem ι_mem_iff (P : Submodule k V) (v : V) :
    SymmetricAlgebra.ι k V v ∈ ideal P ↔ v ∈ P := by
  constructor
  · intro hv
    have hh := ideal_le_ker P hv
    change quotientMap P (SymmetricAlgebra.ι k V v) = 0 at hh
    rw [quotientMap_ι] at hh
    apply (Submodule.Quotient.mk_eq_zero P).mp
    have he : SymmetricAlgebra.ι k (V ⧸ P) (P.mkQ v) =
        SymmetricAlgebra.ι k (V ⧸ P) 0 := by simpa only [map_zero] using hh
    by_contra hn
    obtain ⟨f,hf⟩ := Module.Projective.exists_dual_ne_zero k hn
    have h := congrArg (SymmetricAlgebra.lift f) he
    rw [SymmetricAlgebra.lift_ι_apply,SymmetricAlgebra.lift_ι_apply,map_zero] at h
    exact hf h
  · intro hv
    exact Ideal.subset_span ⟨v,hv,rfl⟩

 theorem ideal_eq_ker (P : Submodule k V) : ideal P = RingHom.ker (quotientMap P) := by
  apply le_antisymm (ideal_le_ker P)
  intro z hz
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  apply (quotientEquiv P).injective
  change quotientMap P z = quotientEquiv P 0
  rw [map_zero]
  exact hz

 instance ideal_isPrime (P : Submodule k V) : (ideal P).IsPrime := by
  rw [ideal_eq_ker]
  exact RingHom.ker_isPrime (quotientMap P)

 theorem ideal_span_eq (s : Set V) :
    ideal (Submodule.span k s) = Ideal.span ((SymmetricAlgebra.ι k V) '' s) := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨v,hv,rfl⟩
    induction hv using Submodule.span_induction with
    | mem x hx => exact Ideal.subset_span ⟨x,hx,rfl⟩
    | zero =>
      rw [map_zero]
      exact (Ideal.span ((SymmetricAlgebra.ι k V) '' s)).zero_mem
    | add x y _ _ hx hy =>
      rw [map_add]
      exact (Ideal.span ((SymmetricAlgebra.ι k V) '' s)).add_mem hx hy
    | smul r x _ hx =>
      rw [map_smul,Algebra.smul_def]
      exact (Ideal.span ((SymmetricAlgebra.ι k V) '' s)).mul_mem_left _ hx
  · apply Ideal.span_le.mpr
    rintro _ ⟨v,hv,rfl⟩
    exact (ι_mem_iff _ _).mpr (Submodule.subset_span hv)

end
end KLInvariance.SymmetricPlaneIdeal
end

end OAI
