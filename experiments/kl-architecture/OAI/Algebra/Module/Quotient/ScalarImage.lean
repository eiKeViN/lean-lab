import Mathlib
import OAI.Algebra.Module.Free.ScalarDivisibility
import OAI.Algebra.Module.Quotient.EdgeEquiv

/-! Semantic home: OAI.Algebra.Module.Quotient.ScalarImage. Source spans: TerminalKernels:11, TerminalKernels:16.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.ScalarQuotient
open Module
universe ur um un ui
variable {R : Type ur} [CommRing R]
  {M : Type um} [AddCommGroup M] [Module R M]
  {N : Type un} [AddCommGroup N] [Module R N]
  {ι : Type ui} [Fintype ι]
noncomputable section

 def coordinateReduction (b : Basis ι R M) (a : R) :
    M →ₗ[R] (ι → R ⧸ Ideal.span {a}) :=
  (LinearMap.pi fun i => (Ideal.span ({a} : Set R)).mkQ.comp
    ((LinearMap.proj i).comp b.equivFun.toLinearMap))

 theorem coordinateReduction_surjective (b : Basis ι R M) (a : R) :
    Function.Surjective (coordinateReduction b a) := by
  intro v
  choose w hw using fun i => Ideal.Quotient.mk_surjective (v i)
  exact ⟨b.equivFun.symm w,funext fun i => by
    change Ideal.Quotient.mk (Ideal.span {a}) (b.equivFun (b.equivFun.symm w) i)=v i
    simpa only [LinearEquiv.apply_symm_apply] using hw i⟩

 theorem coordinateReduction_kernel (b : Basis ι R M) (a : R) (v : M) :
    coordinateReduction b a v=0 ↔ ∃ w, v=a • w := by
  have h : (∃ w, v=a • w) ↔ ∀ i, a ∣ b.equivFun v i :=
    (exists_congr fun _ => eq_comm).trans (FiniteFreeScalar.exists_smul_iff b a v)
  rw [h]
  simp only [coordinateReduction,LinearMap.pi_apply,LinearMap.comp_apply,
    LinearMap.proj_apply,LinearEquiv.coe_coe,funext_iff,Pi.zero_apply]
  exact forall_congr' fun i => (Ideal.Quotient.eq_zero_iff_mem).trans Ideal.mem_span_singleton

 theorem free_of_scalar_presentation (a : R)
    [Module (R ⧸ Ideal.span {a}) N] [IsScalarTower R (R ⧸ Ideal.span {a}) N]
    (b : Basis ι R M) (q : M →ₗ[R] N) (hq : Function.Surjective q)
    (hk : ∀ v, q v=0 ↔ ∃ w, v=a • w) :
    Module.Free (R ⧸ Ideal.span {a}) N := by
  obtain ⟨j,_⟩ := QuotientEdge.exists_scalar_iso q (coordinateReduction b a) a
    hq (coordinateReduction_surjective b a) hk (coordinateReduction_kernel b a)
    (LinearEquiv.refl R M)
  let k : N ≃ₗ[R ⧸ Ideal.span {a}] (ι → R ⧸ Ideal.span {a}) :=
    { j.toAddEquiv with
      map_smul' := by
        intro c v
        obtain ⟨r,rfl⟩ := Ideal.Quotient.mk_surjective c
        change j ((algebraMap R (R ⧸ Ideal.span {a}) r) • v) =
          (algebraMap R (R ⧸ Ideal.span {a}) r) • j v
        simpa only [algebraMap_smul] using j.map_smul r v }
  exact Module.Free.of_equiv k.symm

 def submodule (a : R) [Module (R ⧸ Ideal.span {a}) N]
    [IsScalarTower R (R ⧸ Ideal.span {a}) N] (S : Submodule R N) :
    Submodule (R ⧸ Ideal.span {a}) N where
  carrier := S
  add_mem' := S.add_mem
  zero_mem' := S.zero_mem
  smul_mem' c v hv := by
    obtain ⟨r,rfl⟩ := Ideal.Quotient.mk_surjective c
    change (algebraMap R (R ⧸ Ideal.span {a}) r) • v ∈ S
    simpa only [algebraMap_smul] using S.smul_mem r hv

 theorem saturated_image_free (a : R)
    [Module (R ⧸ Ideal.span {a}) N] [IsScalarTower R (R ⧸ Ideal.span {a}) N]
    (q : M →ₗ[R] N) (hk : ∀ v, q v=0 ↔ ∃ w, v=a • w)
    (L : Submodule R M) [Module.Free R L] [Module.Finite R L]
    (hsat : ∀ v, a • v ∈ L → v ∈ L) :
    Module.Free (R ⧸ Ideal.span {a}) (submodule a (L.map q)) := by
  let f : L →ₗ[R] submodule a (L.map q) :=
    (q.comp L.subtype).codRestrict ((submodule a (L.map q)).restrictScalars R)
      (fun v => ⟨v.val,v.property,rfl⟩)
  apply free_of_scalar_presentation a (Module.Free.chooseBasis R L) f
  · rintro ⟨v,hv⟩
    obtain ⟨w,hw,rfl⟩ := hv
    exact ⟨⟨w,hw⟩,rfl⟩
  · intro v
    constructor
    · intro hv
      obtain ⟨w,hw⟩ := (hk v.val).mp (congrArg Subtype.val hv)
      exact ⟨⟨w,hsat w (hw ▸ v.property)⟩,Subtype.ext hw⟩
    · rintro ⟨w,rfl⟩
      exact Subtype.ext ((hk _).mpr ⟨w.val,rfl⟩)

end
end KLInvariance.ScalarQuotient
end


section
namespace KLInvariance.ScalarQuotient
universe ur un
variable {R : Type ur} [CommRing R]
  {N : Type un} [AddCommGroup N] [Module R N]
noncomputable section

 theorem scalarImage (a z : R)
    [Module (R ⧸ Ideal.span {a}) N] [IsScalarTower R (R ⧸ Ideal.span {a}) N]
    (S : Submodule R N) :
    submodule a (S.map (LinearMap.lsmul R N z)) =
      (submodule a S).map
        (LinearMap.lsmul (R ⧸ Ideal.span {a}) N (Ideal.Quotient.mk _ z)) := by
  ext v
  constructor
  · rintro ⟨w,hw,rfl⟩
    exact ⟨w,hw,by simp only [LinearMap.lsmul_apply]; exact algebraMap_smul _ _ w⟩
  · rintro ⟨w,hw,rfl⟩
    exact ⟨w,hw,by simp only [LinearMap.lsmul_apply]; exact (algebraMap_smul _ _ w).symm⟩

 theorem free_scalarImage (a z : R)
    [Module (R ⧸ Ideal.span {a}) N] [IsScalarTower R (R ⧸ Ideal.span {a}) N]
    (S : Submodule R N) [Module.Free (R ⧸ Ideal.span {a}) (submodule a S)]
    (hz : Function.Injective (fun v : N => z • v)) :
    Module.Free (R ⧸ Ideal.span {a}) (submodule a (S.map (LinearMap.lsmul R N z))) := by
  rw [scalarImage]
  apply Module.Free.of_equiv (Submodule.equivMapOfInjective _ ?_ (submodule a S))
  intro v w h
  apply hz
  change (algebraMap R (R ⧸ Ideal.span {a}) z) • v =
    (algebraMap R (R ⧸ Ideal.span {a}) z) • w at h
  simpa only [algebraMap_smul] using h

end
end KLInvariance.ScalarQuotient
end

end OAI
