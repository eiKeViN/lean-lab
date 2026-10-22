module
public import Mathlib
public import ForMathlib.Algebra.Module.Projective.ReverseFiltration

public section

/-! Semantic home: ForMathlib.Algebra.Module.Projective.ScalarQuotient. Source spans: GradedModules:2.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.ReverseFiltration
universe ua up ui
variable {A : Type ua} [CommRing A] [klPreservedInstance10 : IsDomain A]
noncomputable section

@[expose] def scalarQuotientMap (a : A) (ι : Type ui) :
    (ι → A) →ₗ[A] (ι → A ⧸ Ideal.span {a}) where
  toFun v i := Ideal.Quotient.mk _ (v i)
  map_add' _ _ := by ext i; simp
  map_smul' _ _ := by ext i; simp [Algebra.smul_def]

include klPreservedInstance10 in
theorem scalarQuotientMap_surjective (a : A) (ι : Type ui) :
    Function.Surjective (scalarQuotientMap a ι) := by
  have _ := klPreservedInstance10
  intro v
  choose w hw using fun i => Ideal.Quotient.mk_surjective (v i)
  exact ⟨w,funext hw⟩

/-- Multiplication by the actual nonzero label identifies the kernel of
coordinate reduction with a free module. -/
@[expose] def scalarKernelMap (a : A) (ι : Type ui) :
    (ι → A) →ₗ[A] LinearMap.ker (scalarQuotientMap a ι) where
  toFun v := ⟨fun i => a*v i, by
    ext i
    change Ideal.Quotient.mk (Ideal.span {a}) (a*v i)=0
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact Ideal.mem_span_singleton.mpr (dvd_mul_right a (v i))⟩
  map_add' v w := by apply Subtype.ext; ext i; exact mul_add _ _ _
  map_smul' r v := by apply Subtype.ext; ext i; change a*(r*v i)=r*(a*v i); ring

theorem scalarKernelMap_bijective (a : A) (ha : a≠0) (ι : Type ui) :
    Function.Bijective (scalarKernelMap a ι) := by
  constructor
  · intro v w hvw
    funext i
    exact mul_left_cancel₀ ha (congrFun (congrArg Subtype.val hvw) i)
  · intro v
    have hv (i : ι) : a ∣ v.val i := by
      apply Ideal.mem_span_singleton.mp
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      exact congrFun v.property i
    choose w hw using hv
    refine ⟨w,Subtype.ext (funext fun i => (hw i).symm)⟩

theorem scalarKernel_projective (a : A) (ha : a≠0) (ι : Type ui) [Finite ι] :
    Module.Projective A (LinearMap.ker (scalarQuotientMap a ι)) := by
  exact Module.Projective.of_equiv
    (LinearEquiv.ofBijective (scalarKernelMap a ι) (scalarKernelMap_bijective a ha ι))

/-- Every finite free module over A/(a) has an actual free A-presentation
with projective kernel; no projective-dimension hypothesis is inserted. -/
theorem exists_scalar_presentation (a : A) (ha : a≠0)
    (P : Type up) [AddCommGroup P] [Module A P]
    [Module (A ⧸ Ideal.span {a}) P] [IsScalarTower A (A ⧸ Ideal.span {a}) P]
    [Module.Free (A ⧸ Ideal.span {a}) P] [Module.Finite (A ⧸ Ideal.span {a}) P] :
    ∃ (ι : Type up), Finite ι ∧ ∃ g : (ι → A) →ₗ[A] P,
      Function.Surjective g ∧ Module.Projective A (LinearMap.ker g) := by
  classical
  let C := A ⧸ Ideal.span {a}
  let b := Module.Free.chooseBasis C P
  let ι := Module.Free.ChooseBasisIndex C P
  let : Fintype ι := Fintype.ofFinite ι
  let e : P ≃ₗ[A] (ι → C) := b.equivFun.restrictScalars A
  let g : (ι → A) →ₗ[A] P := e.symm.toLinearMap.comp (scalarQuotientMap a ι)
  refine ⟨ι,inferInstance,g,e.symm.surjective.comp (scalarQuotientMap_surjective a ι),?_⟩
  have hker : LinearMap.ker g = LinearMap.ker (scalarQuotientMap a ι) := by
    ext v
    change e.symm (scalarQuotientMap a ι v)=0 ↔ scalarQuotientMap a ι v=0
    exact e.symm.map_eq_zero_iff
  rw [hker]
  exact scalarKernel_projective a ha ι

/-- The reverse-filtration kernel is projective when the edge image is
actually finite free over the hypersurface quotient. -/
theorem kernel_projective_of_free_scalar_quotient
    (a : A) (ha : a≠0) {F : Type*} [AddCommGroup F] [Module A F]
    [Module.Projective A F]
    {P : Type up} [AddCommGroup P] [Module A P]
    [Module (A ⧸ Ideal.span {a}) P] [IsScalarTower A (A ⧸ Ideal.span {a}) P]
    [Module.Free (A ⧸ Ideal.span {a}) P] [Module.Finite (A ⧸ Ideal.span {a}) P]
    (f : F →ₗ[A] P) (hf : Function.Surjective f) :
    Module.Projective A (LinearMap.ker f) := by
  obtain ⟨ι,hι,g,hg,hgker⟩ := exists_scalar_presentation a ha P
  let : Finite ι := hι
  let := hgker
  exact kernel_projective_of_presentation f g hf hg

end
end KLInvariance.ReverseFiltration
end

end OAI
