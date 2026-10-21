import Mathlib
import ForMathlib.Algebra.Module.Graded.Hilbert.Images
import ForMathlib.Algebra.Module.Projective.ReverseFiltration

/-! Semantic home: ForMathlib.Algebra.Module.Projective.ScalarKernel. Source spans: PositiveTransfer:12.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.ReverseFiltration
universe ua um un up
variable {A : Type ua} [CommRing A]
  {M : Type um} [AddCommGroup M] [Module A M]
  {N : Type un} [AddCommGroup N] [Module A N]
  {P : Type up} [AddCommGroup P] [Module A P]

/-- A kernel which is exactly a regular scalar multiple of its domain is
integrally isomorphic to that domain, not just to its fraction-field span. -/
noncomputable def scalarKernelEquiv (g : M →ₗ[A] N) (a : A)
    (hk : ∀ v, g v = 0 ↔ ∃ w, v = a • w)
    (ha : Function.Injective (fun v : M => a • v)) :
    M ≃ₗ[A] LinearMap.ker g := by
  let f : M →ₗ[A] LinearMap.ker g :=
    (LinearMap.lsmul A M a).codRestrict (LinearMap.ker g) (fun v =>
      (hk (a • v)).mpr ⟨v,rfl⟩)
  apply LinearEquiv.ofBijective f
  constructor
  · intro x y h
    exact ha (congrArg Subtype.val h)
  · intro v
    obtain ⟨w,hw⟩ := (hk v.val).mp v.property
    exact ⟨w,Subtype.ext hw.symm⟩


 theorem projective_kernel_of_scalar_presentation
    [Module.Projective A M] [Module.Projective A P]
    (f : P →ₗ[A] N) (g : M →ₗ[A] N)
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    (a : A) (hk : ∀ v, g v = 0 ↔ ∃ w, v = a • w)
    (ha : Function.Injective (fun v : M => a • v)) :
    Module.Projective A (LinearMap.ker f) := by
  let : Module.Projective A (LinearMap.ker g) :=
    Module.Projective.of_equiv (scalarKernelEquiv g a hk ha)
  exact kernel_projective_of_presentation f g hf hg

 def imageMapKernelEquiv (S : Submodule A M) (f : M →ₗ[A] N) :
    ↥(S ⊓ LinearMap.ker f) ≃ₗ[A] LinearMap.ker (Hilbert.imageMap S f) where
  toFun v := ⟨⟨v.val,v.property.1⟩,Subtype.ext v.property.2⟩
  invFun v := ⟨v.val.val,v.val.property,congrArg Subtype.val v.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Scaled equality of two *embedded* images constructs a presentation with
regular scalar kernel. This is the pure module-algebra form of the reverse
freeness step, allowing arbitrary image codimension. -/
 theorem inf_kernel_projective_of_image_eq
    (S : Submodule A M) (T : Submodule A P)
    [Module.Projective A S] [Module.Projective A T]
    (f : M →ₗ[A] N) (g : P →ₗ[A] N) (φ : N →ₗ[A] N)
    (hφ : Function.Injective φ) (himage : S.map f = (T.map g).map φ)
    (a : A) (hk : ∀ v, g v = 0 ↔ ∃ w, v = a • w)
    (hsat : ∀ v, a • v ∈ T → v ∈ T)
    (ha : Function.Injective (fun v : P => a • v)) :
    Module.Projective A ↥(S ⊓ LinearMap.ker f) := by
  let j : T →ₗ[A] S.map f := ((φ.comp g).comp T.subtype).codRestrict (S.map f) (by
    intro v
    rw [himage]
    exact Submodule.mem_map.mpr ⟨g v.val,Submodule.mem_map.mpr ⟨v.val,v.property,rfl⟩,rfl⟩)
  have hj : Function.Surjective j := by
    intro v
    have hv : v.val ∈ (T.map g).map φ := himage ▸ v.property
    obtain ⟨w,hw,hwv⟩ := Submodule.mem_map.mp hv
    obtain ⟨z,hz,hzw⟩ := Submodule.mem_map.mp hw
    exact ⟨⟨z,hz⟩,Subtype.ext ((congrArg φ hzw).trans hwv)⟩
  have hjker (v : T) : j v = 0 ↔ ∃ w : T, v = a • w := by
    constructor
    · intro hv
      have hv' : φ (g v.val) = 0 := congrArg Subtype.val hv
      have hz : g v.val = 0 := hφ (hv'.trans (map_zero φ).symm)
      obtain ⟨w,hw⟩ := (hk v.val).mp hz
      refine ⟨⟨w,hsat w (hw ▸ v.property)⟩,Subtype.ext hw⟩
    · rintro ⟨w,rfl⟩
      apply Subtype.ext
      change φ (g (a • w.val)) = 0
      rw [(hk (a • w.val)).mpr ⟨w.val,rfl⟩,map_zero]
  have haT : Function.Injective (fun v : T => a • v) := by
    intro v w hvw
    exact Subtype.ext (ha (congrArg Subtype.val hvw))
  let : Module.Projective A (LinearMap.ker (Hilbert.imageMap S f)) :=
    projective_kernel_of_scalar_presentation (Hilbert.imageMap S f) j
      (Hilbert.imageMap_surjective S f) hj a hjker haT
  exact Module.Projective.of_equiv (imageMapKernelEquiv S f).symm

end KLInvariance.ReverseFiltration
end

end OAI
