module
public import Mathlib
public import ForMathlib.Algebra.Module.Graded.ModuleData.Basic
public import ForMathlib.LinearAlgebra.Quotient.Transport

public section

/-! Semantic home: ForMathlib.Algebra.Module.Graded.ModuleData.QuotientHom. Source spans: SheafMorphisms:10.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.Graded.ModuleData
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A}
noncomputable section

 @[expose] def quotientHom {M N E F : ModuleData.{uk,ua,um} 𝓐}
    (f : Hom M E) (g : Hom N F) (hf : Function.Surjective f.map)
    (h : Hom M N) (hk : LinearMap.ker f.map ≤ LinearMap.ker (g.map.comp h.map)) : Hom E F where
  map := QuotientEdge.descend f.map g.map hf h.map hk
  graded := by
    intro n v hv
    obtain ⟨w,hw,rfl⟩ := f.homogeneous_preimage hf n v hv
    rw [QuotientEdge.descend_apply]
    exact g.graded n _ (h.graded n w hw)

 theorem quotientHom_apply {M N E F : ModuleData.{uk,ua,um} 𝓐}
    (f : Hom M E) (g : Hom N F) (hf : Function.Surjective f.map)
    (h : Hom M N) (hk : LinearMap.ker f.map ≤ LinearMap.ker (g.map.comp h.map))
    (v : M) : (quotientHom f g hf h hk).map (f.map v) = g.map (h.map v) :=
  QuotientEdge.descend_apply _ _ _ _ _ v

end
end KLInvariance.Graded.ModuleData
end

end OAI
