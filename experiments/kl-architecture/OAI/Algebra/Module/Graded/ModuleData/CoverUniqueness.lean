import Mathlib
import OAI.Algebra.Module.Graded.ModuleData.Basic

/-! Semantic home: OAI.Algebra.Module.Graded.ModuleData.CoverUniqueness. Source spans: EdgeLocalization:8.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.Graded.ModuleData
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} [DirectSum.Decomposition 𝓐] [SetLike.GradedMonoid 𝓐]
  [IsDomain A] [IsNoetherianRing A]
  (hneg : ∀ n < 0, 𝓐 n = ⊥)
  (hzero : ∀ a ∈ 𝓐 0, ∃ c : k, algebraMap k A c = a)
  {T : ModuleData.{uk,ua,um} 𝓐}

include hneg hzero in
 theorem MinimalCover.hom_bijective (C D : MinimalCover T)
    (f : Hom C.source D.source) (hf : D.hom.map.comp f.map=C.hom.map) :
    Function.Bijective f.map := by
  let := C.free
  let := D.free
  obtain ⟨g,hg⟩ := exists_hom_lift hneg hzero C.hom C.surjective D.hom
  have hfa (v : C.source) : D.hom.map (f.map v)=C.hom.map v := LinearMap.congr_fun hf v
  have hga (v : D.source) : C.hom.map (g.map v)=D.hom.map v := LinearMap.congr_fun hg v
  have hgf : Function.Bijective (g.comp f).map := by
    apply Hom.bijective_of_mod_positive
    intro m
    apply C.minimal
    change C.hom.map (m-g.map (f.map m))=0
    rw [map_sub,hga,hfa,sub_self]
  have hfg : Function.Bijective (f.comp g).map := by
    apply Hom.bijective_of_mod_positive
    intro m
    apply D.minimal
    change D.hom.map (m-f.map (g.map m))=0
    rw [map_sub,hfa,hga,sub_self]
  exact ⟨Function.Injective.of_comp hgf.1,Function.Surjective.of_comp hfg.2⟩

end KLInvariance.Graded.ModuleData
end

end OAI
