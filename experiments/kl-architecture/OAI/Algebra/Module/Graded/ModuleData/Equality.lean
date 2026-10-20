import Mathlib
import OAI.Algebra.Module.Graded.ModuleData.Basic

/-! Semantic home: OAI.Algebra.Module.Graded.ModuleData.Equality. Source spans: GradedSheaves:3, GradedSheaves:5.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.Graded.ModuleData
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A}

def Hom.ofEq {M N : ModuleData.{uk,ua,um} 𝓐} (h : M = N) : Hom M N := h ▸ Hom.id M

@[simp] theorem Hom.ofEq_rfl (M : ModuleData.{uk,ua,um} 𝓐) : Hom.ofEq (rfl : M=M) = Hom.id M := rfl

theorem Hom.ofEq_apply {ι : Type*} (M : ι → ModuleData.{uk,ua,um} 𝓐)
    {x y : ι} (h : x = y) (v : ∀ z, M z) :
    (Hom.ofEq (congrArg M h)).map (v x) = v y := by subst y; rfl

end KLInvariance.Graded.ModuleData
end


section
namespace KLInvariance.Graded.ModuleData
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A}

theorem Hom.ofEq_bijective {M N : ModuleData.{uk,ua,um} 𝓐} (h : M=N) :
    Function.Bijective (Hom.ofEq h).map := by subst N; exact Function.bijective_id

noncomputable def unit [DirectSum.Decomposition 𝓐] [SetLike.GradedMonoid 𝓐]
    (hneg : ∀ n < 0, 𝓐 n = ⊥) : ModuleData.{uk,ua,um} 𝓐 :=
  free (ι := PUnit.{max ua um + 1}) hneg (fun _ => 0) (fun _ => le_rfl)

instance unit_free [DirectSum.Decomposition 𝓐] [SetLike.GradedMonoid 𝓐]
    (hneg : ∀ n < 0, 𝓐 n = ⊥) : Module.Free A (unit.{uk,ua,um} hneg) :=
  inferInstanceAs (Module.Free A (PUnit.{max ua um + 1} → A))

end KLInvariance.Graded.ModuleData
end

end OAI
