import Mathlib
import ForMathlib.Algebra.Module.Graded.ModuleData.Basic
import ForMathlib.LinearAlgebra.Quotient.Transport

/-! Semantic home: ForMathlib.Algebra.Module.Graded.ModuleData.Transport. Source spans: MinimalExtensions:8, MinimalExtensions:4.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.Graded.ModuleData
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A}
noncomputable section
 def zero : ModuleData.{uk,ua,um} 𝓐 where
  obj := ModuleCat.of A PUnit.{max ua um+1}
  kModule := inferInstance
  tower := inferInstance
  piece _ := ⊥
  decomposition := (show DirectSum.IsInternal (fun _ : ℤ => (⊥ : Submodule k PUnit.{max ua um+1})) from by
    apply internal_of_components _ (fun _ => 0)
    · intro _ _; exact Submodule.zero_mem _
    · intro _ _ _; exact Subsingleton.elim _ _
    · intro _ _ _ _ _; rfl
    · intro m; exact ⟨∅,Subsingleton.elim _ _⟩).chooseDecomposition
  graded := ⟨by intro _ _ _ _ _ _; exact Subsingleton.elim _ _⟩
  nonneg _ _ := rfl
  finite := inferInstance

 def Hom.zero (M N : ModuleData.{uk,ua,um} 𝓐) : Hom M N :=
  ⟨0,fun _ _ _ => Submodule.zero_mem _⟩

 def Hom.pi {ι : Type um} [Fintype ι] {M N : ι → ModuleData.{uk,ua,um} 𝓐}
    (f : ∀ i, Hom (M i) (N i)) : Hom (ModuleData.pi M) (ModuleData.pi N) where
  map := LinearMap.pi fun i => (f i).map.comp (LinearMap.proj i)
  graded n _ hm i hi := (f i).graded n _ (hm i hi)
end
end KLInvariance.Graded.ModuleData
end


section
namespace KLInvariance.Graded.ModuleData
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A}

def equivOfEq {M N : ModuleData.{uk,ua,um} 𝓐} (h : M=N) : M ≃ₗ[A] N :=
  h ▸ LinearEquiv.refl A M

 theorem equivOfEq_graded {M N : ModuleData.{uk,ua,um} 𝓐} (h : M=N)
    (n : ℤ) (v : M) (hv : v ∈ M.piece n) : equivOfEq h v ∈ N.piece n := by
  subst N
  exact hv

 theorem quotient_iso_graded {M N E F : ModuleData.{uk,ua,um} 𝓐}
    (f : Hom M E) (g : Hom N F) (hf : Function.Surjective f.map)
    (hg : Function.Surjective g.map) (e : M ≃ₗ[A] N)
    (he : ∀ n v, v ∈ M.piece n → e v ∈ N.piece n)
    (hk : (LinearMap.ker f.map).map e.toLinearMap = LinearMap.ker g.map)
    (n : ℤ) (v : E) (hv : v ∈ E.piece n) :
    QuotientEdge.iso f.map g.map hf hg e hk v ∈ F.piece n := by
  obtain ⟨w,hw,rfl⟩ := f.homogeneous_preimage hf n v hv
  rw [QuotientEdge.iso_apply]
  exact g.graded n _ (he n w hw)

end KLInvariance.Graded.ModuleData
end

end OAI
