import Mathlib
import ForMathlib.Algebra.Module.Graded.ModuleData.Basic
import ForMathlib.LinearAlgebra.PairProjection

/-! Semantic home: ForMathlib.Algebra.Module.Graded.ModuleData.PairProjection. Source spans: BottSamelson:20.
See migration.json and MIGRATION.md for exact provenance.
Graded module-data realization of the existing pair-projection edge, its two maps and homogeneous lifts. -/

namespace OAI

section
namespace KLInvariance.Graded.ModuleData
open PairProjection
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} {M X Y : ModuleData.{uk,ua,um} 𝓐}
  (f : Hom M X) (g : Hom M Y)
noncomputable section

 theorem pairLower_kernel_homogeneous (n : ℤ) (z : X)
    (hz : lower f.map g.map z=0) :
    lower f.map g.map (component X.piece n z)=0 := by
  obtain ⟨m,hm,hy⟩ := (kernel_lower f.map g.map z).mp hz
  apply (kernel_lower f.map g.map _).mpr
  refine ⟨component M.piece n m,?_,?_⟩
  · rw [← f.component,hm]
  · rw [← g.component,hy,map_zero]

 def pairEdgePiece (n : ℤ) : Submodule k (Edge f.map g.map) :=
  (X.piece n).map ((lower f.map g.map).restrictScalars k)

 def pairEdge (hg : Function.Surjective g.map) : ModuleData.{uk,ua,um} 𝓐 where
  obj := ModuleCat.of A (Edge f.map g.map)
  kModule := inferInstance
  tower := inferInstance
  piece := pairEdgePiece f g
  decomposition := (image_isInternal X.piece ((lower f.map g.map).restrictScalars k)
    (lower_surjective f.map g.map hg) (pairLower_kernel_homogeneous f g)).chooseDecomposition
  graded := ⟨by
    rintro i j a z ha ⟨w,hw,rfl⟩
    exact ⟨a • w,SetLike.GradedSMul.smul_mem ha hw,map_smul (lower f.map g.map) a w⟩⟩
  nonneg := by
    intro n hn
    unfold pairEdgePiece
    rw [X.nonneg n hn,Submodule.map_bot]
  finite := Module.Finite.of_surjective (lower f.map g.map) (lower_surjective f.map g.map hg)

 def pairLower (hg : Function.Surjective g.map) : Hom X (pairEdge f g hg) where
  map := lower f.map g.map
  graded := fun _ z hz => ⟨z,hz,rfl⟩

 theorem Hom.homogeneous_lift (hg : Function.Surjective g.map) (n : ℤ)
    (y : Y) (hy : y ∈ Y.piece n) : ∃ m : M, m ∈ M.piece n ∧ g.map m=y := by
  obtain ⟨m,hm⟩ := hg y
  refine ⟨Graded.component M.piece n m,(DirectSum.decompose M.piece m n).property,?_⟩
  rw [← g.component,hm]
  exact DirectSum.decompose_of_mem_same Y.piece hy

 def pairUpper (hg : Function.Surjective g.map) : Hom Y (pairEdge f g hg) where
  map := upper f.map g.map
  graded := by
    intro n y hy
    obtain ⟨m,hm,rfl⟩ := g.homogeneous_lift hg n y hy
    exact ⟨f.map m,f.graded n m hm,compatible f.map g.map m⟩

end
end KLInvariance.Graded.ModuleData
end

end OAI
