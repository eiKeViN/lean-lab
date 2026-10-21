import Mathlib
import ForMathlib.Algebra.Module.Graded.ModuleData.MinimalCover
import ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Extension

/-! Semantic home: ForMathlib.Combinatorics.MomentGraph.Sheaf.Hom. Source spans: SheafMorphisms:26.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.MomentGraph.Sheaf.AboveIso
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} [DirectSum.Decomposition 𝓐] [SetLike.GradedMonoid 𝓐]
  {V E : Type um} [PartialOrder V] {G : OrderedGraph V E}
  [Fintype E] [IsNoetherianRing A] [IsDomain A]
  (hneg : ∀ n < 0, 𝓐 n = ⊥)
  (hzero : ∀ a ∈ 𝓐 0, ∃ c : k, algebraMap k A c = a)
  {B C : GradedSheaf (𝓐 := 𝓐) G} {x : V}
  (j : AboveIso B.forget C.forget x)

include hneg hzero in
 theorem split_stalk_graded
    (hj : ∀ e (h : x < G.target e) n v, v ∈ (B.edge e).piece n →
      j.edge e h v ∈ (C.edge e).piece n)
    (hBfree : Module.Free A (B.vertex x)) (hCfree : Module.Free A (C.vertex x))
    (hBf : B.forget.Flabby) (hBg : B.forget.Generated)
    (hCf : C.forget.Flabby) (hCg : C.forget.Generated)
    (hCmin : C.KernelMinimal x) :
    ∃ (g : ModuleData.Hom (B.vertex x) (C.vertex x))
      (e : B.vertex x ≃ₗ[A] C.vertex x × ModuleData.kernel g),
      Module.Free A (ModuleData.kernel g) ∧
      (∀ n v, v ∈ (B.vertex x).piece n →
        e v ∈ (ModuleData.prod (C.vertex x) (ModuleData.kernel g)).piece n) ∧
      ∀ v, j.boundary (B.forget.stalkMap x v) = C.forget.stalkMap x (e v).1 := by
  let T := ModuleData.range (C.stalkHom x)
  let f : ModuleData.Hom (B.vertex x) T :=
    { map := LinearMap.codRestrict (LinearMap.range (C.forget.stalkMap x))
        (j.boundary.toLinearMap.comp (B.forget.stalkMap x)) (by
          intro v
          rw [← j.map_stalk_image hBf hBg hCf hCg]
          exact ⟨B.forget.stalkMap x v,⟨v,rfl⟩,rfl⟩)
      graded := by
        intro n v hv e _
        exact hj e.val _ n _ ((B.stalkHom x).graded n v hv e (Set.mem_univ e)) }
  let p : ModuleData.Hom (C.vertex x) T :=
    { map := (C.forget.stalkMap x).rangeRestrict
      graded := fun n v hv => (C.stalkHom x).graded n v hv }
  have hfs : Function.Surjective f.map := by
    intro v
    have hv : v.val ∈ (LinearMap.range (B.forget.stalkMap x)).map j.boundary.toLinearMap := by
      rw [j.map_stalk_image hBf hBg hCf hCg]
      exact v.property
    obtain ⟨w,⟨z,rfl⟩,hz⟩ := hv
    exact ⟨z,Subtype.ext hz⟩
  have hps : Function.Surjective p.map := by
    intro v
    obtain ⟨w,hw⟩ := v.property
    exact ⟨w,Subtype.ext hw⟩
  have hpm : LinearMap.ker p.map ≤ positiveIdeal 𝓐 • (⊤ : Submodule A (C.vertex x)) := by
    intro v hv
    apply (C.kernelMinimal_iff x).mp hCmin
    have hh : p.map v = 0 := LinearMap.mem_ker.mp hv
    exact congrArg (fun z : T => z.val) hh
  let D : ModuleData.MinimalCover T := ⟨C.vertex x,hCfree,p,hps,hpm⟩
  let : Module.Free A (B.vertex x) := hBfree
  obtain ⟨g,h,hg,hgh⟩ := ModuleData.exists_minimalCover_split hneg hzero D f hfs
  refine ⟨g,g.splitEquiv h hgh,g.kernel_free_of_split hneg hzero h hgh,
    g.splitEquiv_graded h hgh,?_⟩
  intro v
  exact (congrArg Subtype.val (LinearMap.congr_fun hg v)).symm

end KLInvariance.MomentGraph.Sheaf.AboveIso
end

end OAI
