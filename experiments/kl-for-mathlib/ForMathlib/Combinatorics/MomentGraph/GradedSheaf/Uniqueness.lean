module
public import Mathlib
public import ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Duality

public section

/-! Semantic home: ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Uniqueness. Source spans: EdgeLocalization:10, EdgeLocalization:12, EdgeLocalization:17, EdgeLocalization:14.
See migration.json and MIGRATION.md for exact provenance. -/

namespace OAI

section
namespace KLInvariance.MomentGraph.GradedSheaf
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} {V E : Type um} [PartialOrder V]
  {G : OrderedGraph V E} {B C : GradedSheaf (𝓐 := 𝓐) G}
noncomputable section

 theorem Hom.edge_bijective_of_vertex (f : Hom B C) (α : E → A)
    (hB : B.UpperQuotient α) (hC : C.UpperQuotient α) (e : E)
    (hv : Function.Bijective (f.vertex (G.target e)).map) :
    Function.Bijective (f.edge e).map := by
  let v := LinearEquiv.ofBijective (f.vertex (G.target e)).map hv
  let j := QuotientEdge.iso (B.upper e).map (C.upper e).map
    (hB e).1 (hC e).1 v (QuotientEdge.map_kernel_scalar _ _ (α e) (hB e).2 (hC e).2 v)
  have he : (f.edge e).map=j.toLinearMap := by
    apply LinearMap.ext
    intro m
    obtain ⟨m,rfl⟩ := (hB e).1 m
    rw [f.upper]
    exact (QuotientEdge.iso_apply (B.upper e).map (C.upper e).map
      (hB e).1 (hC e).1 v
      (QuotientEdge.map_kernel_scalar _ _ (α e) (hB e).2 (hC e).2 v) m).symm
  rw [he]
  exact j.bijective

 @[expose] def Hom.isoOfBijective (f : Hom B C)
    (hv : ∀ x, Function.Bijective (f.vertex x).map)
    (he : ∀ e, Function.Bijective (f.edge e).map) : Iso B C where
  vertex x := LinearEquiv.ofBijective (f.vertex x).map (hv x)
  edge e := LinearEquiv.ofBijective (f.edge e).map (he e)
  lower := f.lower
  upper := f.upper
  vertex_graded x := (f.vertex x).graded
  edge_graded e := (f.edge e).graded

 @[expose] def Hom.aboveIso (f : Hom B C) (x : V)
    (hv : ∀ y, x<y → Function.Bijective (f.vertex y).map)
    (he : ∀ e, x<G.target e → Function.Bijective (f.edge e).map) :
    Sheaf.AboveIso B.forget C.forget x where
  vertex y hy := LinearEquiv.ofBijective (f.vertex y).map (hv y hy)
  edge e he' := LinearEquiv.ofBijective (f.edge e).map (he e he')
  lower e _ := f.lower e
  upper e _ := f.upper e

end
end KLInvariance.MomentGraph.GradedSheaf
end


section
namespace KLInvariance.MomentGraph.GradedSheaf
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} {V E : Type um} [PartialOrder V]
  {G : OrderedGraph V E} {B C : GradedSheaf (𝓐 := 𝓐) G}
noncomputable section

 @[expose] def Iso.hom (j : Iso B C) : Hom B C where
  vertex x := ⟨(j.vertex x).toLinearMap,j.vertex_graded x⟩
  edge e := ⟨(j.edge e).toLinearMap,j.edge_graded e⟩
  lower := j.lower
  upper := j.upper

 @[expose] def Iso.invHom (j : Iso B C) : Hom C B where
  vertex x := ⟨(j.vertex x).symm.toLinearMap,fun n v hv =>
    (j.hom.vertex x).mem_of_map_mem (j.vertex x).injective n _
      (by change j.vertex x ((j.vertex x).symm v) ∈ _
          exact ((j.vertex x).apply_symm_apply v).symm ▸ hv)⟩
  edge e := ⟨(j.edge e).symm.toLinearMap,fun n v hv =>
    (j.hom.edge e).mem_of_map_mem (j.edge e).injective n _
      (by change j.edge e ((j.edge e).symm v) ∈ _
          exact ((j.edge e).apply_symm_apply v).symm ▸ hv)⟩
  lower e v := by
    apply (j.edge e).injective
    exact ((j.edge e).apply_symm_apply _).trans
      ((j.lower e ((j.vertex (G.source e)).symm v)).trans
        (congrArg (C.forget.lower e) ((j.vertex (G.source e)).apply_symm_apply v))).symm
  upper e v := by
    apply (j.edge e).injective
    exact ((j.edge e).apply_symm_apply _).trans
      ((j.upper e ((j.vertex (G.target e)).symm v)).trans
        (congrArg (C.forget.upper e) ((j.vertex (G.target e)).apply_symm_apply v))).symm

end
end KLInvariance.MomentGraph.GradedSheaf
end


section
namespace KLInvariance.MomentGraph.GradedSheaf
open _root_.OAI.KLInvariance.Graded Module
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} {V E : Type um} [PartialOrder V]
  {G : OrderedGraph V E}
noncomputable section

 structure SymmetricPerfectPairing (S : GradedSheaf (𝓐 := 𝓐) G) (d : ℤ)
    extends PerfectPairing S d where
  symmetric : ∀ m n, pairing m n=pairing n m

 @[expose] def SymmetricPerfectPairing.pullback {S T : GradedSheaf (𝓐 := 𝓐) G} {d : ℤ}
    (p : SymmetricPerfectPairing T d) (j : Iso S T) : SymmetricPerfectPairing S d where
  toPerfectPairing := p.toPerfectPairing.pullback j
  symmetric _m _n := p.symmetric _ _

 variable {B : Type ua} [CommRing B] [Algebra k B] {𝓑 : ℤ → Submodule k B}
  (e : A ≃ₐ[k] B) (he : ∀ n a, a∈𝓐 n ↔ e a∈𝓑 n)

 @[expose] def SymmetricPerfectPairing.coefficientChange {S : GradedSheaf (𝓐 := 𝓐) G} {d : ℤ}
    (p : SymmetricPerfectPairing S d) : SymmetricPerfectPairing (coefficientChange e he S) d where
  toPerfectPairing := p.toPerfectPairing.coefficientChange e he
  symmetric m n := by
    exact (PerfectPairing.coefficientChange_apply e he p.toPerfectPairing m n).trans
      ((congrArg e (p.symmetric _ _)).trans
        (PerfectPairing.coefficientChange_apply e he p.toPerfectPairing n m).symm)

end
end KLInvariance.MomentGraph.GradedSheaf
end


section
namespace KLInvariance.MomentGraph.GradedSheaf
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} {V E : Type um} [PartialOrder V]
  {G : OrderedGraph V E} {B C D : GradedSheaf (𝓐 := 𝓐) G}
  (s : SplitIn B D) (t : SplitIn C D)

 theorem SplitIn.comparison_bijective (x : V)
    (hs : ∀ v, (s.projector.vertex x).map v=v)
    (ht : ∀ v, (t.projector.vertex x).map v=v) :
    Function.Bijective ((t.projection.comp s.inclusion).vertex x).map := by
  let f := ((t.projection.comp s.inclusion).vertex x).map
  let g := ((s.projection.comp t.inclusion).vertex x).map
  have hgf (v : B.vertex x) : g (f v)=v := by
    exact (congrArg (s.projection.vertex x).map (ht ((s.inclusion.vertex x).map v))).trans
      (s.vertex_split x v)
  have hfg (v : C.vertex x) : f (g v)=v := by
    exact (congrArg (t.projection.vertex x).map (hs ((t.inclusion.vertex x).map v))).trans
      (t.vertex_split x v)
  exact ⟨Function.LeftInverse.injective hgf,Function.RightInverse.surjective hfg⟩

end KLInvariance.MomentGraph.GradedSheaf
end

end OAI
