module
import ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Summand
import Lean
open Lean Elab Command OAI.KLInvariance
run_elab do
  for n in #[`OAI.KLInvariance.MomentGraph.GradedSheaf.Hom.comp,
      `OAI.KLInvariance.MomentGraph.GradedSheaf.Hom.inverse,
      `OAI.KLInvariance.Graded.ModuleData.rangeMap,
      `OAI.KLInvariance.MomentGraph.GradedSheaf.Hom.imageSectionMap,
      `OAI.KLInvariance.MomentGraph.GradedSheaf.SplitIn.downEnd] do
    unless (← getEnv).find? n |>.any (fun ci => ci.hasValue) do
      throwError "Lost exposed computation interface: {n}"
section
open MomentGraph GradedSheaf Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} {V E : Type um} [PartialOrder V] {G : OrderedGraph V E}
  {B C D : GradedSheaf (𝓐 := 𝓐) G}
example (f : Hom B C) (g : Hom C D)
    (hv : ∀ x, Function.Bijective (g.vertex x).map)
    (he : ∀ e, Function.Bijective (g.edge e).map) (Ω : Set V) :
    ((g.inverse hv he).comp (g.comp f)).sectionMap Ω = f.sectionMap Ω := by
  rw [← Hom.comp_assoc, Hom.inverse_comp, Hom.id_comp]
example (s : SplitIn B C) (f : Hom B B) : s.downEnd (s.liftEnd f) = f := s.compress_liftEnd f
end
#print axioms OAI.KLInvariance.Graded.ModuleData.rangeMap_id
#print axioms OAI.KLInvariance.Graded.ModuleData.rangeMap_comp
#print axioms OAI.KLInvariance.Graded.ModuleData.rangeInclusion_comp_rangeMap
#print axioms OAI.KLInvariance.MomentGraph.GradedSheaf.Hom.comp_assoc
#print axioms OAI.KLInvariance.MomentGraph.GradedSheaf.Hom.id_comp
#print axioms OAI.KLInvariance.MomentGraph.GradedSheaf.Hom.comp_id
#print axioms OAI.KLInvariance.MomentGraph.GradedSheaf.Hom.inverse_comp
#print axioms OAI.KLInvariance.MomentGraph.GradedSheaf.Hom.comp_inverse
#print axioms OAI.KLInvariance.MomentGraph.GradedSheaf.Hom.imageInclusion_comp_imageProjection
#print axioms OAI.KLInvariance.MomentGraph.GradedSheaf.Hom.imageSectionMap_val
#print axioms OAI.KLInvariance.MomentGraph.GradedSheaf.Hom.imageSplit_projector
#print axioms OAI.KLInvariance.MomentGraph.GradedSheaf.SplitIn.downEnd_comp
#print axioms OAI.KLInvariance.MomentGraph.GradedSheaf.SplitIn.liftEnd_downEnd
#print axioms OAI.KLInvariance.MomentGraph.GradedSheaf.Hom.imageSectionMap_bijective
#print axioms OAI.KLInvariance.MomentGraph.GradedSheaf.Hom.imageSectionEquiv_val
#print axioms OAI.KLInvariance.MomentGraph.GradedSheaf.SplitIn.imageTo_toImage_vertex
#print axioms OAI.KLInvariance.MomentGraph.GradedSheaf.SplitIn.imageTo_toImage_edge
#print axioms OAI.KLInvariance.MomentGraph.GradedSheaf.SplitIn.primitive_projector_of_id
#print axioms OAI.KLInvariance.MomentGraph.GradedSheaf.SplitIn.lift_down
