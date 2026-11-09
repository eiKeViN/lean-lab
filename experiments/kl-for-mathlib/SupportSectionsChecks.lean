module
import ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Duality
import OAI.KL.Sheaves.FreeModel
import OAI.KL.Comparison.Propagation
import OAI.KL.BottSamelson.AdjointSheaf
import Lean
open Lean Elab Command
run_elab do
  for n in #[`OAI.KLInvariance.MomentGraph.Sheaf.singleStalkEquivSupport,
      `OAI.KLInvariance.MomentGraph.Sheaf.kernelEquivSingleStalk,
      `OAI.KLInvariance.MomentGraph.Sheaf.singleSupportEquivDual,
      `OAI.KLInvariance.MomentGraph.GradedSheaf.Hom.imageSectionEquiv,
      `OAI.KLInvariance.MomentGraph.GradedSheaf.SplitIn.liftEnd,
      `OAI.KLInvariance.MomentGraph.GradedSheaf.SplitIn.projector] do
    unless (← getEnv).find? n |>.any (fun ci => ci.hasValue) do
      throwError "Lost exposed interface: {n}"
  logInfo "Six computation interfaces retain bodies through ordinary imports."
#print axioms OAI.KLInvariance.MomentGraph.Sheaf.singleSupportEquivDual_pairing
#print axioms OAI.KLInvariance.MomentGraph.Sheaf.singleSupportEquivDual_symm_pairing
#print axioms OAI.KLInvariance.MomentGraph.Sheaf.singleStalkEquivSupport_val
#print axioms OAI.KLInvariance.MomentGraph.Sheaf.singleStalkEquivSupport_apply_self
#print axioms OAI.KLInvariance.MomentGraph.Sheaf.singleStalkEquivSupport_symm_val
#print axioms OAI.KLInvariance.MomentGraph.Sheaf.kernelEquivSingleStalk_val
#print axioms OAI.KLInvariance.MomentGraph.GradedSheaf.singleSupportEquivDual_symm_homogeneous
#print axioms OAI.KLInvariance.MomentGraph.GradedSheaf.Hom.imageSectionEquiv_val
#print axioms OAI.KLInvariance.MomentGraph.GradedSheaf.SplitIn.liftEnd_vertex_apply
#print axioms OAI.KLInvariance.MomentGraph.GradedSheaf.SplitIn.liftEnd_edge_apply
#print axioms OAI.KLInvariance.MomentGraph.GradedSheaf.SplitIn.compress_liftEnd
#print axioms OAI.KLInvariance.MomentGraph.GradedSheaf.SplitIn.liftEnd_id
#print axioms OAI.KLInvariance.MomentGraph.GradedSheaf.SplitIn.liftEnd_injective
#print axioms OAI.KLInvariance.MomentGraph.GradedSheaf.SplitIn.liftEnd_comp
#print axioms OAI.KLInvariance.BruhatGraph.kernelEquivSingleSupport_apply
#print axioms OAI.KLInvariance.BruhatGraph.costalkEquivDual_inverse_homogeneous
#print axioms OAI.KLInvariance.BruhatGraph.costalkEquivDual_pairing
#print axioms OAI.KLInvariance.TitsSpace.bottImageSectionWordEquiv_coordinates
