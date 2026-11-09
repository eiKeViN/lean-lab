module
import ForMathlib.Combinatorics.MomentGraph.Sheaf.Restriction
import ForMathlib.Combinatorics.MomentGraph.Sheaf.Models
import Lean
open Lean Elab Command OAI.KLInvariance.MomentGraph
run_elab do
  for n in #[`OAI.KLInvariance.MomentGraph.Sheaf.Iso.assignments,
      `OAI.KLInvariance.MomentGraph.Sheaf.Iso.sections,
      `OAI.KLInvariance.MomentGraph.Sheaf.Iso.boundary,
      `OAI.KLInvariance.MomentGraph.Sheaf.upwardKernel,
      `OAI.KLInvariance.MomentGraph.Sheaf.prod,
      `OAI.KLInvariance.MomentGraph.Sheaf.pi,
      `OAI.KLInvariance.MomentGraph.Sheaf.restrict,
      `OAI.KLInvariance.MomentGraph.Sheaf.extendAssignment] do
    unless (← getEnv).find? n |>.any (fun ci => ci.hasValue) do
      throwError "Lost exposed mathematical operation: {n}"
  logInfo "All eight computation interfaces retain exposed bodies."
section
universe u v w z
variable {R : Type u} [CommRing R] {V : Type v} [PartialOrder V] {E : Type w}
  {G : OrderedGraph V E} (B : Sheaf.{u,v,w,z} (R := R) G) (K : Set V)
example (f g : (B.restrict K).Assignment)
    (h : B.extendAssignment K f = B.extendAssignment K g) : f = g := by
  have hh := congrArg (B.restrictAssignment K) h
  simpa only [Sheaf.restrict_extendAssignment] using hh
end
#print axioms OAI.KLInvariance.MomentGraph.Sheaf.Iso.assignments_apply
#print axioms OAI.KLInvariance.MomentGraph.Sheaf.Iso.assignments_symm_apply
#print axioms OAI.KLInvariance.MomentGraph.Sheaf.Iso.sections_val_apply
#print axioms OAI.KLInvariance.MomentGraph.Sheaf.Iso.boundary_apply
#print axioms OAI.KLInvariance.MomentGraph.Sheaf.mem_upwardKernel_iff
#print axioms OAI.KLInvariance.MomentGraph.Sheaf.upwardKernel_univ
#print axioms OAI.KLInvariance.MomentGraph.Sheaf.pi_stalkMap_apply
#print axioms OAI.KLInvariance.MomentGraph.Sheaf.prod_stalkMap_apply
#print axioms OAI.KLInvariance.MomentGraph.Sheaf.prod_compatible_iff
#print axioms OAI.KLInvariance.MomentGraph.Sheaf.restrict_extendAssignment
#print axioms OAI.KLInvariance.MomentGraph.Sheaf.restrict_compatible_iff
#print axioms OAI.KLInvariance.MomentGraph.Sheaf.Iso.flabby
#print axioms OAI.KLInvariance.MomentGraph.Sheaf.Iso.generated
#print axioms OAI.KLInvariance.MomentGraph.Sheaf.Iso.boundaryMap
#print axioms OAI.KLInvariance.MomentGraph.Sheaf.Iso.upwardKernel_iff
#print axioms OAI.KLInvariance.MomentGraph.Sheaf.prod_generated
#print axioms OAI.KLInvariance.MomentGraph.Sheaf.prod_flabby
#print axioms OAI.KLInvariance.MomentGraph.Sheaf.prod_kernel_iff
#print axioms OAI.KLInvariance.MomentGraph.Sheaf.pi_kernel_iff
#print axioms OAI.KLInvariance.MomentGraph.Sheaf.prod_upwardKernel_iff
#print axioms OAI.KLInvariance.MomentGraph.Sheaf.pi_upwardKernel_iff
#print axioms OAI.KLInvariance.MomentGraph.Sheaf.upwardKernel_le_pullback
#print axioms OAI.KLInvariance.MomentGraph.Sheaf.pullbackKernel_le_of_live
#print axioms OAI.KLInvariance.MomentGraph.Sheaf.extend_compatible
#print axioms OAI.KLInvariance.MomentGraph.Sheaf.restrict_flabby_live
