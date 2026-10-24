module
import ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Summand
import ForMathlib.Algebra.Module.ReflectionPair.TensorDescent
import ForMathlib.LinearAlgebra.KernelCoordinates
import Lean
open Lean Elab Command OAI.KLInvariance
run_elab do
  for n in #[`OAI.KLInvariance.Graded.ModuleData.rangeMap,
      `OAI.KLInvariance.MomentGraph.GradedSheaf.Hom.sectionMap,
      `OAI.KLInvariance.MomentGraph.GradedSheaf.SplitIn.projector,
      `OAI.KLInvariance.ReflectionPairTranslation.lattice,
      `OAI.KLInvariance.ReflectionPairTranslation.kernelMap,
      `OAI.KLInvariance.ReflectionPairTranslation.rightKernelMap,
      `OAI.KLInvariance.ReflectionPairTranslation.twistMap,
      `OAI.KLInvariance.ReflectionPairTranslation.tensorFirst,
      `OAI.KLInvariance.ReflectionPairTranslation.tensorSecond] do
    unless (← getEnv).find? n |>.any (fun ci => ci.hasValue) do
      throwError "Lost an exposed computation interface: {n}"
  logInfo "All nine computation interfaces retain exposed bodies."
section
open TensorProduct ReflectionPairTranslation
variable {C A N P Q : Type*} [CommRing C] [CommRing A] [Algebra C A]
  [AddCommGroup N] [Module A N] [Module C N] [IsScalarTower C A N]
  [AddCommGroup P] [Module A P] [Module C P] [IsScalarTower C A P]
  [AddCommGroup Q] [Module A Q] [Module C Q] [IsScalarTower C A Q]
example (f : N →ₗ[A] P) (g : P →ₗ[A] Q) (m : A ⊗[C] N) :
    tensorFirst (C := C)
      (AlgebraTensorModule.map (LinearMap.id : A →ₗ[A] A) ((g.comp f).restrictScalars C) m) =
      g (f (tensorFirst (C := C) m)) := by
  rw [tensorFirst_natural]
  rfl
end
#print axioms OAI.KLInvariance.Graded.ModuleData.rangeMap_val
#print axioms OAI.KLInvariance.Graded.ModuleData.rangeProjection_val
#print axioms OAI.KLInvariance.Graded.ModuleData.rangeInclusion_apply
#print axioms OAI.KLInvariance.Graded.ModuleData.range_fixed
#print axioms OAI.KLInvariance.MomentGraph.GradedSheaf.Hom.comp_vertex_apply
#print axioms OAI.KLInvariance.MomentGraph.GradedSheaf.Hom.comp_edge_apply
#print axioms OAI.KLInvariance.MomentGraph.GradedSheaf.Hom.sectionMap_comp
#print axioms OAI.KLInvariance.MomentGraph.GradedSheaf.Hom.sectionMap_id
#print axioms OAI.KLInvariance.MomentGraph.GradedSheaf.SplitIn.projection_comp_inclusion
#print axioms OAI.KLInvariance.MomentGraph.GradedSheaf.SplitIn.projector_apply_vertex
#print axioms OAI.KLInvariance.MomentGraph.GradedSheaf.SplitIn.projector_apply_edge
#print axioms OAI.KLInvariance.ReflectionPairTranslation.Twist.val_add
#print axioms OAI.KLInvariance.ReflectionPairTranslation.Twist.val_smul
#print axioms OAI.KLInvariance.ReflectionPairTranslation.mem_lattice_iff
#print axioms OAI.KLInvariance.ReflectionPairTranslation.left_apply
#print axioms OAI.KLInvariance.ReflectionPairTranslation.kernelMap_snd_val
#print axioms OAI.KLInvariance.ReflectionPairTranslation.twistMap_val
#print axioms OAI.KLInvariance.ReflectionPairTranslation.right_apply
#print axioms OAI.KLInvariance.ReflectionPairTranslation.rightKernelMap_fst
#print axioms OAI.KLInvariance.ReflectionPairTranslation.tensorFirst_natural
#print axioms OAI.KLInvariance.ReflectionPairTranslation.tensorSecond_natural
#print axioms OAI.KLInvariance.MomentGraph.GradedSheaf.SplitIn.sections_split
#print axioms OAI.KLInvariance.MomentGraph.GradedSheaf.Hom.imageInclusion
#print axioms OAI.KLInvariance.MomentGraph.GradedSheaf.Hom.imageProjection
#print axioms OAI.KLInvariance.MomentGraph.GradedSheaf.Hom.imageSplit
#print axioms OAI.KLInvariance.MomentGraph.GradedSheaf.Hom.imageSection_fixed
#print axioms OAI.KLInvariance.MomentGraph.GradedSheaf.SplitIn.projector_vertex
#print axioms OAI.KLInvariance.MomentGraph.GradedSheaf.SplitIn.projector_edge
#print axioms OAI.KLInvariance.ReflectionPairTranslation.lattice_saturated
#print axioms OAI.KLInvariance.ReflectionPairTranslation.kernelMap_surjective
#print axioms OAI.KLInvariance.ReflectionPairTranslation.rightKernelMap_surjective
#print axioms OAI.KLInvariance.ReflectionPairTranslation.tensorFirst_map
#print axioms OAI.KLInvariance.ReflectionPairTranslation.tensorSecond_map
#print axioms OAI.KLInvariance.ReflectionPairTranslation.tensor_difference
#print axioms OAI.KLInvariance.ReflectionPairTranslation.twistMap_injective
#print axioms OAI.KLInvariance.Graded.ModuleData.rangeMap_projection
