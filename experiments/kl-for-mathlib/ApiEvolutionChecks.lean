module
import ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Uniqueness
import ForMathlib.Combinatorics.MomentGraph.Sheaf.Structure
import Lean
open Lean Elab Command OAI.KLInvariance
run_elab do
  for n in #[`OAI.KLInvariance.CoefficientChange.map,
      `OAI.KLInvariance.CoefficientChange.mapEquiv,
      `OAI.KLInvariance.Graded.ModuleData.changeHom,
      `OAI.KLInvariance.MomentGraph.GradedSheaf.coefficientChangeSections,
      `OAI.KLInvariance.MomentGraph.Sheaf.quotientPullback] do
    unless (← getEnv).find? n |>.any (fun ci => ci.hasValue) do
      throwError "Lost an exposed computation interface: {n}"
  logInfo "API evolution: all selected interfaces retain exposed bodies."
section
variable {k A B M N P : Type*} [Field k] [CommRing A] [CommRing B]
  [Algebra k A] [Algebra k B] [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
  [Module A M] [Module A N] [Module A P]
  [Module k M] [Module k N] [Module k P]
  [IsScalarTower k A M] [IsScalarTower k A N] [IsScalarTower k A P]
example (e : A ≃ₐ[k] B) (f : M ≃ₗ[A] N) (g : N ≃ₗ[A] P)
    (m : CoefficientChange e M) :
    (CoefficientChange.mapEquiv e (f.trans g) m).val =
      (CoefficientChange.mapEquiv e g (CoefficientChange.mapEquiv e f m)).val := by simp
end
#print axioms OAI.KLInvariance.CoefficientChange.val_zero
#print axioms OAI.KLInvariance.CoefficientChange.val_smul
#print axioms OAI.KLInvariance.CoefficientChange.val_mapEquiv
#print axioms OAI.KLInvariance.Graded.ModuleData.val_changeHom
#print axioms OAI.KLInvariance.MomentGraph.GradedSheaf.coefficientChange_lower_val
#print axioms OAI.KLInvariance.MomentGraph.GradedSheaf.coefficientChange_upper_val
#print axioms OAI.KLInvariance.MomentGraph.GradedSheaf.coefficientChange_compatibleOn_iff
#print axioms OAI.KLInvariance.MomentGraph.GradedSheaf.coefficientChangeSections_symm_val_apply
#print axioms OAI.KLInvariance.MomentGraph.GradedSheaf.PerfectPairing.coefficientChange_apply
#print axioms OAI.KLInvariance.MomentGraph.GradedSheaf.Hom.coefficientChange
#print axioms OAI.KLInvariance.MomentGraph.GradedSheaf.coefficientChange_upperQuotient
#print axioms OAI.KLInvariance.MomentGraph.GradedSheaf.coefficientChange_flabby
#print axioms OAI.KLInvariance.MomentGraph.GradedSheaf.coefficientChange_generated
#print axioms OAI.KLInvariance.MomentGraph.GradedSheaf.coefficientChangeSections
#print axioms OAI.KLInvariance.MomentGraph.GradedSheaf.PerfectPairing.coefficientChange
#print axioms OAI.KLInvariance.MomentGraph.GradedSheaf.SymmetricPerfectPairing.coefficientChange
#print axioms OAI.KLInvariance.CoefficientChange.pairingEquiv_apply
