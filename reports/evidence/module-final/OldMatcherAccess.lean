import ForMathlib.Algebra.Module.CoefficientChange.Basic
import ForMathlib.Algebra.Module.Cover.Local
import ForMathlib.Algebra.Algebra.ReflectionFrobenius.Basis
import ForMathlib.Algebra.Module.ReflectionPair.Twist
import ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Properties
import ForMathlib.GroupTheory.Coxeter.Roots.ReflectionOrder
import Lean
open Lean
run_elab do
  let names : Array Name := #[`OAI.KLInvariance.CoefficientChange.ext.match_1, `OAI.KLInvariance.LocalCover.splitEquiv.match_3, `OAI.KLInvariance.MomentGraph.GradedSheaf.extendBottom_upperQuotient.match_1_1, `OAI.KLInvariance.MomentGraph.GradedSheaf.extendBottom_upperQuotient.match_1_3, `OAI.KLInvariance.ReflectionFrobenius.wallCoordinate_injective.match_1_2, `OAI.KLInvariance.ReflectionFrobenius.wallMatrix_mulVec.match_1_1, `OAI.KLInvariance.ReflectionPairTranslation.Twist.ext.match_1, `OAI.KLInvariance.TitsSpace.exists_common_transverse.match_1_1, `OAI.KLInvariance.LocalCover.splitEquiv.match_6]
  for n in names do
    try
      let actual ← realizeGlobalConstNoOverload (mkIdent n)
      logInfo m!"RESOLVED {n} => {actual}"
    catch _ => logInfo m!"UNAVAILABLE {n}"
