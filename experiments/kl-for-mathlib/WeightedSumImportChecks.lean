import ForMathlib.Algebra.BigOperators.SingleCoordinate
import Lean

-- Weighted finite-sum facts need neither the owned polynomial theory nor KL models.
run_elab do
  let env ← Lean.getEnv
  let localModules := env.header.moduleNames.filter fun n =>
    n.toString.startsWith "ForMathlib." || n.toString.startsWith "OAI."
  unless localModules == #[`ForMathlib.Algebra.BigOperators.SingleCoordinate] do
    throwError "Unexpected weighted-sum dependency: {localModules}"
  for n in #[`OAI.KLInvariance.finite_character_cancellation,
      `OAI.KLInvariance.Comparison.matrix_difference_single,
      `OAI.KLInvariance.Comparison.matrix_difference_le] do
    unless env.contains n do throwError "Missing preserved declaration: {n}"
