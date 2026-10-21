import ForMathlib.Algebra.Polynomial.ScaledEvaluation
import Lean

-- The precise polynomial entrypoint must not bring in weighted-sum helpers.
run_elab do
  let env ← Lean.getEnv
  let localModules := env.header.moduleNames.filter fun n =>
    n.toString.startsWith "ForMathlib." || n.toString.startsWith "OAI."
  unless localModules == #[`ForMathlib.Algebra.Polynomial.Reciprocal,
      `ForMathlib.Algebra.Polynomial.ScaledEvaluation] do
    throwError "Unexpected scaled-evaluation dependency: {localModules}"
  unless env.contains `OAI.KLInvariance.Comparison.eq_of_scaled_difference_reciprocal do
    throwError "Missing preserved polynomial declaration"
  for n in #[`OAI.KLInvariance.finite_character_cancellation,
      `OAI.KLInvariance.Comparison.matrix_difference_single] do
    if env.contains n then throwError "Unrelated weighted-sum declaration imported: {n}"
