import ForMathlib.Algebra.Polynomial.ScaledReciprocity
import ForMathlib.Algebra.BigOperators.FiniteCharacterCancellation
import ForMathlib.Algebra.Module.Localization.Products
import Lean

-- Published entrypoints remain usable; they now forward to precise implementations.
run_elab do
  let env ← Lean.getEnv
  for n in #[`OAI.KLInvariance.Comparison.scaledPolynomial,
      `OAI.KLInvariance.Comparison.eq_of_scaled_difference_reciprocal,
      `OAI.KLInvariance.Comparison.matrix_difference_single,
      `OAI.KLInvariance.Comparison.matrix_difference_le,
      `OAI.KLInvariance.finite_character_cancellation,
      `OAI.KLInvariance.LocalProducts.product_image_scale] do
    unless env.contains n do throwError "Compatibility entry lost a declaration: {n}"
