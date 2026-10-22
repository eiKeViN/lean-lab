module
import ForMathlib.Algebra.Module.Flat.Kernel
import ForMathlib.Algebra.Module.Localization.Membership
import ForMathlib.Algebra.Module.Projective.ReverseFiltration
import ForMathlib.Algebra.Module.Quotient.KernelReduction
import ForMathlib.Algebra.Module.Submodule.ProductScaling
import ForMathlib.Algebra.Polynomial.LowPart
import ForMathlib.LinearAlgebra.Dual.BalancedCut
import ForMathlib.LinearAlgebra.PlaneReduction
import Lean
open scoped BigOperators
example (d : ℕ) (p : Polynomial ℤ) :
    OAI.KLInvariance.CanonicalP.lowPart d p =
      ∑ n ∈ Finset.range ((d + 1) / 2), Polynomial.monomial n (p.coeff n) := rfl
run_elab do
  let env ← Lean.getEnv
  for n in #[`OAI.KLInvariance.FlatSubmodule.baseChange_map, `OAI.KLInvariance.FlatSubmodule.baseChange_ker, `OAI.KLInvariance.TensorLocalMembership.denominator, `OAI.KLInvariance.TensorLocalMembership.baseChange_eq_localized, `OAI.KLInvariance.ReverseFiltration.kernel_projective_of_presentation, `OAI.KLInvariance.EdgeImage.reducedInclusion, `OAI.KLInvariance.EdgeImage.reduced_kernel_injective, `OAI.KLInvariance.EdgeImage.range_reducedInclusion_free, `OAI.KLInvariance.EdgeImage.kernel_saturated, `OAI.KLInvariance.LocalProducts.associated_prod_power, `OAI.KLInvariance.LocalProducts.smul_top_le_of_map_dvd, `OAI.KLInvariance.LocalProducts.product_image_scale, `OAI.KLInvariance.LocalProducts.associated_prod_scale, `OAI.KLInvariance.LocalProducts.smul_top_eq_of_map_associated, `OAI.KLInvariance.CanonicalP.coeff_lowPart, `OAI.KLInvariance.CanonicalP.lowPart.eq_1, `OAI.KLInvariance.CanonicalP.lowPart_solution, `OAI.KLInvariance.CanonicalP.lowPart, `OAI.KLInvariance.CanonicalP.lowPart_degree, `OAI.BalancedCuts.balanced, `OAI.BalancedCuts.balanced_two, `OAI.KLInvariance.PlaneReduction.associated_reduction, `OAI.KLInvariance.PlaneReduction.scalar_reduction] do
    unless env.contains n do throwError "Missing focused owned API: {n}"
  if env.contains `MeasureTheory.integral_const then
    throwError "Unexpected unrelated Mathlib re-export"
  IO.println "Eight focused imports: owned declarations and lowPart rfl preserved; unrelated integral_const absent."
