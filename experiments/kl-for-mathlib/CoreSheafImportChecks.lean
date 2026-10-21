import ForMathlib.Combinatorics.MomentGraph.Sheaf.ScaledImages
import ForMathlib.Combinatorics.MomentGraph.Sheaf.FlowDown
import ForMathlib.Combinatorics.MomentGraph.Sheaf.Products
import ForMathlib.Combinatorics.MomentGraph.Sheaf.Duality
import Lean

-- The complete current ordinary-sheaf layer needs no graded sheaf or model.
run_elab do
  let env ← Lean.getEnv
  for n in env.header.moduleNames do
    let s := n.toString
    if s.startsWith "OAI." || s.startsWith "ForMathlib.GroupTheory." ||
       s.startsWith "ForMathlib.RepresentationTheory." ||
       s.startsWith "ForMathlib.Algebra.Module.Graded." ||
       s.startsWith "ForMathlib.Combinatorics.MomentGraph.GradedSheaf." ||
       s.startsWith "ForMathlib.Combinatorics.MomentGraph.Boundary." then
      throwError "Ordinary sheaf support imports a graded/model layer: {n}"
  for n in #[`OAI.KLInvariance.MomentGraph.Sheaf.Iso,
      `OAI.KLInvariance.MomentGraph.Sheaf.baseChange,
      `OAI.KLInvariance.MomentGraph.Sheaf.structureSheaf,
      `OAI.KLInvariance.MomentGraph.Sheaf.restrict,
      `OAI.KLInvariance.MomentGraph.Sheaf.pullback,
      `OAI.KLInvariance.MomentGraph.Sheaf.pi,
      `OAI.KLInvariance.LocalCover.pi_mem_ideal_smul] do
    unless env.contains n do throwError "Missing ordinary sheaf declaration: {n}"
