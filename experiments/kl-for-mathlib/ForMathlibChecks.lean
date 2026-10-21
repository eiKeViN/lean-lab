import ForMathlib
import Lean

-- This is the staging boundary: declaration namespaces remain compatible,
-- but no imported module may come from the project's OAI implementation layer.
run_elab do
  let env ← Lean.getEnv
  for n in env.header.moduleNames do
    if n.toString.startsWith "OAI." then
      throwError "ForMathlib imports a project module: {n}"
  for n in #[`OAI.LinearEquiv.kernelSourceEquiv,
      `OAI.KLInvariance.CoxeterSupport.reflectionAction,
      `OAI.KLInvariance.bruhat_iff_reduced_subword,
      `OAI.KLInvariance.klPolynomial,
      `OAI.KLInvariance.SignedDihedral.arrowAfter_pair] do
    unless env.contains n do throwError "Missing staged API: {n}"
