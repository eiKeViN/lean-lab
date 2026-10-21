import OAI.KL
import Lean

run_elab do
  let env ← Lean.getEnv
  unless env.contains `OAI.KLInvariance.combinatorial_invariance do
    throwError "KL entrypoint does not expose the main theorem"
  for n in env.header.moduleNames do
    if n.toString.startsWith "OAI.RepresentationTheory." ||
       n == `OAI.Architecture || n == `ForMathlib then
      throwError "Project entrypoint depends on a legacy/all-library umbrella: {n}"
