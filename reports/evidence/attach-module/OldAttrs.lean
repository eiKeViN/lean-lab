import ForMathlib.Combinatorics.MomentGraph.Sheaf.Basic
import Lean
open Lean Meta Elab Command
run_elab do
  let some eqs ← getEqnsFor? ``OAI.KLInvariance.MomentGraph.Sheaf.stalkMap | throwError "missing equation"
  let n := eqs[0]!
  let env ← getEnv
  logInfo m!"old attrs: defeq={defeqAttr.hasTag env n}, backward_defeq={backwardDefeqAttr.hasTag env n}"
