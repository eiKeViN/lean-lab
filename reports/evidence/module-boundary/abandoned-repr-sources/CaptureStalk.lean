import ForMathlib.Combinatorics.MomentGraph.Sheaf.Basic
import Lean
open Lean Meta Elab Command
run_elab do
  let name := ``OAI.KLInvariance.MomentGraph.Sheaf.stalkMap
  let some eqs ← getEqnsFor? name | throwError "no equation"
  let eq := eqs[0]!
  unless eq == `OAI.KLInvariance.MomentGraph.Sheaf.stalkMap.eq_1 do throwError "unexpected equation name"
  let type := (← getConstInfo eq).type
  let some out ← IO.getEnv "STALK_EXPR_OUT" | throwError "STALK_EXPR_OUT missing"
  let some label ← IO.getEnv "STALK_EXPR_LABEL" | throwError "STALK_EXPR_LABEL missing"
  let mut aux : Array (Name × List Name × Expr × Expr) := #[]
  for n in type.getUsedConstants do
    if name.isPrefixOf n && n != name then
      let .thmInfo info ← getConstInfo n | throwError "non-theorem auxiliary {n}"
      aux := aux.push (n, info.levelParams, info.type, info.value)
  let payload := s!"def {label}Aux : Array (Lean.Name × List Lean.Name × Lean.Expr × Lean.Expr) :=\n{reprStr aux}\n"
  IO.FS.writeFile (out ++ ".aux") payload
  IO.FS.writeFile out s!"def {label} : Lean.Expr :=\n{reprStr type}\n"
  logInfo m!"captured {eq} into {out}"
