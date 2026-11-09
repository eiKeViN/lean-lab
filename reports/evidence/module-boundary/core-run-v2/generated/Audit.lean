import Realizer
open Lean Meta Elab Command
run_elab do
  for n in [``Boundary.legacy, ``Boundary.modern, `Boundary.legacy.eq_1, `Boundary.modern.eq_1] do
    let env ← getEnv
    let owner := (env.getModuleIdxFor? n).map fun i => env.header.moduleNames[i.toNat]!
    logInfo m!"{n}: owner={owner}"
