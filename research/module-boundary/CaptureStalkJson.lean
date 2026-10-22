import ForMathlib.Combinatorics.MomentGraph.Sheaf.Basic
import StalkCodec
open Lean Meta Elab Command BoundaryCodec
run_elab do
  let name := ``OAI.KLInvariance.MomentGraph.Sheaf.stalkMap
  let some eqs ← getEqnsFor? name | throwError "no equation"
  unless eqs[0]! == `OAI.KLInvariance.MomentGraph.Sheaf.stalkMap.eq_1 do throwError "unexpected equation"
  let type := (← getConstInfo eqs[0]!).type
  let mut aux : Array (Name × List Name × Expr × Expr) := #[]
  for n in type.getUsedConstants do
    if name.isPrefixOf n && n != name then
      let .thmInfo info ← getConstInfo n | throwError "non-theorem auxiliary {n}"
      aux := aux.push (n, info.levelParams, info.type, info.value)
  let action : StateM Dump Json := do
    let t ← encode type
    let mut records := #[]
    for (n, us, ty, val) in aux do
      records := records.push (toJson (#[nameJson n, toJson (us.map nameJson), toJson (← encode ty), toJson (← encode val)]))
    return Json.mkObj [("type", toJson t), ("aux", toJson records), ("nodes", toJson (← get).nodes)]
  let (obj, _) := action.run {}
  let decoded ← ofExcept (decode (← ofExcept (obj.getObjValAs? (Array Json) "nodes")))
  let ti : Nat ← ofExcept (obj.getObjValAs? Nat "type")
  unless ← isDefEq type decoded[ti]! do throwError "codec roundtrip failed"
  let some out ← IO.getEnv "STALK_JSON_OUT" | throwError "STALK_JSON_OUT missing"
  IO.FS.writeFile out obj.compress
  logInfo m!"captured {eqs[0]!}: {decoded.size} DAG nodes; codec roundtrip passes"
