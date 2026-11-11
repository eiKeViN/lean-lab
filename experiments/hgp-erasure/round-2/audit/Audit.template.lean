import Lean
import Toy
open Lean Elab Command
run_cmd do
  let env ← getEnv
  for moduleName in [`Toy] do
    let some idx := env.getModuleIdx? moduleName | throwError "absent module {moduleName}"
    for name in env.header.moduleData[idx.toNat]!.constNames do
      unless name.isInternalOrNum do
        let some c := env.find? name | continue
        let axioms ← collectAxioms name
        let type ← liftTermElabM <| Meta.ppExpr c.type
        let row := Json.mkObj [("module", toJson moduleName.toString), ("name", toJson name.toString),
          ("type", toJson type.pretty), ("axioms", toJson (axioms.map Name.toString))]
        IO.println ("AUDIT " ++ row.compress)
