import ImplementationImports
import Lean

open Lean

-- Retrieval metadata only; PublicTypes.lean remains the separate type authority.
run_elab do
  let env ← getEnv
  let some path ← IO.getEnv "SEMANTIC_CORPUS_OUT" | throwError "Set SEMANTIC_CORPUS_OUT"
  let mut seen : NameHashSet := {}
  let mut rows : Array Json := #[]
  for idx in [:env.header.moduleData.size] do
    let owner := env.header.moduleNames[idx]!
    if owner.toString.startsWith "OAI." || owner.toString.startsWith "ForMathlib." then
      for info in env.header.moduleData[idx]!.constants do
        if !isPrivateName info.name && !info.name.isInternal && !seen.contains info.name then
          seen := seen.insert info.name
          if let some (.thmInfo _) := env.find? info.name then
            let doc ← findDocString? env info.name
            rows := rows.push (Json.mkObj [("name", toJson info.name.toString),
              ("module", toJson owner.toString), ("doc", toJson (doc.getD ""))])
  IO.FS.writeFile path ((Json.mkObj [("schema", toJson (1 : Nat)),
    ("count", toJson rows.size), ("records", toJson rows)]).pretty ++ "\n")
  IO.println s!"Exported {rows.size} owned public theorem retrieval records."
