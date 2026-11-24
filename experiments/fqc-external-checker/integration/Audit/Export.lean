module
public import Lean

/- Compare elaborated public types in separate processes. Ignore binder names
and metadata, but retain constants, universes, binder kinds and expression shape. -/
@[expose] public section
namespace FQCAudit
open Lean Elab Command

partial def canonical : Expr → Expr
  | .mdata _ e => canonical e
  | .forallE _ a b kind => .forallE .anonymous (canonical a) (canonical b) kind
  | .lam _ a b kind => .lam .anonymous (canonical a) (canonical b) kind
  | .letE _ a v b nondep => .letE .anonymous (canonical a) (canonical v) (canonical b) nondep
  | .app a b => .app (canonical a) (canonical b)
  | .proj n i e => .proj n i (canonical e)
  | e => e

def exportTypes (path : System.FilePath) : CommandElabM Unit := do
  let env ← getEnv
  let names := [`QuantumComputation.Specs.photochemistryAncillas,
    `QuantumComputation.Specs.photochemistryProgram,
    `QuantumComputation.Specs.photochemistryConstCost,
    `QuantumComputation.Specs.photochemistry_correctness,
    `QuantumComputation.Specs.photochemistry_const_cost]
  let mut fields := #[]
  for name in names do
    let some info := env.find? name | throwError "Missing public declaration {name}"
    fields := fields.push (name.toString, Json.str (reprStr (canonical info.type)))
  liftIO <| IO.FS.writeFile path (Json.pretty (Json.mkObj fields.toList))

end FQCAudit
