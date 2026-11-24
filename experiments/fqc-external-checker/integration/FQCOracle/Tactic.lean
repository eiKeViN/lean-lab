module
public meta import Lean
public meta import Lean.Meta.Native
public meta import Lean.Compiler.Options
public meta import FQCOracle.Policy
public meta import Audit.Export

/- Named outside-kernel evaluation. Stock Lean nativeEqTrue performs evaluation;
its temporary axiom is discarded. Only the explicitly named axiom is retained.
The ordinary kernel checks all subsequent uses of that assumption. -/
public meta section
namespace FQCOracle
open Lean Meta Elab Tactic

def canonicalText (e : Expr) : String := reprStr (FQCAudit.canonical e)

def checkDependencies (e : Expr) : MetaM (Array Name) := do
  let mut result : Array Name := #[]
  for name in e.getUsedConstants do
    for ax in ← collectAxioms name do
      unless Policy.allowed ax do
        throwError "Unapproved axiom in external decision procedure: {ax}"
      if !result.contains ax then result := result.push ax
  return result.qsort Name.lt

def evalOnly (e : Expr) : MetaM Bool := withoutModifyingEnv do
  match ← nativeEqTrue `FQCOracleEvaluation e with
  | .success _ => return true
  | .notTrue => return false

def record (name : Name) (goal decision axType : Expr) (deps : Array Name)
    (path : System.FilePath := "../results/full/oracle") : MetaM Unit := do
  let some site := Policy.sites.find? (·.name == name)
    | throwError "Unregistered external goal: {name}"
  liftM <| IO.FS.createDirAll path
  let text ← withOptions (fun opts => opts.setBool `pp.fullNames true |>.setBool `pp.proofs true) do
    return (← ppExpr goal).pretty
  let payload := Json.mkObj [
    ("name", toJson name.toString), ("module", toJson site.owner),
    ("source_sha256", toJson site.source), ("source_line", toJson site.line),
    ("goal", toJson text), ("goal_expr", toJson (canonicalText goal)),
    ("decision_expr", toJson (canonicalText decision)),
    ("axiom_type_expr", toJson (canonicalText axType)),
    ("decision_axioms", toJson (deps.map Name.toString)),
    ("accepted", toJson true),
    ("method", toJson "Lean nativeEqTrue evaluation; named axiom, not kernel reduction")]
  liftM <| IO.FS.writeFile (path / (name.toString ++ ".json")) payload.pretty

elab "fqc_checked " key:ident : tactic => withMainContext do
  let name := key.getId
  unless Policy.sites.any (·.name == name) do throwError "Unregistered external source site {name}"
  let goal ← getMainGoal
  let ty ← instantiateMVars (← goal.getType)
  if ty.hasFVar || ty.hasMVar then throwError "External checking requires a closed goal"
  let d ← mkDecide ty
  let deps ← checkDependencies d
  let levels := (collectLevelParams {} d).params.toList
  let valueName := name ++ `value
  let levelArgs := levels.map mkLevelParam
  let boolType := mkConst ``Bool
  if (← getEnv).contains valueName then
    throwError "Source site elaborated more than once: {name}"
  withOptions (Elab.async.set · false) do
  withOptions (Compiler.compiler.postponeCompile.set · false) do
    addAndCompile <| .defnDecl {
      name := valueName
      levelParams := levels
      type := boolType
      value := d
      hints := .abbrev
      safety := .safe }
  unless ← evalOnly (mkConst valueName levelArgs) do
    throwError "External decision procedure returned false at {name}"
  let axType ← mkEq d (mkConst ``Bool.true)
  addDecl <| .axiomDecl {
    name := name
    levelParams := levels
    type := axType
    isUnsafe := false }
  let equationName := name ++ `definition
  let equationType ← mkEq (mkConst valueName levelArgs) d
  addDecl <| .thmDecl {
    name := equationName
    levelParams := levels
    type := equationType
    value := ← mkEqRefl d }
  record name ty d axType deps
  goal.assign <| mkApp3 (mkConst ``of_decide_eq_true) ty d.appArg! (mkConst name levelArgs)
  replaceMainGoal []

/-- Freshly rerun the exported decisions; their axiom types remain independently auditable. -/
def replay : Command.CommandElabM Unit := Command.runTermElabM fun _ => do
  for site in Policy.sites do
    let env ← getEnv
    let some info := env.find? site.name | throwError "Missing external source site {site.name}"
    unless info matches .axiomInfo _ do throwError "Expected named axiom {site.name}"
    let args := info.type.getAppArgs
    unless info.type.isAppOfArity ``Eq 3 && args[0]!.isConstOf ``Bool && args[2]!.isConstOf ``Bool.true do
      throwError "Malformed external axiom {site.name}"
    let d := args[1]!
    let eqInfo ← getConstInfo (site.name ++ `definition)
    let eqArgs := eqInfo.type.getAppArgs
    unless eqInfo.type.isAppOfArity ``Eq 3 && canonicalText eqArgs[2]! == canonicalText d do
      throwError "External decision definition mismatch {site.name}"
    let deps ← checkDependencies d
    let value ← getConstInfo (site.name ++ `value)
    let levels := value.levelParams.map mkLevelParam
    unless ← evalOnly (mkConst value.name levels) do throwError "External replay rejected {site.name}"
    let ty := d.appFn!.appArg!
    record site.name ty d info.type deps "../results/full/oracle-replay"

end FQCOracle
