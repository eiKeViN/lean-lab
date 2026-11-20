/-
Copyright (c) 2026 Kevin Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Zhao
-/
import Giallar
import Lean
import Lean.Util.CollectAxioms

/-!
# Public-environment axiom audit

Enumerate every exported constant owned by a `Giallar` module, including generated declarations.
For each constant, collect transitive axioms using Lean's own `collectAxioms` implementation.
Only `propext`, `Classical.choice`, and `Quot.sound` are allowed. Local axioms and user-written
unsafe or partial definitions are rejected independently of their use. Lean-generated recursive
runtime helpers are inventoried separately, with their safe parent and recursion metadata checked.

The JSON output also retains pretty-printed public types for semantic review. This audits the
elaborated imported environment, not text excerpts or a hard-coded list of headline theorems.
-/

open Lean Elab Command

private def auditedModule (n : Name) : Bool :=
  n == `Giallar || n.toString.startsWith "Giallar."

private def constantKind : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

/-- Recognize the compiler's partial implementation of a kernel-checked recursive definition.
The name alone is insufficient: parent safety, recursion metadata, module, type, and universes
must agree. The Python driver independently rejects explicit helper names and compiler hooks
in project source, so a user-written unsafe definition cannot obtain this exemption. -/
private def compilerHelperFor? (env : Environment) (n : Name)
    (info : ConstantInfo) : Option Name := do
  guard info.isPartial
  let parent ← Compiler.isUnsafeRecName? n
  let parentInfo ← env.find? parent
  guard (!parentInfo.isUnsafe && !parentInfo.isPartial)
  guard (Meta.recExt.isTagged env parent)
  guard (env.getModuleIdxFor? n == env.getModuleIdxFor? parent)
  guard (info.type == parentInfo.type && info.levelParams == parentInfo.levelParams)
  return parent

elab "#audit_giallar" : command => do
  let env ← getEnv
  let modules := env.allImportedModuleNames.filter auditedModule
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let constants := env.constants.toList.toArray.qsort fun a b => Name.quickLt a.1 b.1
  let mut records : Array Json := #[]
  let mut rejected : Array String := #[]
  let mut helperCount := 0
  for (n, info) in constants do
    let some idx := env.getModuleIdxFor? n | continue
    let modName := env.allImportedModuleNames[idx.toNat]!
    unless auditedModule modName do continue
    let axioms ← collectAxioms n
    let forbidden := axioms.filter fun a => !allowed.contains a
    if !forbidden.isEmpty then
      rejected := rejected.push s!"{n}: forbidden axioms {forbidden}"
    let helperFor := compilerHelperFor? env n info
    if helperFor.isSome then helperCount := helperCount + 1
    if (info.isUnsafe || info.isPartial) && helperFor.isNone then
      rejected := rejected.push s!"{n}: unrecognized unsafe or partial declaration"
    if let .axiomInfo _ := info then
      rejected := rejected.push s!"{n}: local axiom declaration"
    let typeText ← liftTermElabM do
      return (← Meta.ppExpr info.type).pretty
    records := records.push <| Json.mkObj [
      ("name", toJson n.toString),
      ("module", toJson modName.toString),
      ("kind", toJson (constantKind info)),
      ("type", toJson typeText),
      ("axioms", toJson (axioms.map Name.toString)),
      ("unsafe", toJson info.isUnsafe),
      ("partial", toJson info.isPartial),
      ("compiler_helper_for", toJson (helperFor.map Name.toString)),
      ("logical_declaration", toJson helperFor.isNone)]
  if records.isEmpty then throwError "Axiom audit selected no project declarations"
  let output := Json.mkObj [
    ("status", toJson (if rejected.isEmpty then "PASS" else "FAIL")),
    ("method", toJson "Lean.collectAxioms over every exported project-module constant"),
    ("allowed_axioms", toJson (allowed.map Name.toString)),
    ("audited_modules", toJson (modules.map Name.toString)),
    ("declaration_count", toJson records.size),
    ("safe_logical_declaration_count", toJson (records.size - helperCount)),
    ("generated_runtime_helper_count", toJson helperCount),
    ("rejected", toJson rejected),
    ("declarations", toJson records)]
  liftIO <| IO.FS.createDirAll "evidence"
  liftIO <| IO.FS.writeFile "evidence/axioms.json" (output.pretty ++ "\n")
  unless rejected.isEmpty do
    throwError "Axiom audit rejected {rejected.size} declaration checks: {rejected}"
  logInfo m!"Audited {records.size - helperCount} logical declarations; axioms accepted"
  logInfo m!"Inventoried {helperCount} generated runtime helpers in {modules.size} modules"

#audit_giallar
