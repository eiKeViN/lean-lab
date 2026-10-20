import OAI.Architecture
import Lean

open Lean

structure TypeDumpState where
  ids : ExprStructMap Nat := {}
  proofIds : ExprStructMap Nat := {}
  next : Nat := 0
  privateOwners : Std.HashMap Name Name := {}
  proofAliases : NameHashSet := {}

-- Alpha equivalence ignores binder display names. Only compiler-private OAI
-- owner prefixes are erased from constant names; their user names stay exact.
-- There are no duplicate private user names in the pinned source.
private def canonicalConstant (n : Name) : Name :=
  if n.toString.startsWith "_private.OAI." then
    (privateToUserName? n).getD n
  else n

-- Keep every mathematical expression constructor, universe, binder info,
-- constant, application and de Bruijn index. Metadata and binder display names
-- have no effect on the mathematical type. A local compiler theorem auxiliary
-- is represented by its full proposition, using kernel proof irrelevance.
-- No proof body, general definition, data instance or user theorem is unfolded.
partial def dumpType (env : Environment) (out : IO.FS.Handle) (e : Expr)
    (proofContext := false) : StateT TypeDumpState IO Nat := do
  let cached : TypeDumpState ← get
  let cache := if proofContext then cached.proofIds else cached.ids
  if let some id := cache[ExprStructEq.mk e]? then return id
  if let .mdata _ body := e then return ← dumpType env out body proofContext
  let fields ← match e with
    | .bvar i => pure ["bvar", toString i]
    | .sort u => pure ["sort", reprStr u]
    | .const n us =>
      let proofName := match n with
        | .str _ s => s.startsWith "_proof_"
        | _ => false
      if n.isInternal && n.toString.startsWith "OAI." && proofName then
        if let some (.thmInfo info) := env.find? n then
          -- Kernel theorem declarations prove propositions. Their full
          -- proposition, including parameters, is retained; only its binder
          -- display/implicitness metadata is irrelevant to the proof value.
          let proposition ← dumpType env out (info.type.instantiateLevelParams info.levelParams us) true
          modify fun st => { st with proofAliases := st.proofAliases.insert n }
          pure ["proof", toString proposition]
        else pure ["const", reprStr n, reprStr us]
      else
        let canonical := canonicalConstant n
        if canonical != n then
          if let some previous := (← get).privateOwners[canonical]? then
            if previous != n then throw <| IO.userError "Ambiguous private type constant"
          modify fun st => { st with privateOwners := st.privateOwners.insert canonical n }
        pure ["const", reprStr canonical, reprStr us]
    | .app f a => do
      let f ← dumpType env out f proofContext; let a ← dumpType env out a proofContext
      pure ["app", toString f, toString a]
    | .lam _ t b bi | .forallE _ t b bi => do
      let t ← dumpType env out t proofContext; let b ← dumpType env out b proofContext
      pure [if e.isLambda then "lam" else "forall", "_", if proofContext then "kernel" else reprStr bi, toString t, toString b]
    | .letE _ t v b nondep => do
      let t ← dumpType env out t proofContext; let v ← dumpType env out v proofContext; let b ← dumpType env out b proofContext
      pure ["let", "_", toString t, toString v, toString b, toString nondep]
    | .lit v => pure ["lit", reprStr v]
    | .proj n i b => do
      let b ← dumpType env out b proofContext
      pure ["proj", reprStr n, toString i, toString b]
    | .fvar _ | .mvar _ => throw <| IO.userError "Non-closed declaration type"
    | .mdata _ _ => unreachable!
  let state : TypeDumpState ← get
  if proofContext then
    set { state with proofIds := state.proofIds.insert (ExprStructEq.mk e) state.next, next := state.next+1 }
  else
    set { state with ids := state.ids.insert (ExprStructEq.mk e) state.next, next := state.next+1 }
  out.putStrLn s!"NODE\t{state.next}\t{(toJson fields).compress}"
  return state.next

private def declarationKind : ConstantInfo → String
  | .axiomInfo _ => "axiom" | .defnInfo _ => "def"
  | .thmInfo _ => "theorem" | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient" | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor" | .recInfo _ => "recursor"

run_elab do
  let env ← getEnv
  let some path ← IO.getEnv "LEAN_TYPES_OUT" | throwError "Set LEAN_TYPES_OUT"
  let out ← IO.FS.Handle.mk (System.FilePath.mk path) .write
  let action : StateT TypeDumpState IO Unit := do
    let mut seen : Std.HashMap Name ConstantInfo := {}
    let mut duplicates := 0
    for idx in [:env.header.moduleData.size] do
      let moduleName := env.header.moduleNames[idx]!
      if moduleName.toString.startsWith "OAI." then
        for info in env.header.moduleData[idx]!.constants do
          if !isPrivateName info.name && !info.name.isInternal then
            if let some previous := seen[info.name]? then
              -- A lazy equation can be serialized by two import branches.
              -- Check the complete duplicate record; never silently discard it.
              unless info.type == previous.type && info.levelParams == previous.levelParams &&
                  declarationKind info == declarationKind previous && info.value? true == previous.value? true do
                throw <| IO.userError s!"Conflicting serialized declaration: {info.name}"
              duplicates := duplicates + 1
              out.putStrLn s!"SERIALIZED_COPY\t{info.name}\t{moduleName}"
              continue
            seen := seen.insert info.name info
            let some actual := env.find? info.name | throw <| IO.userError "Missing global declaration"
            let some owner := env.getModuleIdxFor? info.name | throw <| IO.userError "Missing global owner"
            out.putStrLn s!"MODULE\t{env.header.moduleNames[owner.toNat]!}"
            let id ← dumpType env out actual.type
            out.putStrLn s!"TYPE\t{actual.name}\t{(toJson (reprStr actual.levelParams)).compress}\t{id}\t{declarationKind actual}"
    for n in (← get).proofAliases.toArray do out.putStrLn s!"PROOF_ALIAS\t{n}"
    out.putStrLn s!"SUMMARY\t{seen.size}\t{duplicates}\t{(← get).proofAliases.size}"
  discard <| action.run {}
  out.flush
  IO.println "Unique global public types exported with checked serialization copies and compiler-proof propositions."
