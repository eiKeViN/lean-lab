import OAI.Architecture
import Lean

open Lean

structure TypeDumpState where
  ids : ExprStructMap Nat := {}
  next : Nat := 0

-- Alpha equivalence ignores binder display names. Only compiler-private OAI
-- owner prefixes are erased from constant names; their user names stay exact.
-- There are no duplicate private user names in the pinned source.
private def canonicalConstant (n : Name) : Name :=
  if n.toString.startsWith "_private.OAI." then
    (privateToUserName? n).getD n
  else n

-- Keep every mathematical expression constructor, universe, binder info,
-- constant, application and de Bruijn index. Metadata and binder display names
-- have no effect on the mathematical type. Do not reduce or unfold types.
partial def dumpType (out : IO.FS.Handle) (e : Expr) : StateT TypeDumpState IO Nat := do
  let cached : TypeDumpState ← get
  if let some id := cached.ids[ExprStructEq.mk e]? then return id
  if let .mdata _ body := e then return ← dumpType out body
  let fields ← match e with
    | .bvar i => pure ["bvar", toString i]
    | .sort u => pure ["sort", reprStr u]
    | .const n us => pure ["const", reprStr (canonicalConstant n), reprStr us]
    | .app f a => do
      let f ← dumpType out f; let a ← dumpType out a
      pure ["app", toString f, toString a]
    | .lam n t b bi | .forallE n t b bi => do
      let t ← dumpType out t; let b ← dumpType out b
      pure [if e.isLambda then "lam" else "forall", "_", reprStr bi, toString t, toString b]
    | .letE n t v b nondep => do
      let t ← dumpType out t; let v ← dumpType out v; let b ← dumpType out b
      pure ["let", "_", toString t, toString v, toString b, toString nondep]
    | .lit v => pure ["lit", reprStr v]
    | .proj n i b => do
      let b ← dumpType out b
      pure ["proj", reprStr n, toString i, toString b]
    | .fvar _ | .mvar _ => throw <| IO.userError "Non-closed declaration type"
    | .mdata _ _ => unreachable!
  let state : TypeDumpState ← get
  set (TypeDumpState.mk (state.ids.insert (ExprStructEq.mk e) state.next) (state.next+1))
  out.putStrLn s!"NODE\t{state.next}\t{(toJson fields).compress}"
  return state.next

run_elab do
  let env ← getEnv
  let some path ← IO.getEnv "LEAN_TYPES_OUT" | throwError "Set LEAN_TYPES_OUT"
  let out ← IO.FS.Handle.mk (System.FilePath.mk path) .write
  let action : StateT TypeDumpState IO Unit := do
    for idx in [:env.header.moduleData.size] do
      let moduleName := env.header.moduleNames[idx]!
      if moduleName.toString.startsWith "OAI." then
        out.putStrLn s!"MODULE\t{moduleName}"
        let mut privateCount := 0
        let mut internalCount := 0
        for info in env.header.moduleData[idx]!.constants do
          if !isPrivateName info.name && !info.name.isInternal then
            let kind := match info with
              | .axiomInfo _ => "axiom" | .defnInfo _ => "def"
              | .thmInfo _ => "theorem" | .opaqueInfo _ => "opaque"
              | .quotInfo _ => "quotient" | .inductInfo _ => "inductive"
              | .ctorInfo _ => "constructor" | .recInfo _ => "recursor"
            let id ← dumpType out info.type
            out.putStrLn s!"TYPE\t{info.name}\t{(toJson (reprStr info.levelParams)).compress}\t{id}\t{kind}"
          else if isPrivateName info.name then
            privateCount := privateCount + 1
          else
            internalCount := internalCount + 1
        out.putStrLn s!"EXCLUDED\t{moduleName}\t{privateCount}\t{internalCount}"
  discard <| action.run {}
  out.flush
  IO.println "Public type DAG exported."
