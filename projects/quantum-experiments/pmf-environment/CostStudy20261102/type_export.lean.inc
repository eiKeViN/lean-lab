import Lean
open Lean Elab Command

private partial def canonicalType (e : Expr) : Expr :=
  match e with
  | .mdata _ a => canonicalType a
  | .forallE _ t b bi => .forallE Name.anonymous (canonicalType t) (canonicalType b) bi
  | .lam _ t b bi => .lam Name.anonymous (canonicalType t) (canonicalType b) bi
  | .letE _ t v b nd => .letE Name.anonymous (canonicalType t) (canonicalType v) (canonicalType b) nd
  | .app f a => .app (canonicalType f) (canonicalType a)
  | .proj s i a => .proj s i (canonicalType a)
  | e => e

run_cmd do
  let env ← getEnv
  for n in STUDY_NAMES do
    let some ci := env.find? n | throwError "missing declaration {n}"
    let levels := ci.levelParams.zipIdx |>.map fun (_, i) => Level.param (Name.mkSimple s!"u{i}")
    let t := canonicalType (ci.type.instantiateLevelParams ci.levelParams levels)
    liftIO <| IO.println ("TYPEJSON " ++ (Json.mkObj [("name", toJson n.toString),
      ("type", toJson (reprStr t))]).compress)
