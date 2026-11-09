run_elab do
  -- Reinstall actual legacy auxiliary proofs under fresh names. No axioms or sorry.
  -- Universe arities differ between versions; reusing the modern constant by name is invalid.
  let names := oldStalkTypeAux.map (·.1)
  let renameExpr := fun (e : Expr) => e.replace fun e =>
    match e with
    | .const n us => if names.contains n then some (.const (`BoundaryOld ++ n) us) else none
    | _ => none
  for (n, us, type, value) in oldStalkTypeAux do
    addDecl (.thmDecl {name := `BoundaryOld ++ n, levelParams := us,
      type := renameExpr type, value := renameExpr value})
  let oldType := renameExpr oldStalkType
  unless !(ExprStructEq.mk oldType == ExprStructEq.mk newStalkType) do
    throwError "expected different stored equation expressions"
  Lean.Meta.check oldType
  Lean.Meta.check newStalkType
  unless ← isDefEq oldType newStalkType do
    throwError "actual stalk equation types are not definitionally equal in the modern full environment"
  unless !(← isDefEq (mkConst ``Nat) (mkConst ``Bool)) do
    throwError "negative type control failed"
  logInfo "actual stalkMap.eq_1 types: different stored expressions; legacy auxiliary proofs kernel-checked under fresh names; both types well-formed; definitional equality passes; Nat/Bool negative control passes"
