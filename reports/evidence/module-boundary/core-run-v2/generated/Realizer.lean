import Legacy
import Modern
open Lean Meta Elab Command
run_elab do
  for name in [``Boundary.legacy, ``Boundary.modern] do
    let before := (← getEnv).contains (name ++ `eq_1)
    let eqs ← getEqnsFor? name
    logInfo m!"{name}: before={before}; equations={eqs}"
    if let some eqs := eqs then
      for eq in eqs do
        logInfo m!"{eq}: owner={(← getEnv).getModuleIdxFor? eq}"
  let a ← getConstInfoDefn ``Boundary.legacy
  let b ← getConstInfoDefn ``Boundary.modern
  logInfo m!"legacy body: {a.value}"
  logInfo m!"modern body: {b.value}"
  unless ← isDefEq a.value b.value do throwError "body reduction mismatch"
  logInfo "bodies definitionally equal"
  let lawA := a.value.getAppArgs[1]!
  let lawB := b.value.getAppArgs[1]!
  logInfo m!"law shapes: legacy const={lawA.isConst}; modern lambda={lawB.isLambda}"
  unless lawA.isConst && lawB.isLambda do throwError "unexpected proof representation"
  let ta := (← getConstInfo `Boundary.legacy.eq_1).type
  let tb := (← getConstInfo `Boundary.modern.eq_1).type
  let ta := ta.replace fun e => if e.isConstOf ``Boundary.legacy then some (mkConst ``Boundary.modern) else none
  unless !(ExprStructEq.mk ta == ExprStructEq.mk tb) do throwError "expected stored expression difference"
  unless ← isDefEq ta tb do throwError "equation types differ definitionally"
  logInfo "equation types: stored expressions differ; definitional equality passes"
example : Boundary.legacy = Boundary.modern := rfl
example (n : Nat) : Boundary.modern.toFun n = n := rfl
example (x y : Nat) : Boundary.modern.toFun (x+y) = x+y := by simp [Boundary.modern]
