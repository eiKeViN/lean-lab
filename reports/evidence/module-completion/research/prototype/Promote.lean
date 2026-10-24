module
public import Lean
public section
namespace Boundary
 theorem ext (x : Option Nat) : x = x :=
  match x with
  | none => rfl
  | some _ => rfl
#check ext.match_1_1

open Lean Elab Command in
run_elab do
  let user := `Boundary.ext.match_1_1
  let n ← withoutExporting <| realizeGlobalConstNoOverload (mkIdent user)
  IO.println s!"actual private helper={n}"
  let ci ← withoutExporting <| getConstInfo n
  let .defnInfo info := ci | throwError "not definition"
  withExporting (isExporting := true) do
    addDecl <| .defnDecl { info with name := user }
