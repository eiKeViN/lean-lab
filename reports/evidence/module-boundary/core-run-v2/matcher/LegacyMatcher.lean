import Lean
namespace Boundary
 theorem ext (x : Option Nat) : x = x :=
  match x with
  | none => rfl
  | some _ => rfl
#check ext.match_1_1
open Lean Elab Command in
run_elab do
  for (n, _) in (← getEnv).constants.toList do
    if n.toString.startsWith "Boundary." then logInfo m!"{n}"
