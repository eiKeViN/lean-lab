module
public import Lean
public section
namespace Boundary
 theorem ext (x : Option Nat) : x = x :=
  match x with
  | none => rfl
  | some _ => rfl
#check ext.match_1_1
