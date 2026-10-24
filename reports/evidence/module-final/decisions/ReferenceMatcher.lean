module
public import Lean
public section
namespace Boundary
 theorem ext (x : Option Nat) : x = x :=
  match x with
  | none => rfl
  | some _ => rfl
#check ext.match_1_1

@[expose] def keepMatcher := @Boundary.ext.match_1_1
