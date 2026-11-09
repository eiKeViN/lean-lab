module
public import Lean
public section
namespace Boundary
structure Map where
  toFun : Nat → Nat
  map_add : ∀ x y, toFun (x + y) = toFun x + toFun y
