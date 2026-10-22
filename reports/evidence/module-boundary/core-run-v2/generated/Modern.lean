module
public import Common
public section
namespace Boundary
@[expose] def modern : Map where
  toFun n := n
  map_add x y := by rfl
