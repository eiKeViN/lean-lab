module
public section
private def quotientLinear (n : Nat) : Nat := n + 1
def structureSheaf (n : Nat) : Nat := quotientLinear n
-- A propositional API can retain the private implementation.
theorem structureSheaf_spec (n : Nat) : structureSheaf n = n + 1 := by
  unfold structureSheaf quotientLinear
  rfl
