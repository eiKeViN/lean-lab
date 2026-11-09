module
public section
private def quotientLinear (n : Nat) : Nat := n + 1
@[expose] def structureSheaf (n : Nat) : Nat := quotientLinear n
