module
public section
@[expose] def consume (P : Nat → Prop) (_h : ∀ n, P n) : Nat := 0
variable (Q : Nat → Prop) (hQ : ∀ n, Q n)
@[expose] def attachStalkMap : Nat := consume _ (by exact hQ)
