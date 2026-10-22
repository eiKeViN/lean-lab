module
public section
@[expose] def consume (P : Nat → Prop) (_h : ∀ n, P n) : Nat := 0
variable (Q : Nat → Prop) (hQ : ∀ n, Q n)
set_option backward.proofsInPublic true in
@[expose] def attachStalkMap : Nat := consume _ (by simpa using hQ)
