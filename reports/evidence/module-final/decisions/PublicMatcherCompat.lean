module
public import ModernMatcher
public section
@[expose] def Boundary.ext.match_1_1 (motive : Option Nat → Prop) (x : Option Nat)
    (h₁ : Unit → motive none) (h₂ : ∀ y, motive (some y)) : motive x :=
  Option.rec (h₁ ()) h₂ x
