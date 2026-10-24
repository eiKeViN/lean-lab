import ModernMatcher
#check Boundary.ext
#check Boundary.ext.match_1_1
example (motive : Option Nat → Prop) (x : Option Nat)
    (h₁ : Unit → motive none) (h₂ : ∀ y, motive (some y)) : motive x :=
  Boundary.ext.match_1_1 motive x h₁ h₂
