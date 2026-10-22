module
import ForMathlib.LinearAlgebra.CoordinateProjection
import Lean
open OAI.KLInvariance.CoordinateProjection
universe ur un uv ux
variable {R : Type ur} [CommRing R] {N : Type un} [AddCommGroup N] [Module R N]
  {V : Type uv} {X : V → Type ux} [∀ x, AddCommGroup (X x)] [∀ x, Module R (X x)]
  (f : ∀ x, N →ₗ[R] X x)
example (U : Set V) (n : N) (x : U) : (project f U n).val x = f x.val n := rfl
example {U K : Set V} (h : U ⊆ K) (n : N) :
    restrict f h (project f K n) = project f U n := rfl
run_elab do
  if (← Lean.getEnv).contains `MeasureTheory.integral_const then
    throwError "Unexpected accidental unrelated Mathlib re-export"
  IO.println "Narrow consumer: owned .val/rfl contracts hold; integral_const is unavailable."
