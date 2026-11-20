import Mathlib.Algebra.BigOperators.Fin
import Giallar.Certificates
import Giallar.PhaseTraceDistance
import Giallar.RealScheduling

open Giallar.Certificates

/-- The relaxation permits x=1/2, but integer feasibility requires x≥1. -/
def halfProblem : System 1 1 where
  coeff := fun _ _ => 2
  rhs := fun _ => 1

/-- The split proves infeasibility left of zero and a unit lower bound to its right. -/
def halfCertificate : BranchCertificate 1 1 :=
  .split 0 0
    (.infeasible (fun i => if i = 0 then 1 else 1 / 2))
    (.bound (fun i => if i = 0 then 1 else 0))

theorem halfCheck : check halfProblem (fun _ => 1) 1 halfCertificate = true := by
  norm_num [check, halfProblem, halfCertificate, IsDual, System.prepend,
    System.upperRow, System.lowerRow, Fin.forall_fin_succ, Fin.sum_univ_succ]

example (x : Fin 1 → ℤ) (hx : halfProblem.feasible fun j => (x j : ℚ)) :
    1 ≤ dot (fun _ => (1 : ℚ)) (fun j => (x j : ℚ)) :=
  check_sound halfProblem (fun _ => 1) 1 halfCertificate halfCheck x hx

example (x : Fin 1 → ℝ) (hx : halfProblem.feasibleReal x)
    (hi : IntegralOnTree halfCertificate x) :
    1 ≤ dot (fun _ => (1 : ℝ)) x := by
  simpa using check_sound_real halfProblem (fun _ => 1) 1 halfCertificate halfCheck x hx hi

#print axioms Giallar.Certificates.check_optimal_real
#print axioms Giallar.phaseDistance_unitary_eval_le
#print axioms Giallar.traceDistance_unitary_le_phaseDistance
#print axioms Giallar.RealScheduling.earliest_makespan_le
