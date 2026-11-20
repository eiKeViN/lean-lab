# Giallar verification foundations

Lean formalization of the mathematical models in [Specification.md](Specification.md), covering
approximation, phase-polynomial compilation, routing, external result certificates, pulse
scheduling and terminating worklist expansion. This is an independent formal model, with
explicit contracts for future connections to Qiskit implementations.

## Build

From this directory:

```sh
bash setup.sh  # pinned Lean release, fixed dependencies, official Mathlib cache, then checks
bash check.sh  # reuse the prepared environment
```

Lean **4.35.0**, mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`, Physlib
`c5a908ba7a1ee474063626bdf0470af006f9812e`. The Physlib pin is the existing lean-lab quantum
baseline; its Mathlib dependency matches the specification's reference environment. The new
project does not update other experiments or their dependency pins.

Main import: `Giallar`. Each topic has its own module, targeted imports, copyright header,
module documentation and documented definitions. Chronological execution places the first
operation at the right of the matrix product. Matrix analysis explicitly uses the L2 operator
norm (`Matrix.Norms.L2Operator`), never the entrywise sup norm.

## Specification-to-proof map

| Report | Modules | Main declarations |
| --- | --- | --- |
| L1, A1 | `Approximation` | `eval`, `norm_eval_sub_le`, `norm_unitary_eval_sub_le` |
| A1φ | `PhaseDistance` | `exists_phase_min`, `phaseDistance_isLeast`, `phaseDistance_unitary_eval_le` |
| L3, A2 | `TraceBounds`, `PhaseTraceDistance` | `traceNorm_sandwich`, `traceDistance_unitary_le_phaseDistance` |
| L2, A2a/b | `ReferenceSystem` | `norm_kronecker_one`, `traceDistance_reference_unitary_le_phaseDistance`, `unitaryDiamondDistance_le_phaseDistance` |
| L4, measurement A2 | `MeasurementBounds` | `abs_inner_le_half_traceNorm`, `abs_exp_val_sub_le_traceDistance`, `abs_exp_val_unitary_sub_le` |
| A3 | `ControlledPhase` | concrete diagonal CP matrices; `qft_truncation_error`, common-suffix bound, gate counts |
| B0–B2 | `PhasePolynomial` | concrete Boolean CNOT/phase gate semantics, extraction, nonlocal merging, modulo-2π preservation, matrix unitarity |
| B3 | `PhaseSynthesis` | concrete compute/phase/uncompute gates, Gaussian CNOT synthesis, `synthesize_correct`, `optimize_correct` |
| C1, C2, D1 | `Routing`, `LocalGates` | layout bit/matrix representation and concrete local-gate embedding; checked trace soundness; simple-path fallback; bounded heuristic wrapper and SWAP count |
| C3 | `RoutingProbability` | actual nested measurable survival events, geometric tail, almost-sure termination, exact tail-sum expectation and cost bound |
| D3, D4 | `Certificates` | rational dual lower bound/infeasibility; executable branch-tree checker; integer and mixed-integer optimality |
| D2, E1, E2 | `Scheduling`, `RealScheduling`, `TopologicalOrder` | resource/precedence checker, adjacent incomparable swaps, order-independent products, earliest starts and makespan minimum |
| Eexp, E3 | `PulseSchedule`, `SchedulePartition`, `TickPulseSchedule`, `WeightedPulseSchedule`, `RealPulsePartition`, `RealPulseSchedule` | commuting exponentials, actual active timelines, finite real endpoint refinement and chronological gate correspondence |
| E4 | `Hamiltonian`, `HamiltonianMatrix` | derivative-based perturbation estimate; concrete Hermitian matrix evolution and piecewise error sum |
| F1 | `Worklist` | local expansion contract, semantic invariant, strict potential descent, termination, step bound and total correctness |

The fully qualified signatures, including all assumptions, are retained in
[evidence/axioms.json](evidence/axioms.json). The source and import graph are the primary API;
the mathematical source report is preserved unchanged as historical input.

## Verification

`check.sh` verifies dependency identity, builds the aggregate import, elaborates integration
clients, runs mathlib's text-style linter and standard elaboration linters, checks source layout,
and audits all exported declarations with Lean's `collectAxioms`. The audit also checks that
every local library module occurs in the aggregate import closure. The accepted logical basis
is `propext`, `Classical.choice`, and `Quot.sound`; custom axioms, `sorryAx`, source-written
unsafe/partial code and native decision trust shortcuts are rejected. Lean-generated unsafe
recursion helpers used by compiled runtime evaluation are inventoried separately from the
safe logical declarations; proofs do not depend on these compiler implementations.

[tests/Integration.lean](tests/Integration.lean) composes the interfaces on concrete controlled
phases, CNOT/phase optimization, accepted/rejected schedules, accepted/rejected routing actions,
and a terminating primitive compilation. [tests/Certificates.lean](tests/Certificates.lean)
checks a genuine integrality gap: minimizing integer `x` subject to `2x ≥ 1`, with an infeasible
left branch and a lower-bounded right branch. Proofs use kernel-reduced exact arithmetic.

The compiled dependency cache is reused; the check does not claim a separate reconstruction
and kernel re-verification of all Mathlib and Physlib dependencies. Source identity, fresh
project compilation, public types, transitive axioms and examples are recorded separately.

## Mathematical and implementation boundaries

- Global phase is ignored only for an entire evolution. These theorems do not justify dropping
  relative phases inside controlled subroutines.
- The QFT approximation theorem proves deletion error relative to the specified source circuit.
  The retained single-qubit skeleton is parameterized by unitaries, so it includes Hadamards;
  correctness of QFT as the discrete Fourier transform is a separate algorithm theorem.
- Phase synthesis and connected-graph reference routing select finite witnesses
  noncomputably. Their existence and correctness are proved; no runtime bound for that choice
  operation or production executable Gaussian/BFS implementation is claimed. Certificate
  checking and finite path-to-SWAP extraction have executable definitions.
- Randomized correctness holds for legal traces. Probability guarantees additionally require
  the stated positive success lower bound; this is not inferred from the use of randomness.
- Minimum makespan is relative to a fixed, acyclic resource ordering. `TopologicalOrder` derives
  a numbering and a pointwise least real-time resource schedule for any finite strict partial order. Mixed-integer optimality requires integrality only for branched coordinates.
- Real-time scheduling predicates are mathematical checks on exact reals, not executable
  comparisons of arbitrary real numbers. Natural tick schedules and rational optimization
  certificates have computational checkers.
- Pulse semantics uses finite-dimensional, piecewise-constant Hamiltonians, with commuting
  overlapping independent events. Drift/crosstalk perturbations fit E4 when their total
  Hamiltonian deviations are supplied. Dissipation, measurement/feedback, calibration validity
  and leakage to a larger space require their corresponding extended semantic models.
- No original Qiskit Python/Rust implementation, external solver, parser or hardware calibration
  is identified with this model without an additional implementation-to-model proof.
