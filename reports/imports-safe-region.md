# Safe-region import optimization — acceptance pending

Branch:codex/imports-safe-region, from verified2a7f8dc51dae6b10bc8344890a32ca0ef323b633.
This is A-line work only. The125-module migration scope, module/public/expose
strategy,1196 modern type policy,3947 complete records and three-axiom rules are
unchanged. No remaining legacy boundary is migrated or reproduced here.

Eight independent already-modern producers receive precise public Mathlib data
and source-used tactic imports:PlaneReduction,Flat.Kernel,Dual.BalancedCut,
Quotient.KernelReduction,Projective.ReverseFiltration,Polynomial.LowPart,
Localization.Membership and Submodule.ProductScaling. Mathematical text is exact;
253 other products, including all136 legacy products, remain byte-identical.
The previous12 narrow records are immutable under the extended hash-bound plan.

Fresh starting setup and43-stage ready acceptance passed. Read-only shake was
scoped to the8 ready targets, without force/fix; lakefile bytes were restored.
Six first candidates compiled; Quotient.KernelReduction needed the actual
QuotSMulTop-free instance from RingTheory.Regular.Free, and ProductScaling needed
Algebra.Tower and BigOperators.Associated. Only imports repaired these failures.
The8 targets and an isolated modern consumer now pass:owned names and lowPart rfl
are available, while unrelated MeasureTheory.integral_const is unavailable.
External consumers requiring such formerly incidental Mathlib re-exports need
explicit Mathlib imports; arbitrary Mathlib forwarding is not promised. The
existing explicit Bochner.Basic consumer test demonstrates the repair. No
production consumer repair has been necessary so far.

Observed per-target importArts change from8908 to856–1766 (Mathlib8530 to600–1509).
This is a transitive-closure observation, not a clean-build speedup claim. Source
metadata and graph flags are updated exactly; local implementation edges remain363.

The complete downstream build and final44-stage acceptance are in progress.
Final full/public types,axioms,consumer regressions,doc/index checks,execution
identity and costs will be recorded before final delivery. Checkpoint is not
acceptance. No main merge,other-task branch edit,or upstream PR is performed.
