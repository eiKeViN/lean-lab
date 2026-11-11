# Target mapping

Status: incomplete; no completion claim. Scope is source.md and acceptance.md, all A–E and both concrete examples.

| Result | Planned module | Current state |
|---|---|---|
| A: actual HGP checks, quotients, parameters, representative distance bound | `Targets.A`, namespace `Sheaf.HGP` | Worker sandbox; compilation pending |
| B: actual supported logical images, both rank and complement identities | Supporting `Paper` module and target module to be assigned | DAG proof plan only |
| C: ambiguity equivalence and least failing erasure equals CSS distance | Target module to be assigned | DAG proof plan only |
| D: both universal strip formulas on actual HGP | Target module to be assigned | DAG and detailed coordination proof plan only |
| E: both concrete examples and required call sites | Target module to be assigned | DAG proof plan only |

Frozen dependencies: Lean 4.33.1, local `/opt/qecert`, Mathlib from `/opt/qecert/.lake/packages/mathlib`. Build from `lean/` using `lake build`; the maintainer owns global builds during collaboration. Final default build must include all library modules, `TargetsCheck.lean`, and `Challenge.lean`. These final audit roots are not yet available. No remote publication is planned.
