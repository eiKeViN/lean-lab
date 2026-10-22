# A line: safe-region import optimization

Completed on `codex/imports-safe-region`, from verified
`2a7f8dc51dae6b10bc8344890a32ca0ef323b633`. Eight already-modern producers now use
precise Mathlib imports. All 44 final acceptance stages pass after an actual
complete ForMathlib/OAI build. The 125-module migration set, public/expose strategy,
mathematics, compatibility standards and legacy boundaries are unchanged.
B-line migration-boundary reproduction is intentionally outside this work.

## Actual changes and closure

All eight targets originally publicly imported Mathlib and had no local imports.
They form independent upstream dependency closures. Counts below are actual
setup.json importArts, with complete module lists and setup hashes retained.

| ForMathlib target | Before | After | Mathlib before → after |
|---|---:|---:|---:|
| LinearAlgebra.PlaneReduction | 8908 | 856 | 8530 → 600 |
| Algebra.Module.Flat.Kernel | 8908 | 1594 | 8530 → 1337 |
| LinearAlgebra.Dual.BalancedCut | 8908 | 921 | 8530 → 665 |
| Algebra.Module.Quotient.KernelReduction | 8908 | 1766 | 8530 → 1509 |
| Algebra.Module.Projective.ReverseFiltration | 8908 | 1268 | 8530 → 1011 |
| Algebra.Polynomial.LowPart | 8908 | 1217 | 8530 → 960 |
| Algebra.Module.Localization.Membership | 8908 | 1416 | 8530 → 1159 |
| Algebra.Module.Submodule.ProductScaling | 8908 | 1067 | 8530 → 811 |

Only leading import lines change. Module declarations, public sections, exposure
annotations, statements, proofs and definition bodies are byte-identical after
removing the exact before/after header prefixes. The other 253 products, including
all 136 legacy products and previous three pilot sources, are byte-identical to
the starting commit. The original migration plan/type/alias policies and protected
snapshots are unchanged. The existing 12 narrow records remain exact; the bounded
header manifest now contains 20. A guard rejects edits to those previous records
or the declared unchanged module scope, with adversarial regression coverage.
Source inversion, span/provenance checks and public/meta/all DAG flags remain
explicit. The 363 local implementation edges are unchanged.

Read-only shake was scoped to the eight ready targets before and after editing,
without fix or force. The temporary defaultTargets setting is restored byte for
byte. Raw status 1 means suggestions remain, not that all suggestions were applied.
Data imports were individually selected; actual source-used Ring/Linarith/Abel
modules were retained. Broad tactic-registration suggestions were not blindly
adopted. Direct import edge count is not the optimization objective; some direct
roots are transitively redundant but conservatively retained. Real transitive
closures shrink, rather than merely deleting a redundant local edge.

## Compatibility and re-export boundary

Both views retain the existing strict checks. Original 3902 types plus 45 additions
pass; the complete fresh 3947-record export is also **byte-identical** to the fresh
starting export (SHA256
`4941d5baf676d273d887fa1a96f8142bd30d1b2372747c5e390e3f3b4b5f1ada`).
All normalized fields, including module owners, match with zero changes. All 1196
modern records, original-kind checks and the three-axiom limit pass. Existing old
names, proof-reuse, `.val`, inverse-map and rfl consumers pass. No kind/private-name
exception, body-hiding change or declaration/API redesign was introduced.

`SafeImportChecks` imports only these eight producers and Lean, confirms every
owned declaration from those producer records is available, and proves the
lowPart definition equality by rfl. It asserts unrelated
`MeasureTheory.integral_const` is absent. Thus arbitrary Mathlib forwarding is
intentionally reduced. This applies to focused paths and any forwarding wrapper
whose ambient Mathlib availability depended solely on them; arbitrary external
import-only uses are not promised compatible. Such consumers need explicit
relevant Mathlib imports. The existing modern explicit
`Mathlib.MeasureTheory.Integral.Bochner.Basic` consumer demonstrates the repair.
No production consumer repair was necessary in the actual whole build.
Compatibility and aggregate entrypoints retain all owned API responsibilities.
Aggregates still carry the broad Mathlib closure; no default-project closure or
performance improvement is inferred from these focused reductions.

Fresh full-view semantic extraction retains all 2627 records and 338 documented
theorems. All 45 indexed compiled docstrings and four retrieval groups pass.
Index contents did not change. This legacy/server corpus result does not assert
ordinary public-view documentation availability.

## Failures, actual cost and limits

Fresh fixed-cache setup took 4.69 s; starting 43-stage acceptance took 159.22 s and
passed before any source edit. This reused the current environment/cache, not a
new-environment initialization measurement. Lean4.34.1/5045d005 and Mathlib/d13f23b
pins remain fixed; the Mathlib Git tree is clean. Resources remain four CPU,
16 GiB, LEAN_NUM_THREADS=4 and the inherited serial compiler gate.

The first compiled candidate set had two real missing-import failures:
Quotient.KernelReduction required the quotient-module Free instance defined in
Mathlib.RingTheory.Regular.Free; ProductScaling required Algebra.Algebra.Tower
and Algebra.BigOperators.Associated. Precise imports fixed them; no body changed.
Six other targets had already passed. The failed run took16.02 s, then the repaired
ready-target run7.34 s. The source-used imports and failures are retained.

An earlier editor slip replaced the122 module-count guard with202 while changing
the12-import guard to20; static analysis correctly failed closed. It was restored
before compilation. A prematurely invoked absent /tmp build helper also failed
before executing a build (0.01 s). These are integration mistakes, not permissions
or mathematical failures, and are not counted as successful measurements.

The real complete target build took283.78 s, logging58 rebuilt project modules
and no rebuilt Mathlib source module. Stalks/UpperSections were not logged as
rebuilt in this batch. Final 44-stage acceptance took157.82 s, including a3.57 s
no-change complete build. Its peak child RSS was7784700 KiB; full-build peak was
7558100 KiB. Lake job times include serial-gate waits and must not be summed as
isolated elaboration costs. RSS is largest child process, not aggregate memory.

These are integration costs and observed impact, not controlled performance
comparisons. Baseline/final acceptance have different stage sets; neither those
times nor this batch versus the earlier module-migration build proves speedup.
No full microbenchmark suite, private-only edit experiment, new benchmark
framework or total-time/token estimate is manufactured. Token telemetry is
unavailable; pre-launch hashing and operator/report time are outside command times.

Remaining 117 modern products were not optimized in this bounded batch. Many have
local dependencies still importing Mathlib, so dropping a direct broad edge may
not shrink their closure. All136 legacy boundaries are untouched and left to B.
Further A-line batches should first establish closure reduction, retain necessary
syntax/tactic/instance modules, and run the unchanged complete interface checks.

## Execution identity and reproduction

Every measured command uses scripts/recorded_run.py with actual command, Git/diff
identity and file hashes captured before execution. Whole build and final
acceptance started at2a7f8dc plus the recorded dirty patch, before checkpoint
`ec406991cb318f6da598035b38c2e64770dd6ccb` was created during the run. All347
captured project/script inputs still match that published code exactly; no source,
checker, pin, fixture or index changed after final acceptance. Do not relabel the
execution HEAD as the later checkpoint. Temporary diagnostic/build scripts are
retained with hashes matched to their pre-execution absolute input paths.

From the repository root, using fresh output labels:

```bash
bash scripts/setup.sh
source scripts/env.sh
python3 scripts/recorded_run.py results/recheck/full.log bash scripts/check.sh
# After complete artifacts are ready:
python3 scripts/recorded_run.py results/recheck/warm.log bash scripts/check.sh warm
python3 experiments/kl-for-mathlib/module_rollout.py --write-checks
```

The recorder refuses reused identities. The retained exact diagnostic command
shows the eight-target temporary default scope; it never globally applies shake
results. Offline gzip exports can be compared with unchanged compare_types and
proof_evolution tools; that rechecks captured evidence, not fresh Lean elaboration.

[Evidence](evidence/imports-safe-region/) contains baseline/final execution records,
closure lists, scope protection, full/public exports, all final stage logs, failures,
source identity, semantic/index/retrieval results and checksums. Final remote head
and CI state are checked after push. No main merge, other-task branch edit or
upstream PR is performed.
