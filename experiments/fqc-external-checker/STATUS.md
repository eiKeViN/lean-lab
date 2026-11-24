# Full Photochemistry validation

Baseline: FQC `a88de8ff65d78af564b2373088ca369dc95f6547`, Lean 4.35.0.
Checkpoint date: 2026-11-24. Runtime reports live under ignored `results/`;
this document records a checkpoint, not reusable proof of a fresh execution.

| Work package | Status | Evidence / acceptance condition |
|---|---|---|
| Original final-theorem import closure | Complete | 107 source blobs, SHA1/SHA256, 39 external import roots |
| Stage 1/2 certificate coverage | Passed | All 1,656 batches; 415 exact conjunctions; 4,105 cell occurrences |
| Cauchy predicates | Passed | Three original functions; zero-length segment and binding negatives rejected |
| Borrow-wire enumeration | Passed | Original 8,192-input predicate; flipped expected output rejected |
| Pair family | Passed | All 16 original cases; omitted, wrong-index and false results rejected |
| ULP family | Passed | All 32 original cases; exact batch binding and three rejection cases passed |
| Named closed decisions | Passed | 59 locked source sites; all original decisions accepted and independently replayed; exact frozen expressions matched |
| Small sample and Stage 2 references | Passed | Fresh original `c1_0` / `c2_0`; four corruptions per stage rejected by native and kernel routes; 11 audited bridge lemmas |
| Admission negatives | Passed | Changed catalog/checker/admission/binary identities; missing and duplicate admissions |
| Evaluator rejection paths | Passed | Actual Lean rejection of false, open, unregistered and foreign-axiom goals |
| Exact dependency setup | Passed | Ten pinned packages; official Mathlib cache closure 3,241 artifacts; 42 Physlib modules |
| Source-preserving partitions | Complete | 16 HalfPlane and seven MidTap namespaces; three Coulomb and five polynomial section partitions; definitions modules and original import-path facades |
| Complete materialization | Passed | 143 generated modules, 90 unchanged original modules, 480 named assumptions; final source unchanged |
| Full final-theorem compilation | Passed | Both original final theorems compiled with unchanged source |
| Public-type equality | Passed | Separate reference/solution processes; five canonical elaborated types equal retained export |
| Reachable-axiom audit | Passed | Both final theorems: standard three plus all 480 exact external names; no unapproved or unused external entries |
| Reproducible entry point | Passed | Fresh `bash scripts/check.sh full` and `all-status.json` |
| Upstream Comparator | Not run | Its original three-axiom whitelist excludes the deliberately extended trust policy |

The 480 registered assumptions comprise 415 coverage propositions, three Cauchy
results, one borrow-wire result, two parameter batches, and 59 named closed
decisions. Each numerical predicate and all downstream generic mathematics retain
the upstream definitions and proofs. The complete coverage decoder is a trusted
executable port; its equivalence is not established by the 11 small bridge lemmas.

Final targets are `QuantumComputation.Specs.photochemistry_correctness` and
`QuantumComputation.Specs.photochemistry_const_cost`. Their original source,
program and stated specification are retained. Numeric admissions, source identity,
public-type equality, kernel compilation and reachable assumptions are checked
separately. The isolated reference export never supplies the candidate placeholders
to the solution environment.

The implementation adds neither a generic `sorryAx` allowance nor a blanket native
axiom prefix. The named evaluator's 59 propositions are locked as actual elaborated
expressions after successful evaluation; normal audits must match that registry.
A complete decoder-equivalence proof and an independently modified Comparator are
separate follow-up projects.

## Successful complete check

`bash scripts/check.sh full` returned exit 0 on 2026-11-24 in
438.60 s. Valid Lake traces were reused; external observations,
original small kernel references, negative tests, public-type export and final
axiom audit were rerun. This is not a cold-build timing. Linux `wait4` reported
4,424,320 KiB maximum RSS for the command/child-process family;
that statistic is not aggregate simultaneous RAM and excludes RAM-backed cache
usage from a process-RSS measurement. The machine had 9.7 GiB RAM, no swap.

The first final-target bootstrap after its dependencies were ready took 38.58 s
(max-RSS 1,980,636 KiB); this also is not a cold dependency build.

Fresh numerical timings from the successful complete check:

| Check | Seconds | Boundary |
|---|---:|---|
| 1,656 coverage batches | 26.81 | Checker runtime only |
| Three Cauchy predicates | 5.12 | Includes evaluator imports and result binding |
| 8,192-input borrow enumeration | 4.16 | Includes evaluator imports and result binding |
| 16-case pair family | 23.91 | Includes evaluator imports and result binding |
| 32-case ULP family | 30.92 | Includes evaluator imports and result binding |

Reports are reproducible from the pinned sources and committed admission code;
ignored runtime files are not treated as a substitute for a fresh check.
