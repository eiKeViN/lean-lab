# Library-wide screening and lemma extraction — 2026-10-22

This round keeps the same project and branch. It selects 21 old proofs in 11
files and retains 24 new lemmas with independent mathematical responsibilities.
Together with the first three rounds there are 45 added lemmas and 36 rewritten
old proofs. It is a wider extraction round, not a general API redesign or a claim
that every library proof has been read line by line.

Start: `a0b5b59457f593c86d3054b086da3b820585c282`; main observed at
`a234ae5be6f77763e2014aad2cddd69e6aa50755`. The pre-edit screening plan was
published in `c234e512b76201d14d14b1dcecb716a84a8c9dc9` before source edits.
No main merge is part of this round. The sole maintained project remains
`experiments/kl-for-mathlib`; historical baselines stay recoverable from Git.

## Coverage and selection

The [coverage register](lemma-granularity-library-coverage.md) and
[evidence](evidence/lemma-granularity-library/coverage.json) cover all 207
implementation files, with another 54 import-only entries checked separately.
All 261 file hashes were checked against the starting Git tree. The named-heading
recognizer is a bounded inventory, not a Lean parser or a full list of generated
constants/instances. Twenty files received targeted source/proof reading; eleven
were selected and nine retained after that reading. Other regions were screened
at declaration/region level and deferred, not declared devoid of useful lemmas.
The later duplicate cross-check also read the existing `Hilbert/Numerator` shift
lemma; that focused check is recorded as a coverage addendum.

| Region and old clients | Extracted mathematical responsibility | Decision |
| --- | --- | --- |
| `Localization/FiniteCharacters`: `uniform_projector`, `class_projector`, `partition_local_denominator`, `character_class_projector` | Polynomial values on/off a block; nondivisibility of a test product; common-denominator partition identity; existence of stable separating tests | Four lemmas, leaving stability, prime avoidance and final assembly with their respective clients |
| `Localization/ProjectiveLattice`: `prime_divide_of_relation`, `mem_of_prime_local_membership` | Coordinate prime divisibility; one prime denominator cancellation | Two lemmas; free-coordinate calculation does not require projective splitting, domain or UFD assumptions |
| `Polynomial/Reciprocal`: `low_degree_zero_of_eval_reciprocal` | Functional reciprocity on an interval implies polynomial reflection identity | One lemma with degree coverage; strict midpoint bound remains solely in rigidity |
| `Hilbert/Basic`: `pieces_eq_of_value_eq`, `eq_of_value_eq` | A strict graded rank defect lowers the convergent Hilbert value; homogeneous pieces reconstruct inclusion | Two lemmas separating analytic positivity from algebraic gluing |
| `Hilbert/Images`: `scalar_value`, `imageMap_ker`; `Hilbert/Increment`: `shifted_image_value` | Existing sequence-shift API; scalar witnesses lie in a saturated submodule | One new lemma, two actual reuses of an existing API |
| `Hilbert/Series`: `value_image_exact` | Weighted degreewise exactness; positivity transfers summability to kernel and image | Two lemmas before summing the exact sequence |
| `Sheaf/Pullback`: `pullback_flabby_live`, `pullback_kernel` | Geometric live-edge image closure; compatibility of pushed partial sections; unconditional and live-edge converse kernel inclusions | Four lemmas; extension and equality assembly remain in old clients |
| `Sheaf/BaseChange`: `tensorSections_surjective`, `baseChange_flabby`, `baseChange_upperQuotient` | Finite tensor constraint transport; extension of already-tensored sections; scalar-kernel exact sequence | Three lemmas; finiteness/flatness for arbitrary sections stays with the later client |
| `Sheaf/Models`: `prod_scaledImages`, `pi_scaledImages` | Lower-image and scaled upper-image membership decomposes into factor witnesses | Four lemmas; arbitrary scalar, including zero, and arbitrary family index |
| `Sheaf/FlowDown`: `flowDown_flabby` | Agreement off a vertex makes the correction defect divisible by the outgoing label product | One lemma; choosing the flow-down section and induction stay with the client |

Exact full names, source links, conditions, original-site keys and short explanations
are in the generated [lemma index](../experiments/kl-for-mathlib/LEMMA_INDEX.md).
[Proof structures](evidence/lemma-granularity-library/proof-structures.json) retain
all 21 old statements and complete before/after proof bodies at the starting and
final source states; current helper signatures and bodies are in the Lean diff.
This evidence supports mathematical structure comparisons, not semantic search
quality inferred from line counts. Nonblank proof-body lines are 430 before and
214 after, plus 225 in new helpers (439 combined, +9). Signatures and docs add
further source length. These are textual volume counts, not complexity, token or
speed measures; see `proof-volume.json`.

## Representative before/after structure

- `mem_of_prime_local_membership` formerly embedded the scalar relation in a
  projective presentation, divided its coordinates, cancelled the prime using
  torsion freeness, and resumed UFD induction. The new
  `cancel_prime_denominator` states the local-to-prime cancellation task itself;
  the main induction now calls that task. Its prerequisite
  `prime_dvd_coordinates` separately states the free-coordinate argument.
- `low_degree_zero_of_eval_reciprocal` formerly interleaved interval evaluations,
  invertible scalars and reflected polynomial evaluation before reading a
  coefficient. `eq_reflect_of_eval_reciprocal` owns that functional-to-algebraic
  bridge under `natDegree ≤ d`. The old theorem owns the stronger strict support
  bound and coefficient contradiction. The old conclusion and hypotheses do not
  change.
- `pullback_flabby_live` now reads as live-image closure, pushed compatibility,
  ambient extension, then pulling back. Neither new preliminary lemma assumes
  flabbiness or finite vertices; only compatibility needs injectivity/dead-edge
  hypotheses. Kernel equality separately composes two inclusions with different
  hypotheses. This exposes real logical responsibilities, though dependent
  assignment transports remain inside the helpers.
- `value_image_exact` now obtains the weighted rank identity and convergence of
  the two series before applying `tsum_add`. The algebraic identity accepts every
  real parameter; the summability lemma requires a positive parameter.
- Product and arbitrary-product scaled-image proofs now compose coordinate
  membership equivalences with the factor assumptions. They no longer unpack
  witnesses in the same proof that establishes scaled-image equality. These
  remain representation-specific sheaf lemmas, not a universal transport API.

The initial 25-helper plan contained a duplicate shift calculation. A later
whole-library check found `Hilbert.hasSum_shift_coeff` already in `Numerator`.
The revised plan withdraws `hasSum_shift_weight` and calls the existing theorem
from `scalar_value` and `shifted_image_value`. Its original `numerator_add_shift`
consumer remains unchanged. One exact same-layer import, `Series → Numerator`,
is recorded separately from the pristine migration and included in the active
DAG checks. `pre-reuse-plan.json` preserves the initial plan, while the revised
`plan.json` is hash-bound by the evolution checker. This is a recorded discovery
and correction, not a newly extracted lemma or a new second use for a retained
helper.

The only additional consumer of a **new** helper this round is
`image_terms_summable → term_image_exact`; it is a helper-to-helper call, not a
second old proof. All original helper call sites and both new existing-API uses
are inside the planned samples. Outside-sample production reuse remains zero.
Four new applicability examples check an empty projector block, `X+1` reflection,
a zero scalar product image and an empty product family; examples are tests,
not production reuse.

## Retained and deferred work

Direct reading retained the already coherent adjoint/Frobenius/summand and
coordinate kernel APIs, `Polynomial/LowPart`, and application support/free-model/
stalk-reciprocity/edge-localization responsibilities. Isolated simp steps,
nonzero-power positivity, coefficient wrappers and degree-bound arithmetic were
not split into names. Larger tensor/basis/generator abstractions need their own
proof reading and interface design. Coxeter, root-plane, dihedral and Hecke-word
regions were not excluded because they are specialized mathematics: their
inventory-level screening is explicitly marked deferred.

No previous helper proof or type changed. The ten prior active source files are
frozen. Prior debts remain: redundant torsion-free/pairing assumptions in integral
support, a heavy terminal-root-complement import, and an application-owned scalar
identity that may deserve a general home later. New candidates also retain
project namespaces and some inherited section context; this round does not claim
Mathlib-ready APIs or minimal hypotheses everywhere. Small finite-product and
coordinate witness lemmas are accepted for coherent statements, not size alone.
`upperQuotient_exact` is especially small: its value is exposing the scalar-kernel
condition in the exact-sequence formulation consumed by flat tensoring, rather
than moving a large proof. It is not presented as a large complexity reduction.

## Validation and retrieval

The final `lake build ForMathlib OAI` passed in **1171.704 s** with the
fixed Lean 4.34.1 (`5045d0056413266e57c625dcd7c365b10e377c52`) and Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`. No installation or Mathlib source
build was performed this round; the existing pinned toolchain/cache was reused.

- All **32 validator stages** passed in **109.747 s**; the warm repeat was
  **4.651 s**. [Stage records](evidence/lemma-granularity-library/final-validation/stages.json)
  and logs separate baseline replay, current builds, exports, axioms and tests.
- The fresh export has **3947** owned declarations: the **3902** baseline types
  match under the inherited comparison policy; the previous **21** added records
  remain exact, and **24** new theorem types are separately listed in
  [twenty-four-new-types.json](evidence/lemma-granularity-library/twenty-four-new-types.json).
  No missing or unlisted public declaration, changed level/type/kind, or new axiom
  declaration was accepted. The comparator's 3902 owner relocations are inherited
  from the historical architecture migration, not file moves in this round.
- The hash/diff/span guard covers **21** active source exceptions, freezes the
  prior **10** byte-for-byte, and preserves all **36** selected old headers
  literally. The other product sources still match pristine reconstruction.
  The new integration import is exact and hash-bound; the active DAG has **363**
  direct edges and **zero ForMathlib-to-OAI edges**. No global simp attribute or
  custom tactic was introduced.
- The **81** exact named pilot closures and **16** original audit closures satisfy
  the three-axiom allowlist. The main theorem is still exactly
  `[propext, Classical.choice, Quot.sound]`. No `sorry`, added axiom or unsafe
  proof bypass is accepted. Closure logs are in `final-validation`.
- **30** evolution regressions passed normally and with `python3 -O`; the
  inherited comparator **31** and partition **14** tests passed, as did root
  script **18** tests both normally and optimized. New negative cases cover
  rebinding third-round source/types, an unselected proof, an old header,
  an unlisted import, and complete zero-axiom audit records.
- Kernel proof expressions verify **50** cumulative direct relationships, **27**
  in this round (24 original-client/new-helper, two existing-API uses, one
  helper-to-helper). The initial applicability pass had linter warnings: `simpa`
  could close the empty-block goal without using the helper. After the 32-stage
  run, that test was strengthened to an explicit helper application. One rerun
  failed on an incorrect Mathlib spelling; pinned-source lookup fixed it to
  `Finset.notMem_empty`. The final **6.497 s** focused compile passed without
  warnings. Only `PilotChecks.lean` changed in this follow-up; library source,
  type exporter, policy and other checks were unchanged. The original warning,
  failed rerun and final clean logs are all retained, rather than relabelling
  the earlier 32-stage result as a rerun of the strengthened test.

[Verified input hashes](evidence/lemma-granularity-library/verified-inputs.json)
record the final tested source/tooling and export hash. The line-based guard is
bounded, not a general Lean parser; compilation, type export and axiom checks are
independent safeguards. The pre-existing unused torsion-free-section-variable
warning is replayed for the frozen support helper; it was not suppressed.

The current Lean-exported lexical corpus has **2627** theorems, versus **2603**
before this round. All **45** indexed explanations match compiled docstrings.
The ten queries were fixed before source/doc edits and the ranking method was
unchanged. Role-target labels were assigned afterwards; this is a reproducible,
**nonblind diagnostic**, not an independent user study or proof of lookup speed.
New-target absence in the old corpus is not itself a quality improvement.

| Fixed query topic | First role-target rank after | Rank with only the 24 new docstrings removed |
| --- | ---: | ---: |
| stable character class separating tests | 1 | 42 |
| finite partition common scalar denominator | 1 | 3 |
| prime scalar relation projective lattice cancellation | 1 | 2 |
| functional reciprocity implies polynomial reflection | 1 | not ranked |
| strict homogeneous piece Hilbert value defect | 1 | 4 |
| integer graded sequence shift weighted sum | 7 | 7 |
| live edge pullback partial section compatibility | 1 | 10 |
| flat tensor section constraint kernel | 1 | 16 |
| product sheaf scaled image witnesses | 1 | 5 |
| flow down correction outgoing label product | 1 | 75 |

Nine new-role queries place a new lemma first. The existing shift API remains
seventh with or without the new docstrings; it has no new source docstring.
The generated index adds an explicit reuse lookup note. Names remain in the
ablation and corpus-dependent IDF is recomputed, so the table is evidence about
this lexical method, not semantic understanding or statistical significance.
[Full rankings and caveats](evidence/lemma-granularity-library/search-comparison.json)
and compressed before/after/ablation corpora preserve the exact observation.
No docstrings or queries were retuned after examining these rankings.


## Costs and reproduction

[Timing summary](evidence/lemma-granularity-library/timing-summary.json),
[command ledger](evidence/lemma-granularity-library/measurements.jsonl) and
[phase observations](evidence/lemma-granularity-library/phase-observations.json)
retain successes, failures and limits. The approximate session start was 02:10 UTC;
the pre-edit plan commit is exactly 02:17:32. Initial grouped source builds finished
at 02:29:37, the final mathematical source write was 02:39:40, and final tests
finished at 03:15:00. These overlapping phase windows are not exclusive active
model/editing time. Selection/design, incremental verification-tool adaptation
and reporting were not separately stopwatch-metered; their exclusive costs are
unavailable. Existing three-round infrastructure and the installed Lean/Mathlib
cache are not charged as new setup work.

| Observed command group | Wall seconds | Interpretation |
| --- | ---: | --- |
| Initial five targeted batch commands | 101.036 | Includes three failed integration iterations and successful compilation of all selected sources |
| First full downstream build | 1243.836 | Completed normally; superseded by the later duplicate-removal revision |
| Final source/cache reconciliation | 1171.704 | Recompiled affected foundational dependents and passed |
| Full 32-stage validation | 109.747 | Includes the warm repeat below; do not add it twice |
| Warm repeat within that run | 4.651 | Artifact readiness; not comparable with cold direct elaboration |
| Final strengthened harness compile | 6.497 | After one 6.285-second spelling failure; no library rebuild |

All instrumented commands total **2727.090 command-wall
seconds** and **3216.208 child CPU seconds**. These are not
exclusive session elapsed time: the cancelled gated startup overlaps the first
build. Build-command wall totals **2561.449 s**, including
failures and that wait. Shared arithmetic averages are **102.458 s** per attempted
new statement (25 proposals) and **106.727 s** per retained lemma (24), not
individual or marginal lemma prices and not a linear forecast for another region.
No new paired direct-elaboration microbenchmarks were run; no speedup is claimed.

The main compute lesson is dependency placement: even an unchanged `Stalks` and
`UpperSections` proof is rebuilt after foundational changes. The late duplicate
check caused a second pass through that heavy chain. Future rounds should check
existing theorem APIs before the first full build and finish a dependency batch
before launching it. Grouping edits limits repeat work; lemma extraction by
itself does not reduce module-level invalidation. This round's infrastructure
changes are explicit plan/type/source bindings, six small regression extensions,
one active import edge and reuse of the existing index/search tooling, not a new
test framework. **Reliable model token telemetry is unavailable.** No character,
line count or estimate is reported as token consumption.

All failed measured commands are retained:

| Label | Exit | Wall seconds |
| --- | ---: | ---: |
| `library-algebra-characters` | 1 | 9.477 |
| `library-algebra-build` | 1 | 25.798 |
| `library-algebra-corrected` | 1 | 24.833 |
| `library-reuse-downstream` | -15 | 44.872 |
| `library-applicability-clean` | 1 | 6.285 |

The `-15` row is a deliberately terminated startup blocked at the serial
`lean --githash` query, before compilation; the original running build was not
interrupted. Unmetered partial-edit, scope-recorder and unsupported-option
iterations are listed separately. Initial Lean failures were new-interface
DecidableEq/function-congruence integration errors, not failures of unchanged
upstream mathematics. No failed iteration or placeholder warning is accepted as
final verification.


```bash
bash scripts/setup.sh
bash scripts/check.sh
source scripts/env.sh
cd experiments/kl-for-mathlib
SEMANTIC_CORPUS_OUT="$LAB_ROOT/results/lemma-granularity/library-after-corpus.json" \
  python3 pilot_measure.py library-after-corpus-replay lake env lean SemanticCorpus.lean
python3 render_lemma_index.py "$LAB_ROOT/results/lemma-granularity/library-after-corpus.json" --check
python3 semantic_search.py "$LAB_ROOT/results/lemma-granularity/library-after-corpus.json" \
  --library --query "live edge pullback partial section compatibility"
```

Use the retained baseline corpus for the old query results; exporting the current
source cannot recreate a historical corpus. Setup reuses the pinned dependencies
and warm artifacts, does not change saved settings, and refuses an automatic full
Mathlib source build. Compilation and allowed-axiom closure checks do not
independently certify the original mathematical development. No new independent
external source review or GitHub CI result is claimed by local validation.
