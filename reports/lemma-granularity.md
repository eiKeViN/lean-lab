# Lemma granularity pilot — 2026-10-21

Architecture PR [#6](https://github.com/eiKeViN/lean-lab/pull/6) was merged first.
Pilot base: `a234ae5be6f77763e2014aad2cddd69e6aa50755`, whose tree equals verified
`6b02eeb`. Pilot branch: `codex/kl-lemma-granularity`; this pilot is not merged.
The same `experiments/kl-for-mathlib` project and its caches are maintained.

## Scope and disposition

Four original proofs in three files were selected before editing. The committed
[plan](lemma-granularity-plan.md) and [frozen query/sample record](evidence/lemma-granularity/plan.json)
precede the implementation. This is a feasibility/cost sample, not a random or
blind experiment and not comprehensive API generalization.

| Sample | Original declaration | Responsibility |
| --- | --- | --- |
| S1 | `OAI.KLInvariance.finite_character_cancellation` | Finite weighted sums and elimination of coordinate errors. |
| S2 | `OAI.KLInvariance.Comparison.matrix_difference_single` | A genuine second consumer of the same single-coordinate calculation. |
| S3 | `OAI.KLInvariance.Comparison.eq_of_scaled_difference_reciprocal` | A real square-root substitution followed by polynomial scaling cancellation. |
| S4 | `OAI.KLInvariance.BruhatGraph.bottom_eq_of_comparisons` | A KL comparison argument with inverse interval-isomorphism bookkeeping. |

| Candidate | Final decision and evidence |
| --- | --- |
| C1 weighted finite-sum exchange | Retained as `weighted_sum_exchange`; separates bilinear reindexing from cancellation. One production consumer, S1. No novelty/upstream-readiness claim. |
| C2 normalized single-coordinate weighted sum | Retained as `weighted_sum_single`; production consumers S1 and S2 actually reference the lemma in their kernel proof values. |
| C3 error-sum equality to zero | Declined: the existing `mul_sub` / `Finset.sum_sub_distrib` simp calculation already expresses the step. |
| C4 final subtraction equality | Declined: `sub_eq_zero.mp` is already the one-step fact. |
| C5 square-root witness in the open unit interval | Retained as `exists_pos_sq_eq_of_mem_Ioo`; keeps the concrete sqrt calculation out of S3's algebraic step. |
| C6 clear reciprocal polynomial scaling | Retained as `eval_difference_of_scaled_reciprocal`; its nonzero-point statement also applies at negative points. |
| C7 nonvanishing of a natural power | Declined: `pow_ne_zero` already supplies it. |
| C8 inverse interval transport away from bottom | Retained as `upper_polynomial_eq_symm`; coherent endpoint bookkeeping, but a context-heavy signature with only one production consumer. |
| C9 transport distinct endpoints | Declined: keep the existing rank-difference/length facts in place rather than another one-off contextual wrapper. |
| C10 combine opposite scalar inequalities | Declined: the existing `linarith` call already closes the combination. |

Thus: 10 considered candidates, 5 retained lemmas, 5 declined; 6 implemented
lemma attempts when C8's failed first iteration is counted. The implemented
statements remain in their existing mathematical namespaces. No new simp
registration, custom tactic or general abstraction hierarchy is added.

## Semantic information and observed use

Each new lemma has a short Lean docstring explaining its mathematical role,
conditions and intended use. [LEMMA_INDEX.md](../experiments/kl-for-mathlib/LEMMA_INDEX.md)
is generated from compiled docstrings and a small JSON index of source parents,
keywords and decisions. The index does not maintain another formal signature or
per-file Markdown specification. `render_lemma_index.py --check` checks both the
compiled/plain source docstring agreement and the generated index. No embeddings,
external search service or vector-store maintenance is introduced.

Compared with a Markdown file beside every Lean file, this keeps the explanation
next to the declaration and avoids synchronizing two specifications. The cost is
that exported docstring metadata must be refreshed to regenerate the browsing
index; the source docstring remains authoritative. This is intentionally a small
pilot tool, not a general documentation platform.

There are **5 original-site calls plus 1 second production use**, verified by
six direct constant references in kernel theorem proof expressions. The second
use is S2's use of C2; **both C2 consumers are among the original four samples**.
**Outside-sample production reuse is 0.** Future potential is not observed reuse.

Four separate examples passed: an integer `Fin 3` sum whose other weights are
17 rather than zero; the square-root witness for `q=1/4`; scaling cancellation
at `t=-2`, `p=X+1`, `d=1`; and an identity interval-isomorphism interface smoke
check. These demonstrate applicability/elaboration, not additional production
reuse. The last example has a reflexive conclusion and is deliberately described
as an interface smoke check, not new mathematical evidence.

## Retrieval observations

The same IDF-weighted word-overlap search uses theorem names and docstrings,
with alphabetical tie breaking and deterministic word accumulation. The baseline
has 2582 project-owned public theorems, the final corpus 2587. Mathlib's complete
external corpus and theorem types/proof bodies are not searched. Six queries were
fixed before new docstrings; no query contains a declaration name. The author
knew the queries when writing documentation, so this is **not an independent
blind relevance benchmark**. No statistical inference is made.

The baseline column is the best rank of the relevant original parent proof; the
new columns rank the extracted target. These are different retrievable units.
A second comparison removes only the five new docstrings from the final corpus,
keeping names, records and search method fixed.

| Query | Original parent rank | New lemma rank | New lemma without its docstring |
| --- | ---: | ---: | ---: |
| weighted finite sum single surviving coordinate | 17 | 1 | 1 |
| exchange two finite sums weighted coefficients | 142 | 1 | 1 |
| positive square root inside open unit interval | no word match | 1 | no word match |
| clear reciprocal polynomial evaluation scaling | 6 | 1 | 7 |
| inverse interval isomorphism equality away from bottom | 19 | 1 | no word match |

For the first two, naming/extraction alone explains the observed target rank;
the experiment does not attribute that improvement to docstrings. Documentation
provides additional matching vocabulary for the other three. The negative-control
query, `projective module prime local denominator`, keeps the same leading
unmodified `EdgeLattice.mem_of_prime_local_membership` result. The frozen baseline
was replayed with the final deterministic search implementation and produced
identical rankings. Full/ablated results and compressed corpora are retained in
[the evidence directory](evidence/lemma-granularity/).

## Proof volume and elaboration

| Proof-body measure | Before | After |
| --- | ---: | ---: |
| S1 | 20 | 10 |
| S2 | 11 | 5 |
| S3 | 16 | 5 |
| S4 | 36 | 28 |
| Four clients combined | 83 | 48 |
| New helper bodies | 0 | 32 |
| Clients plus helpers | **83** | **80** |

These are nonblank uncommented proof-body source lines, excluding signatures,
docstrings and scope frames; they are **not tokens** or proof-complexity measures.
The three whole files grow from **476 to 508 physical source lines**. Extraction
makes the clients shorter but does not deliver substantial total proof-volume
reduction; signatures/documentation have a real maintenance footprint.

Two sequential direct-elaboration pairs were run for each containing module,
reversing before/after order in the second pair. Both variants use the same
already-warm active dependencies, fixed toolchain, temporary input filename and
serial compiler gate; every input is elaborated from source without accepting an
input `.olean`. The before source is checked pristine reconstruction, not a second
historical project. In particular, this does not measure a cold historical build.
The modules contain other unchanged declarations as well as the sampled proofs.

| Containing module | Before mean seconds | After mean seconds | Individual before → after pairs |
| --- | ---: | ---: | --- |
| SingleCoordinate | 4.256 | 4.288 | 4.295→4.071; 4.217→4.505 |
| ScaledEvaluation | 4.264 | 4.135 | 4.182→4.135; 4.346→4.135 |
| Finite invariance | 4.801 | 4.868 | 4.821→4.822; 4.782→4.914 |

These small differences include process/Lake startup and ordinary timing noise.
Two pairs do not establish speedup, statistical significance or general absence
of regressions. The final warm library rebuild was 4.440 s; it is not compared
with direct source elaboration or a cold build.

## Costs and failure iterations

No model input/output token-usage meter is exposed. **Model token cost and tokens
per lemma are unavailable.** Character, word, line and command-output token
counts are not substituted for usage.

Available wall-clock boundaries are kept in `phase-observations.json`:

- Architecture merge/readback: 14:46:38–14:47:53 UTC, separate from the pilot.
- Sample selection and initial design: 14:47:53–14:52:29, 4m36s, interleaved;
  their individual elapsed contributions cannot be separated retrospectively.
- Validation infrastructure and proof drafting: 14:52:29–15:00:31, 8m02s,
  also interleaved. It would be misleading to call this all pure proof editing.
- First filesystem edit to corrected sample build: 15:00:31.199–15:02:15.053,
  103.853 s, including validation, the failure and waiting, not pure editing.
- Later rejection tests, retrieval/index tooling, measurements and report work
  overlap command execution. No unsupported pure design/edit/infrastructure time
  attribution is invented. The command ledger gives the separately measurable
  validation/measurement costs; model effort is not measured by that ledger.

The one-time machinery includes explicit proof-evolution/source and added-type
checks, their rejection tests, corpus/index/search tools and the measurement
harness. It is substantial relative to five small lemmas and should not be hidden
inside an assumed marginal extraction price. It is fixed to this pilot's files
and additions, not a production-ready generic evolution framework.

Observed compile-attempt cost: **48.780 s failed first batch + 9.345 s correction
+ 47.478 s completion = 105.603 s**. C8 initially lost `hub`, which was used in the
proof but not its declared statement; Lean required a local `include hub`.
No mathematical hypothesis was weakened to fix it. This illustrates real context
capture cost. The initial small build was ungated; later commands use the serial
gate. Different concurrency/cache states prevent using those attempt times as
before/after performance pairs.

Amortizing just that measured build-attempt cost gives **17.601 s per implemented
lemma attempt (6)** or **21.121 s per retained lemma (5)**. These are shared-batch
averages, not individual measured lemma costs, and exclude model drafting,
infrastructure implementation and final whole validation. Five declined candidates
were considered but never implemented; they are not counted as compiled attempts.
The command/timing JSON also preserves corpus exports, applicability/audit work,
all twelve controlled direct runs and both complete validation runs separately.

All recorded measurement-command wall times plus both complete validation stage
sums total **417.795 s**. Pooled across the pilot this is **69.632 s per
implemented attempt** or **83.559 s per retained lemma**, including the
one-time corpus, benchmark and rejection-test commands. These totals exclude
unmeasured model/infrastructure editing effort, overlap the phase windows and
are not marginal future extraction prices. The ledger separates command categories
so that one-time measurement machinery is not mistaken for proof-edit cost.

One additional tooling iteration cost **0.633 s**: a stronger edit-span guard
rejected adversarial mutations earlier than three tests expected. The test
expectations were corrected by isolating the later guard layers, retaining all
rejection assertions; the corrected 16-test run cost 0.767 s. This was a test
ordering/instrumentation failure, not an accepted bad proof. Both logs are saved.

Dependencies were warm throughout. Changed local modules/dependents were rebuilt;
no Mathlib source build, cache cleaning, or repeat of the expensive Stalks and
UpperSections proofs was needed. The direct measurements were run without a
competing build for the compiler lock. Future costs cannot be forecast from this
small first-time infrastructure-heavy batch alone.

## Validation evolution and final status

The original pristine source units, blob hashes, exporter, DAG reader/comparator,
3902-type reference, sixteen-closure audit and dependency/toolchain pins remain
unchanged. Pristine source coverage is retained as historical reconstruction
coverage; it is not misreported as verbatim active proof identity.

`proof_evolution.py` checks an explicit three-file allowlist, pristine and active
hashes, the exact recorded diff, edit-line spans restricted to the four proof
bodies/five documented additions, literal old theorem headers, no new bypass
commands or attributes, and the separate added-type snapshot binding. Its bounded
span recognizer is not a general Lean parser; full Lean elaboration and type/axiom
exports are independent checks. All other products remain exact pristine
reconstructions. The old 3902 types are compared in full; the exact five additional
names, theorem kinds and types are checked separately. Historical evidence is not
overwritten, and `--record` is an explicit reviewed-update operation rather than
an automatic acceptance path.

Final `bash scripts/check.sh`: **all 32 stages passed**. Old API: 3902/3902, no
missing, added or changed old type. Additions: exactly five/ five theorem types.
The original 16 axiom closures and all nine helper/client closures pass; the main
theorem still has exactly `propext`, `Classical.choice`, `Quot.sound`. The inherited
31 comparator tests, 14 partition tests, 18 root tests and new **16** evolution
rejection tests pass. Root/evolution suites also pass with Python optimization.
The four applicability examples, five docstring checks and six actual production
proof references pass. The index regeneration check and frozen search replay pass.

Reproduce full acceptance from the repository root:

```bash
bash scripts/check.sh
python3 scripts/test_checks.py
PYTHONOPTIMIZE=1 python3 experiments/kl-for-mathlib/test_proof_evolution.py
```

Retrieval and direct-measurement commands are documented in the maintained README
and `measure_samples.py`. [Final logs](evidence/lemma-granularity/final-validation/)
and the [exact proof diff](../experiments/kl-for-mathlib/proof-evolution.patch) are
reviewable. Compiler caches and uncompressed temporary exports stay outside Git.

The pilot supports prioritizing steps with a clear semantic boundary and a real
second consumer. C2 supplies that evidence; C8 exposes the overhead of contextual
extraction. Most observed benefit here is organization and lookup, not total proof
shortening, proven speedup or outside-sample reuse. Independent review, broader
reuse, novelty and upstream API suitability remain unestablished. Publication
checks are reported separately; local validation is not GitHub CI. Only the
architecture round was authorized for merge; this trial remains on its work branch.
