# Independent mathematical steps — expanded pilot, 2026-10-22

Continue `codex/kl-lemma-granularity` from
`0fb4b2ec594b11fed9cd84fc5b1488fa34122f67`. Remote main was and remains
`a234ae5be6f77763e2014aad2cddd69e6aa50755`; no local `main` branch is created or changed; this experiment is not authorized
for merge. One maintained project, `experiments/kl-for-mathlib`, and its caches
are reused. The first round's [report](lemma-granularity.md), plan, original
source reconstruction and evidence remain historical records.

The revised selection criterion is independent mathematical meaning first.
A real second use is a bonus, not a threshold. Moving a coherent argument out
of a main proof can justify an extraction even if the total source grows.
This is a bounded five-proof/eight-lemma expansion, not a whole-library API
redesign or a claim of upstream readiness. The [committed pre-edit plan](lemma-granularity-expansion-plan.md)
and [exact sample/candidate record](evidence/lemma-granularity-expansion/plan.json)
were committed as `7722d8b94920acb017804b1ad2d6f599237623ba` before Lean edits.

## What moved, and what did not

All declaration names below have prefix `OAI.KLInvariance`.

### Reflection displacement (E1, X1)

File: `ForMathlib/LinearAlgebra/Reflection/Plane.lean`.
Original client: `ReflectionPlane.range_preReflection_product_sub_id`.
New lemma: `ReflectionPlane.preReflection_product_sub_id_apply`.

For arbitrary roots α, β and forms f, g over a field, it states

```
((preReflection α f) ∘ (preReflection β g) − id) v
  = (−f v + f β * g v) • α + (−g v) • β.
```

Before, the range proof first established this action formula locally, then
proved the two inclusions. After, it invokes the formula at each inclusion and
retains the surjectivity argument needed to realize arbitrary root coefficients.
The formula needs neither independent forms nor normalized roots; independence
remains exactly where the original range statement needs it. This is a small
computational lemma with a distinct mathematical statement, not an extraction
of the final `module` tactic alone.

### Normalized root-plane coordinates (E2, X2–X3)

Same file. Client: `ReflectionPlane.reflection_triple_in_plane`.
New lemmas: `ReflectionPlane.plane_combination_norm_two_iff` and
`ReflectionPlane.triple_root_norm_two`.

For a symmetric real bilinear form B with B(a,a)=B(b,b)=2, X2 states

```
B (x • a + y • b) (x • a + y • b) = 2
  ↔ x² + B a b * x * y + y² = 1.
```

Given the right-hand quadratic equation, X3 states that

```
d = x • b − (B a b * x + y) • a
```

also has B(d,d)=2. Neither lemma assumes plane nondegeneracy or independence
of a and b. The original proof still chooses plane coordinates, defines d,
proves the two scalar coefficient identities and establishes the operator
identity. Only the coordinate normalization and constructed-root normalization
move out. This makes the proof's stages explicit without pretending that the
remaining triple-product calculation has disappeared.

### Integral support versus annihilation (E3, X4–X5)

File: `ForMathlib/LinearAlgebra/Dual/IntegralSupport.lean`.
Client: `IntegralSupport.supported_iff_annihilates`.
New lemmas: `IntegralSupport.annihilates_of_supported` and
`IntegralSupport.supported_of_annihilates`.

The first direction turns single support at x into annihilation of the kernel
of the stalk projection. It balances the cut, uses its explicit value on a
supported section and cancels a nonzero scalar. The converse uses the perfect
pairing to kill every other cut, then torsion-freeness to kill its coordinate.
The client now combines these two implications directly:

```lean
exact ⟨annihilates_of_supported M p hcut hp d hbalanced x m,
  supported_of_annihilates M p hcut hp d hbalanced x m⟩
```

This split follows two different mathematical arguments, not arbitrary blocks
of equal size. It remains integral: no fraction-field replacement was introduced.
The forward helper still carries an inherited torsion-free typeclass which Lean
reports as unused. This conservative first extraction does not claim minimal
assumptions; removing that ambient parameter can be considered separately before
an upstream API proposal. The old equivalence's type is unchanged.

### Image membership under sheaf isomorphism (E4, X6–X7)

File: `ForMathlib/Combinatorics/MomentGraph/Sheaf/ScaledImages.lean`.
Client: `MomentGraph.Sheaf.Iso.scaledImages`.
New lemmas: `MomentGraph.Sheaf.Iso.mem_lowerImage_iff_symm` and
`MomentGraph.Sheaf.Iso.mem_scaledUpperImage_iff_symm`.

Writing L(B) for the lower map's image of the chosen upward kernel, and U_r(B)
for witnesses `∃ w ∈ kernel, r • upper w = z`, these say

```
z ∈ L(C) ↔ j.edge.symm z ∈ L(B)
z ∈ U_r(C) ↔ j.edge.symm z ∈ U_r(B).
```

The actual lower statement uses the existing `Submodule.map`; ordinary sheaves
have no `lowerImage` shorthand. X6 is intentionally a thin membership interface
built from existing `map_lowerImage` and Mathlib's `Submodule.mem_map_equiv`.
It is not claimed as new mathematical content. X7 packages the scalar witness
and commuting-square reasoning for arbitrary r, including zero. The client now
composes these two equivalences with the given scaled-image equivalence. Its
former duplicated witness transport no longer hides the conceptual argument.

### A complementary root spanning the plane (E5, X8)

File: `OAI/KL/Localization/TerminalImages.lean`.
Client: `TitsSpace.PlaneBasis.coset_structure_scaledImages`.
New lemma: `TitsSpace.PlaneBasis.exists_root_plane_complement`.

Given a plane basis B and a positive root α with α.val ∈ P, the conclusion is
`∃ β, α ≠ β ∧ rootPlane α β = P`. The proof chooses one of B's two basis roots
and establishes the span equality. The client now obtains that witness in one
step before handling label reduction, supported counts and the unsupported
edge case. The helper needs no scheduling, sheaf or interval-comparison data.
It stays in the existing application file in this round: choosing a more general
API home or changing the dependency graph is not part of this experiment.

## Decisions, semantic information and actual use

Eight preselected points were retained. Four other candidates were declined:
scalar base-change relocation would require API placement work; direct character
simp branches hide no substantial argument; splitting the triple-product's final
scalar identities would fragment a coherent calculation; model-sum interface
redesign is beyond extraction. Their reasons are recorded before implementation.
These judgments are not established by compilation alone.

Lean docstrings remain the explanatory authority. The generated
[LEMMA_INDEX.md](../experiments/kl-for-mathlib/LEMMA_INDEX.md) adds source-parent
links, lookup keywords, extracted responsibilities and applicability notes from
one small provenance index. There is no second formal specification, per-file
Markdown mirror or new retrieval service. All thirteen indexed lemmas across
both rounds must match compiled source docstrings on regeneration.

The expansion has eight distinct original-client → helper relationships and no
observed second production consumer. The displacement formula is invoked twice
inside E1; that is not a second consumer. Across both rounds: thirteen original
client/helper relationships plus the one second production relationship from the first round. That pair remains wholly within
the first four samples. Outside-sample production reuse is still zero. Kernel
proof-expression checks test each of the fourteen expected direct constant-reference
relationships; this checks presence, not expression-occurrence counts. Transitive downstream dependency is not counted as an additional use.

Eight new applicability checks cover dependent forms on a one-dimensional
rational vector space; coincident normalized roots (both normalization lemmas);
the two directions of integral support; a lower-image isomorphism round trip;
scaled upper membership at scalar zero for an arbitrary isomorphism; and a
complement to the left basis root. These are tests, not production consumers or
independent mathematical certification.

## Validation and measurements

Final executed results are recorded below. The exact toolchain
remains Lean 4.34.1 (`5045d0056413266e57c625dcd7c365b10e377c52`), with Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`. No dependency update, Mathlib source
build, cache cleaning or second project is used.

The frozen old 3902-type snapshot, exporter/comparator and pristine source
coverage remain intact. The exact first-round added-type and source-evolution
records are retained and hash-bound separately. The cumulative evolution policy
lists nine old proof bodies, thirteen additions and seven source files; the
first round's three files additionally remain frozen to their previously tested
active hashes. An exact zero-context unified diff binds the source exceptions
without whitespace-only context lines. Headers, edit spans, no-bypass tokens,
attributes, complete type export and axiom closures remain separate checks.
The edit-span recognizer is bounded, not a general Lean parser. A narrowly
specified existing `include hp hbalanced in` prefix must be admitted because
diff alignment can put its repeated insertion immediately before the old docstring;
no arbitrary scope-command edits are permitted. Existing rejection tests are
retained and four tests add frozen first-round source/types and expansion-specific
unsampled-proof/old-statement mutations.

The first-round infrastructure is reused. Incremental tooling is limited to
explicit expansion bindings, those four rejection cases, expanded doc/index/call
checks and an expansion option on the existing measurement script. This does
not include building a general evolution framework or benchmark platform.

Model token telemetry is unavailable. Neither source lines, command-output tokens
nor character counts are substituted. Selection/design, proof editing and guard
adaptation are interleaved; only available UTC boundaries and actual command wall
and CPU times are reported, without inventing a pure model-editing time split.


## Reproduction commands

From the repository root, the full acceptance command remains:

```bash
bash scripts/check.sh
python3 scripts/test_checks.py
PYTHONOPTIMIZE=1 python3 experiments/kl-for-mathlib/test_proof_evolution.py
```

For lookup/index regeneration and the optional single direct-measurement pair,
see the maintained project's README. The original semantic search is extended
only with `--expansion`; it uses these six committed queries without declaration
names. All rankings are word overlap over exported project theorem names and
docstrings, not mathematical relevance proof, theorem-type search, embeddings
or a blind benchmark. Before/after target sizes differ. The author knew the
queries while writing docstrings; document removal is a controlled vocabulary
ablation, not independent testing.

The exact cumulative mathematical diff is
[`proof-evolution.patch`](../experiments/kl-for-mathlib/proof-evolution.patch);
[proof-structures.json](evidence/lemma-granularity-expansion/proof-structures.json)
retains each expansion client's original/final proof body and the extracted
bodies separately. Use Git at the pinned first-round commit for full context.
No historical record is relabelled as new validation. Publication status and
GitHub checks are reported separately from local Lean acceptance.

## Source volume is descriptive, not the selection objective

| Sample | Old client body | New client body | Extracted bodies |
| --- | ---: | ---: | ---: |
| E1 displacement/range | 18 | 12 | 3 |
| E2 triple reflection | 43 | 35 | 8 |
| E3 support/annihilator | 15 | 2 | 14 |
| E4 image transport | 22 | 3 | 12 |
| E5 complementary root | 27 | 22 | 6 |
| Total | 125 | 74 | 43 |

These are nonblank uncommented proof-body lines, excluding top-level signatures
and docs. Local `have` statements remain part of the old client-body count while
new top-level signatures are excluded, so this is not a symmetric measure of
all proof material. No line count measures mathematical complexity or tokens. The four whole files
increase from 786 to 840 physical lines. Client-plus-helper bodies are 117 lines
versus 125, with part of the reduction coming from reusing an existing image-map
API. Neither that small net reduction nor the larger total files decides whether
a mathematical boundary is useful. The concrete responsibility changes above
are the assessment; no outside-sample reuse or independent review is implied.

## Fixed-query lookup observations

Baseline corpus: 2587 project-owned public theorems; final: 2595. The final search
code reproduces all frozen baseline rankings exactly. The corpus excludes the
full external Mathlib collection, theorem types and proof bodies. The baseline
column ranks the original parent proof, while the other columns rank a new
lemma; these are different retrievable units. The ablation removes only this
round's eight docstrings from the final corpus, keeping all names and prior docs.

| Fixed query | Old parent rank | New target rank | Target without its new docstring |
| --- | ---: | ---: | ---: |
| two reflection product displacement root span | 1 | 1 | 17 |
| normalized root plane quadratic combination norm | 3 | 1 | 1 |
| single support annihilator stalk projection kernel | 4 | 2 | 99 |
| isomorphism lower image inverse edge membership | no word match | 1 | 9 |
| scaled upper image inverse isomorphism scalar | 66 | 1 | 4 |
| complementary positive root spans given plane | 316 | 4 | 53 |

For the quadratic query the new name alone gives the observed rank; do not
credit docstrings for that result. The other ablations show additional useful
matching vocabulary. The complementary-root target still ranks fourth, and the
support target second: this remains a small lexical tool with no stemming or
mathematical relevance guarantee. Queries were known during documentation;
these observations are neither a blind study nor statistical evidence. Full
rankings, ablations, compressed corpora and target identities are retained in
[search-comparison.json](evidence/lemma-granularity-expansion/search-comparison.json)
and the adjacent evidence files. No docstrings were retuned after these results.


## Executed acceptance

`bash scripts/check.sh` passed all **32 stages**. The 3902 original public types
have no missing, extra or changed type; the five first-round added records remain
identical. Exactly eight additional theorem types are recorded independently in
[eight-new-types.json](evidence/lemma-granularity-expansion/eight-new-types.json),
with all thirteen additions required by the complete 3915-declaration export.
No original statement is weakened. The first-round three active files remain
byte-for-byte frozen; this round changes only the four selected mathematical files.

The original sixteen named axiom closures and all 22 pilot helper/client closures
pass the allowlist. The main theorem still has exactly `propext`,
`Classical.choice`, `Quot.sound`. All thirteen helper docstrings and all fourteen
expected client/helper proof-reference relationships pass. The original four and
new eight applicability checks pass. No global simp registration, custom tactic,
`sorry`, new axiom or unsafe bypass is introduced.

The inherited 31 comparator tests, 14 partition tests, 18 root regression tests
and cumulative 20 evolution tests pass. Evolution and root suites also pass with
Python optimization. The generated index passes its source/compiled-docstring
check; the six frozen-query rankings reproduce before the after/ablation runs.
Final stage logs are in [final-validation](evidence/lemma-granularity-expansion/final-validation/).
The toolchain/dependency pins, old snapshot/exporter/comparator, provenance,
source-coverage algorithm and first-round evidence were checked unchanged against
`0fb4b2e`. Local validation is not GitHub CI; remote checks are reported at delivery.

## Direct elaboration and incremental costs

One sequential before/after pair per containing module, the same temporary input
filename, pinned toolchain and already-warm **current** dependencies, with the
serial compiler gate. Both inputs are elaborated from source, not accepted from
an input `.olean`. No other own build competed during these measurements. These
modules contain other declarations besides the selected samples. Before-source
hashes match the pre-edit plan/pristine reconstruction; this is not a cold or
complete historical-project build.

| Module | Before seconds | After seconds | Descriptive change |
| --- | ---: | ---: | ---: |
| Reflection/Plane | 5.754 | 5.483 | −4.71% |
| Dual/IntegralSupport | 5.610 | 5.631 | +0.37% |
| Sheaf/ScaledImages | 5.103 | 5.259 | +3.05% |
| Localization/TerminalImages | 5.413 | 5.411 | −0.03% |

Single ordered pairs include startup, cache/order effects and timing noise. They
cannot establish speedup, statistical significance or absence of a regression.
The small observed differences did not justify additional benchmark iterations.
The final warm library rebuild was **4.761 s**, a separate workload.

The measured build ledger preserves **144.265 s failed first build + 8.673 s
failed correction + 14.577 s successful changed-module build + 1100.242 s full
downstream build = 1267.757 s**. The failed first build also completed valid
independent/dependency work which the next run reused; it was not restarted cold.
The first error used a nonexistent ordinary-sheaf `lowerImage` shorthand; the
second exposed the witness/coercion proof fragility. Reusing existing
`map_lowerImage` with `Submodule.mem_map_equiv` fixed that integration and produced
the final one-line lower membership proof. No genuine failure of the unchanged
upstream mathematics was encountered.

A separate **5.453 s** applicability-harness failure came from an underconstrained
`LinearMap.id` in the rational example. An explicit type fixed it; the corrected
check cost **5.189 s**. No mathematical source or expensive downstream artifact
changed for that correction. These three failed measured commands total
**158.391 s**. The wrong-working-directory preflight and the bounded include-prefix
guard adaptation are additionally recorded in `phase-observations.json`; they
were not metered by the command harness. A formatting check also exposed blank
context lines in the serialized diff; zero-context rendering fixes the artifact,
not the Lean proof. No test failure or denial is concealed as a pass.

The full 32-stage validation wrapper cost **106.675 s** (sum of recorded stage
walls **106.231 s**). All measured expansion command walls, including metadata,
eight direct elaborations, failure iterations and optimized tests, total
**1477.451 s**; validation stages are not added again to their enclosing wrapper.
These sums exclude unmetered model/editing/read/report effort and are not a
complete task-time or compute-price meter. The separate command wall/CPU rows
are retained in [measurements.jsonl](evidence/lemma-granularity-expansion/measurements.jsonl).

Amortizing only shared build attempts gives **158.470 s per retained lemma (8)**
or **126.776 s per implemented attempt (10: eight implementations plus two
transport-proof retries)**. The harness correction is counted separately from
lemma implementation. These are batch averages, not measured individual costs
or predictions of marginal future cost. Four declined candidates were not coded.

The first round's substantial infrastructure is reused and excluded from this
round's ledger. Incremental guard/index adaptation and documentation are real
costs but not separately timed from editing/waiting. The first observed UTC clock
is 00:32:17; plan commit 00:33:03; first changed-module build 00:34:00; successful
module build 00:37:57; complete downstream build 00:56:23; controlled measurements
finished 01:00:30. These overlapping windows are not pure selection/design/edit
phase estimates. No reliable token-usage tool is exposed: **model token cost is
unavailable**, not estimated from source or command-output size.

The major observed cost is dependency invalidation from editing low-level modules:
Stalks and UpperSections genuinely recompiled (the latter Lake job reports 653 s;
a historical matching source build reports 641 s). Those per-job figures may
include queue/lock waiting and must not be summed as independent CPU costs.
No new Lean/Mathlib installation, Mathlib source build, cache cleaning or second
project was needed. Unchanged source modules were preserved; invalidated artifacts
were rebuilt rather than relabelled. Future scheduling should account for that
dependency breadth, rather than treating the 18-minute downstream build as the
intrinsic elaboration price of eight short lemmas.

## Assessment and remaining limits

This expansion supports keeping single-consumer lemmas when their mathematical
responsibility is clear: the support converse, coordinate normalization and
complementary-root witness are concrete examples. The thin lower-image interface
has a different value: exposing an existing transport theorem in the form used
by its client. It should not be sold as newly discovered mathematics. The remaining
triple-reflection operator argument is deliberately not fragmented further.

The result supplies reusable, findable material and clearer client proof stages;
it does not establish external reuse, API novelty, minimal assumptions for every
helper, independent review, upstream acceptance or long-term automation stability.
One inherited redundant typeclass in the forward support helper is explicit
placement/assumption debt. No new general API hierarchy or wider file reorganization
was attempted. The branch is ready for independent review, not automatically
approved for merge.
