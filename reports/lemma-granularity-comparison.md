# Comparison-pipeline extraction — 2026-10-22

Work branch `codex/kl-lemma-granularity`, starting at
`bdcb35071c4790585beb47f7f28798ece8ed58d9`. Remote main remains
`a234ae5be6f77763e2014aad2cddd69e6aa50755`; no merge is authorized here.
The sole maintained project and dependency caches are reused in place.
The [pre-edit plan](lemma-granularity-comparison-plan.md) records six original
proofs, eight retained extraction points and four declined candidates, committed
before Lean edits. Exact names/hashes/queries are in
[plan.json](evidence/lemma-granularity-comparison/plan.json).

The criterion remains independent mathematical responsibility and meaningful
complexity moved out of a client, with a second consumer as a bonus. This round
batches three application-level comparison files; no low-level Stalks or
UpperSections source changes, general API redesign or file reorganization is made.
The prior round's source-only review did not rerun Lean and does not constitute
independent review of this round. Its assumption/placement debts are retained,
not silently changed: support's redundant torsion-free class, stronger-than-needed
pairing data, and the geometric complement helper's heavy import home.

## Mathematical boundaries and before/after structure

Names below share prefix `OAI.KLInvariance.BruhatGraph`.

| Sample | Old client | Extracted lemma(s) |
| --- | --- | --- |
| P1 | `transported_dispatch_entry` | `adapted_path_sources_le` |
| P2 | `scaledStalk_reciprocity_inverse` | `stalkCharacter_reciprocity_eval`, `scaledStalk_rTilde_term`, `reciprocal_square_weight` |
| P3 | `scaledStalk_reciprocity_upper` | `rTilde_weighted_sum_upper` |
| P4 | `costalkEquivDual_symmetric` | `costalk_pairing_scaled` |
| P5 | `normalized_fullKernel_of_duality_character` | `fullKernel_hilbert_of_duality_character`, second use of `reciprocal_square_weight` |
| P6 | `schedule_kernels_free_of_images_eq` | `schedule_head_kernels_free` |

### Transport: path bounds, reciprocal evaluation and triangular sums

File: `OAI/KL/Comparison/Transport.lean`.

P1 previously proved the source bound by list induction inside a dispatch graph
embedding proof. `adapted_path_sources_le` now states that for a Bruhat path from
z to w, every edge source lies above z. It has no schedule/isomorphism data or
finite-generator assumption. The client retains graph embedding, schedule
ordering and edge-lifting obligations; its last lifting obligation calls this
path bound and the existing target bound. This extracts the monotonicity argument,
not the subsequent graph-embedding API application.

P2 previously mixed reflected-polynomial evaluation, degree bookkeeping and
summand normalization in one proof. The extracted evaluation identity is

```
(v²)^rankDifference(x,b) · stalkCharacter(x)((v⁻¹)²)
  = ∑ z, OrdinaryR(x,z)(v²) · stalkCharacter(z)(v²),  v ≠ 0.
```

The actual Lean statement uses `Polynomial.eval₂ (Int.castRingHom C)` over a
field C. The proof constructs a square unit, uses the existing stalk degree bound
to evaluate reflection, and converts its inverse to the inverse square.
The client then applies the grading weight and assembles the sum.

`scaledStalk_rTilde_term` independently packages each summand:

```
v^(length(x)−length(b)) · (OrdinaryR(x,z)(v²) · stalkCharacter(z)(v²))
  = rTilde(x,z)(v−v⁻¹) · scaledStalk(v,z).
```

It retains R-polynomial normalization and addition of grading exponents, for
arbitrary interval vertices, without adding comparability or positivity.
The original sum proof now invokes this interface for each z.

The genuinely repeated scalar calculation is

```
v^(m−n) · (v²)^(n−m) = (v⁻¹)^(m−n),  v ≠ 0,  m n : ℤ.
```

`reciprocal_square_weight` supplies it to both P2 and P5. P2 still explicitly
converts the natural rank difference to the integer length difference; the
helper does not hide that geometric fact. P5 uses it directly for the Hilbert
grading exponent. The new helper has a field signature, not a positivity premise.
It currently lives in the existing pipeline namespace; upstream placement,
duplicate search and a general scalar API proposal remain future work.

P3 previously combined polynomial reciprocity with filtering a full interval sum,
proving off-upper terms vanish and reindexing a subtype. The new statement is

```
∑ z∈[1,b], eval(T, rTilde(x,z)) · w(z)
  = ∑ᶠ z∈[a,b], eval(T, rTilde(x,z)) · w(upperInclusion(z)),  x∈[a,b].
```

`rTilde_weighted_sum_upper` accepts arbitrary weights in a commutative ring,
not only field-valued scaled stalks. It uses triangular support, the filtered
sum and the explicit upper-interval equivalence. It needs no finite-generator
assumption. P3 now rewrites the reciprocal identity and applies this weighted-sum
lemma with scaled-stalk weights. No new general reindexing framework is introduced.

### Propagation: pairing compatibility and raw Hilbert information

File: `OAI/KL/Comparison/Propagation.lean`.

For the costalk duality e, single-supported lift f and incoming label product g,
`costalk_pairing_scaled` states

```
g · (e k)(l.val) = d.pairing (f k).val (f l).val.
```

P4 previously established this locally using scalar linearity, the explicit lift
value and the existing section-pairing compatibility, then used symmetry and
cancelled g. The compatibility calculation now has its own statement without
symmetry or finite sigma. P4 retains precisely symmetry and nonzero-product
cancellation, calling the lemma in both orders. Those two invocations within one
client do not count as a second production consumer. The contextual SectionDuality
API remains; this is not a claim of a minimal general bilinear-form interface.

`fullKernel_hilbert_of_duality_character` exposes the raw expression

```
kernelHilbert(q,x,univ)
  = q^(length(b)−length(x)) · eval(q⁻¹, klPolynomial(x,b)) · ((1−q)⁻¹)^card(σ),
  0 < q < 1.
```

It chooses a nonnegative homogeneous basis, identifies its polynomial with the
stalk/KL character and applies the existing costalk Hilbert theorem. P5 now
starts from this expression at q=t² and retains only the state normalization,
reciprocal square weight and elementary denominator cancellation. The chosen
basis does not leak into the new statement; no new duality theory is invented.

### Suffix freeness: the mathematical induction step

File: `OAI/KL/Comparison/SuffixFreeness.lean`.

`schedule_head_kernels_free` states that adding one reverse-schedule edge preserves
freeness at every vertex, given all previous kernels free and the embedded image
equality for that edge. At its source it installs the previous source and target
free modules and applies the existing partial-kernel theorem. At other vertices
it uses the unchanged remaining condition set. P6 retains empty-list treatment,
suffix induction and restriction of the image-equality hypothesis. It delegates
the complete one-edge preservation argument rather than arbitrary chunks of the
induction bookkeeping.

## Selection, semantic lookup and actual calls

Four candidates are declined: upper-suffix set wrappers would restate existing
cutoff/pullback interfaces; positivity and elementary scalar cancellation already
have suitable facts; a separate chosen-basis polynomial lemma would add context
for three existing rewrites; changing the previous support assumptions or moving
the root helper is frozen API work outside this round. Eight points are retained
for the responsibilities above, not to reach a quota.

Short Lean docstrings remain authoritative. The generated
[LEMMA_INDEX.md](../experiments/kl-for-mathlib/LEMMA_INDEX.md) links each of the
21 helpers to its current client and pinned original file, with role/keywords and
applicability scope. There is no second formal specification or per-file Markdown
mirror. All 21 explanations match compiled docstrings on regeneration.

Nine new direct client/helper relationships are checked in kernel proof expressions:
eight original sites plus P5's second use of the square-weight helper. Both consumers
are among this round's six samples. Across all rounds there are 21 original
client/helper relationships and two second-production relationships (23 total),
all within planned samples. **Outside-sample production reuse is still zero.**
Presence checks do not count expression occurrences; the displacement lemma from
the prior round and the pairing lemma here each occur twice inside one client.
Transitive dependence and test examples are not counted as new production reuse.

Nine new applicability examples cover a one-edge path without finite generator
data; negative rational evaluation; the diagonal normalized summand; a negative
point/negative degree square weight and equal-degree boundary; integer-valued
arbitrary weights; a diagonal costalk pairing without symmetry or finite sigma;
the raw expression at q=1/4; and the one-edge schedule from empty conditions.
These are interface/edge-condition examples with symbolic data, not independent
mathematical certification or additional production consumers. No claim of a
full family of concrete Coxeter examples is made.

Eight queries were fixed before editing. Search is the same deterministic
IDF-weighted word overlap over exported project theorem names and docstrings,
excluding full Mathlib, theorem types and proof bodies. The author knew the queries;
this is a reproducible **nonblind** check. Baseline rankings replay identically.
The baseline has 2595 theorems, the final corpus 2603. Before ranks the parent,
after ranks a new lemma: these are different retrievable units. The ablation
removes only the eight new docstrings, retaining prior thirteen and all names.

| Fixed query | Parent before | Target after | Target without its new docstring |
| --- | ---: | ---: | ---: |
| increasing Bruhat path source above start | 285 | 1 | 14 |
| reflected stalk polynomial reciprocal evaluation | 30 | 1 | 43 |
| normalized R polynomial scaled stalk summand | 12 | 1 | 3 |
| inverse square degree weight identity | 29 | 1 | 2 |
| upper interval triangular weighted sum | 134 | 1 | 1 |
| incoming label costalk section pairing | 11 | 1 | 3 |
| full kernel Hilbert reciprocal character | 1 | 1 | 1 |
| one edge reverse schedule kernel freeness | 12 | 1 | 125 |

Naming alone supplies the observed target ranks for weighted sums and raw Hilbert
information; do not attribute those to docstrings. The other ablations show useful
matching vocabulary, not blind relevance or statistical evidence. No descriptions
were retuned after reading the rankings. Full corpora/results and target identities
are in [search-comparison.json](evidence/lemma-granularity-comparison/search-comparison.json)
and adjacent compressed evidence.

## Source volume, validation policy and evidence

| Sample | Old client body | New client body | New helper bodies |
| --- | ---: | ---: | ---: |
| P1 | 30 | 18 | 9 |
| P2 | 36 | 16 | 26 |
| P3 | 24 | 3 | 23 |
| P4 | 12 | 4 | 8 |
| P5 | 36 | 21 | 10 |
| P6 | 27 | 14 | 12 |
| Total | 165 | 76 | 88 |

Client-plus-helper bodies are 164 versus 165 lines; whole mathematical files grow
from 1610 to 1696 lines. Counts exclude top-level signatures/docstrings but include
local `have` signatures inside old clients, so they are not a symmetric measure of
all proof material. They measure neither mathematical complexity nor tokens.
The responsibility changes above, not net line reduction, decide the assessment.
Full before/after bodies are retained in
[proof-structures.json](evidence/lemma-granularity-comparison/proof-structures.json).

Lean remains 4.34.1 (`5045d0056413266e57c625dcd7c365b10e377c52`), Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`. No setup reinstall, pin change,
Mathlib source build, cache clearing or second project is needed. The old type
snapshot/exporter/comparator, original provenance and source-coverage algorithm
remain intact. The previous thirteen added-type records and seven active source
hashes are retained, hash-bound and frozen. Eight new types are listed separately.

The cumulative evolution lists 15 old proof bodies, 21 additions and ten source
exceptions. It retains hash/diff/source allowlists, no-bypass and attribute checks,
complete export checks and literal old headers. A line diff can align a reused
proof body with a new theorem and treat the unchanged old header as moved. Selected
old header lines are therefore admitted in the bounded diff regions, **then their
literal bytes are independently compared**. The new negative case changes an old
header and rebinds the source manifest without mocking the span checker; it still
fails. Other new cases reject changes to a second-round source/type and an unselected
comparison proof. Older tests remain, with prior-freeze layers isolated only where
necessary to exercise the later guards. This bounded recognizer is not a general
Lean parser; it is combined with complete kernel type and axiom checks.

Two new unused finite-generator premises were omitted before recording new types,
following actual linter output. Those exact prefixes are explicitly listed and
checked; no old type changes. The existing source-only review debts are untouched.
The failed verification action in this round is the initial old-header diff-alignment
check; its exact target/reason and unmetered status are recorded with phase evidence.
No genuine unchanged-source failure or permission denial occurred.

Full `bash scripts/check.sh` passes all **32 stages**. The original 3902 types and
all previous thirteen added records remain unchanged. Exactly eight new theorem
types are recorded in [eight-new-types.json](evidence/lemma-granularity-comparison/eight-new-types.json),
with all 21 additions required in the 3923-declaration export. Original sixteen
axiom closures and all 36 cumulative pilot helper/client closures pass. Main still
has exactly `propext`, `Classical.choice`, `Quot.sound`. All original and new
applicability/docstring/direct-reference checks pass. No `sorry`, new axiom,
unsafe bypass, global simp registration or custom tactic is introduced.
The 31 inherited comparator tests, 14 partition tests and cumulative 24 evolution
tests pass. The 18 root regression tests pass, and both root/evolution suites
also pass with Python optimization.
The current mathematical code has not received an independent source review or
independent rerun. Local cloud validation is separate from GitHub CI.

Reproduce from the repository root:

```bash
bash scripts/check.sh
python3 scripts/test_checks.py
PYTHONOPTIMIZE=1 python3 experiments/kl-for-mathlib/test_proof_evolution.py
```

Current metadata, query and optional `measure_samples.py --comparison` commands are
in the maintained README. The exact cumulative mathematical diff is
[`proof-evolution.patch`](../experiments/kl-for-mathlib/proof-evolution.patch).
Prior reports/evidence are preserved as historical records, not relabelled as new
runs. Publication and check status are reported for the exact remote head at delivery.


## Controlled elaboration and incremental cost

One ordered source pair per containing file, same temporary input filename,
pinned toolchain and warm **current** dependencies, no input `.olean` reuse and no
other own build competing for the serial compiler gate:

| Containing file | Before seconds | After seconds | Descriptive difference |
| --- | ---: | ---: | ---: |
| Transport | 5.806 | 5.840 | +0.58% |
| Propagation | 10.521 | 9.783 | −7.02% |
| SuffixFreeness | 5.852 | 5.930 | +1.33% |

These measure whole modules including unchanged declarations and process startup,
not individual extracted lemmas. Before-source hashes match the plan/pristine
reconstruction; imports use current warm dependencies, not a cold historical
checkout. Ordered pairs include cache/order effects and noise. One pair does not
establish speedup, statistical significance or absence of regression. The observed
differences did not justify more benchmarking. The warm library rebuild was
**4.682 s**, a different workload.

The initial eight implementations compiled together successfully in **39.376 s**.
Linter-guided removal of two redundant new finite-generator premises used a second
successful shared build of **37.194 s**; that is an assumption-cleanup iteration,
not a failed proof attempt. Remaining downstream compilation cost **32.792 s**.
All measured compile/check commands succeeded. The unmetered source-span alignment
failure and its correction are explicitly recorded in
[phase-observations.json](evidence/lemma-granularity-comparison/phase-observations.json).
No mathematical source failure, failed applicability example or permission denial
occurred. The test harness has a local interval Fintype instance derived from the
existing finiteness theorem; no production instance is added.

Total shared build-command wall time is **109.363 s**, or **13.670 s per retained
lemma** when amortized over eight implementations. That is not an individual cost
measurement or marginal future price. The four declined candidates were not coded.
Full 32-stage validation cost **109.601 s** (stage walls sum **109.166 s**).
All measured comparison-round command walls total **312.114 s**, including metadata,
all six direct elaborations and normal/optimized tests. Validation stages are not
added again to their enclosing wrapper. Raw wall and CPU records, logs and the
input-hash protocol are in the evidence directory; this is not a billing meter.

The previous rounds' tooling is reused, not charged again to this ledger. New
binding/span/test/index adaptations, selection, model drafting, editing and report
work are real costs but not separately metered. First observed UTC clock: 01:40:06;
first module build: 01:45:06; cleanup complete: 01:47:44; downstream complete:
01:49:28; complete validation: 01:54:27; controlled measurements complete: 01:55:39.
These are available overlapping boundaries, not pure design/edit time estimates.
Model token telemetry remains **unavailable**; source length and command-output
counts are not substituted for tokens.

The practical cache observation is that this batch stayed above the expensive
foundational modules. Neither Stalks nor UpperSections recompiled; the prior round
had genuinely invalidated them. This is a dependency-scope difference, not proof
that extraction became intrinsically faster or that this batching strategy always
has a particular speedup. It supports planning related edits together before one
validation pass, while preserving the full source/type/axiom acceptance.

## Assessment and limits

The clearest responsibility splits are reciprocal polynomial evaluation versus
summand normalization, triangular support versus the chosen weights, pairing
compatibility versus symmetry, raw Hilbert information versus scalar normalization,
and a one-edge mathematical preservation step versus suffix induction. P2/P5 also
supply actual shared use of the same scalar identity. The main proofs become
structured compositions while the extracted statements describe their own role.

This is evidence of useful organization and findable material, not evidence of
outside-sample production reuse, novelty, upstream readiness, minimal assumptions
for every contextual interface, or independent mathematical certification. Generic
scalar-helper placement and the earlier API debts remain explicit future design
material. No complete API hierarchy or whole-library architecture pass is attempted.
The result is ready for independent review on its work branch; it is not merged.
