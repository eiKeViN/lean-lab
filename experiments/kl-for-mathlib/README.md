# KL formalization

The single maintained Lean project. Continue updating this directory in place.
Earlier stages through `85b3d1a4fa9c4f08beb718d8925d2d0ec9c50060` remain
recoverable from Git history; their experiment directories have been removed.
That consolidation preserved the mathematical source and interfaces. Subsequent
file-responsibility refinements are recorded below and in the current report.

`ForMathlib/` contains 181 implementation modules that can presently form a
standalone dependency layer: general algebra/linear support, Coxeter geometry,
ordered paths and moment-graph sheaves, Hecke and equal-parameter KL polynomial
theory, and the existing Tits Bott word model. This includes specialized research
mathematics; subject specialization is not a reason for exclusion.

`OAI/KL/` contains 25 application modules plus the kernel-name wrapper:
Tits stalk/pairing/character constructions, basis-specific boundary/duality
models, localization bridges, comparison propagation and finite/parabolic model
assembly. Their mathematics may also be suitable upstream; their current
interfaces/dependencies remain tied to this proof architecture. Extracting
future general interfaces is outside this round.

`ForMathlib` must not import any `OAI` module, including compatibility imports.
This is our project architecture rule, not an official prescribed Mathlib
ForMathlib layout. `ForMathlib.lean` imports every candidate; `OAI.Architecture`
imports every implementation. Declaration namespaces and public types remain
compatible (`OAI.*`); candidate staging does not rename mathematical APIs.

Original 34 KL module import entrypoints and the two existing kernel import
entrypoints are import wrappers. Published paths retired by responsibility
refinements also forward to precise implementations; there are 51 compatibility
entries in total. Earlier semantic import paths are available in
the pinned historical Git trees.
The maintained project uses the paths in CLASSIFICATION.md and does not add
another 193 import wrappers.

Use `import OAI.KL` for the main application theorem, or a focused ForMathlib
module for reusable support. [MODULES.md](MODULES.md) indexes all 207 current
implementations and the compatibility paths. `OAI.Architecture` is the complete
audit/export umbrella; `ForMathlib` loads the entire candidate layer. The
[whole-library report](../../reports/whole-library-layout.md) records the full
review and remaining placement debt. File organization is iterative: a full
review is not a claim that no further refinement will ever be useful.

The classification follows the official guides consulted on 2026-10-21:
[scope and AI policy](https://leanprover-community.github.io/contribute/index.html),
[review criteria](https://leanprover-community.github.io/contribute/pr-review.html),
[naming](https://leanprover-community.github.io/contribute/naming.html) and
[style](https://leanprover-community.github.io/contribute/style.html).
Candidates still need duplicate/API searches, suitable namespace/naming and
assumption review, focused Mathlib imports, proper docs and human/maintainer
review. This round does not establish that any file is PR-ready or accepted.
No Mathlib PR or community comment is published.

Changes to file responsibility preserve complete declarations and proofs:

- Polynomial files now use `Algebra/Polynomial`. Generic functional avoidance
  belongs to `LinearAlgebra/Avoidance`.
- Quotient descent and induced quotient equivalences share
  `LinearAlgebra/Quotient/Transport`; pair-projection basic/kernel/lifting tools
  share `LinearAlgebra/PairProjection`.
- Reflection evaluation and reciprocal rigidity share `Polynomial/Reciprocal`.
- The former mixed scaled-comparison file separates polynomial transfer
  evaluation, ordered-field real-power scalar identities and scaled polynomial reciprocity.
- `BigOperators/SingleCoordinate` puts the existing finite cancellation and
  weighted-difference lemmas together; `Polynomial/ScaledEvaluation` contains
  the scaled evaluation and its reciprocal rigidity, without weighted sums.
- `Module/Submodule/ProductScaling` describes scalar images and associated
  finite products over arbitrary algebra extensions; it needs no localization.
- The dihedral Hecke/KL polynomial bridge is located with KL polynomials.
  Concrete word coordinates are named `BottSamelson/TitsWords`.
- Project filenames state their roles: `SuffixFreeness`, `GraphEmbedding`,
  `TerminalImages`; general plane models and finite-rank reduction live below.
- Weighted-basis grading, polynomial-map grading and multiplication homogeneity
  now have distinct files; homogeneous equivalences and finite pieces do not
  import structured pair-projection or coefficient-change constructions.
- Ordinary sheaf isomorphisms, products, pullback, base change, structure and
  restriction sit below graded sheaf constructions. The old mixed umbrellas
  remain compatibility imports. Graph deletion has an explicit home; its
  residual GraphEquiv/reindex dependency is documented in the report.
- Nondegenerate bilinear-form extensions sit apart from reflection relations.
  Hilbert numerator identities do not claim a rational-function interface.
- Bott upper-section projectivity, stalk-character recurrences and interval
  projection-sheaf flabbiness are separate application responsibilities.
- Graded stalk splitting and bijectivity under minimal-cover conditions share
  `GradedSheaf/StalkMaps`; their former ordinary-sheaf paths are compatibility
  imports. All current ordinary-sheaf implementations, including localization,
  remain below grading.

The architecture migration rewrote no mathematical statement or proof body.
The active [library extraction round](../../reports/lemma-granularity-library.md)
has forty-five added lemmas and thirty-six rewritten old proofs across four rounds.
All 3902 original API types and the previous twenty-one added types are preserved;
twenty-four further types are separately recorded in the cumulative snapshot.
`proof-evolution.json` binds twenty-one precise source exceptions and their exact diff;
the previous ten remain additionally frozen to the tested `a0b5b59` active hashes.
All other products remain pristine reconstructions. One exact same-layer integration
import, `Hilbert.Series → Hilbert.Numerator`, reuses `hasSum_shift_coeff` in two
old clients instead of adding a duplicate lemma. This edge is bound by the revised
library plan and included in dependency checks; the pristine migration is unchanged.
The earlier 76 explicit
instance-name annotations and single local instance attribute are inherited.
`migration.json` and `migrate.py --check` bind all 525 immutable parent units and
fixed sources to the pristine reference history. One mixed parent is partitioned
at a complete declaration boundary into two hashed pieces, covering its original
bytes exactly once and copying only existing opening/closing scope frames.
There are 526 allocated pieces. `source_check.py` verifies full source coverage;
14 focused partition tests include malformed and incomplete allocations.
`CLASSIFICATION.md` indexes every prior module with actual declaration references;
`upstream-assessment.json` records current rationale and remaining preparation.
`DEPENDENCIES.dot` and `layout-metrics.json` reproduce dependency boundaries.

From the repository root:

```bash
bash scripts/setup.sh
bash experiments/kl-for-mathlib/check.sh
```

For static checks: add `--static`. With warm OAI and candidate artifacts:
`--checks-only`. `--verify-baseline` verifies Git baselines and retained export
evidence without running Lean. The old `--refresh-reference` option is retired;
there is no second project to recompile.
The unchanged hash-bound reference still covers 3902 old declarations. The active
pilot requires exactly those types plus the forty-five explicitly listed theorem types
in `additional-types.json`; it does not replace the old snapshot.
The comparator and all 31 adversarial tests are inherited byte-for-byte.
Relative to the original architecture exporter, the sole difference remains the
ForMathlib-owned module selector alongside OAI-owned modules; the static checker
enforces that exact one-line derivation. The snapshot and exporter binding are
unchanged in this round, and
the retained independently captured reference export is parsed again on every
check. Replay verifies frozen evidence; it does not re-elaborate old Lean source.
The candidate-only import harness rejects any OAI module import;
other import, behavior and axiom checks remain active.


The [three-file module integration](../../reports/module-integration.md) migrates
SingleCoordinate and the two kernel-transport files. Its exact syntax manifest is
`module-integration.json`; `module-import-graph.json` records module status and
explicit public/meta/import-all modifiers. The original implementation exporter
remains unchanged. `ModernPublicTypes.lean` separately checks the eleven selected
public types and original declaration kinds; `ModernCompatChecks.lean` checks the
old kernel reductions in a modern consumer; `LegacyKernelEntryChecks.lean` tests
both original kernel entrypoints. SingleCoordinate intentionally uses
four conservative focused Mathlib imports, so arbitrary unrelated Mathlib content
is no longer an implicit contract of that focused path.

The exact Lean 4.34.1 toolchain and pinned Mathlib checkout/artifacts are reused.
Missing Mathlib artifacts fail before local compilation. Renamed local modules
are genuinely re-elaborated; .olean files are not relabelled or transplanted.
The existing per-run compiler lock bounds memory. The active artifacts and dependency cache are preserved; retired project build
caches are removed.
See [the consolidation record](../../reports/project-consolidation.md) for current
commands and results. The [layout report](../../reports/for-mathlib-layout.md)
records the earlier published classification and build; historical commands there
are not current entrypoints.

Actual-content review additionally stages interval polynomial transport,
finite-rank parabolic polynomial reduction and the plane-model sheaf adapter.
Their existing interfaces already suffice; original Invariance/Localization
filenames do not determine the classification. Real scalar power identities
belong to `Algebra/Order/Field/RealScaling`, without implying an rpow theory.

The precise scaled-evaluation entrypoint does not import the finite weighted-sum
helpers; the precise weighted-sum entrypoint does not import owned polynomial
theory. Lean import harnesses check both module sets and preserved names.
The old scaled-reciprocity compatibility entrypoint deliberately exposes both.
See [the current responsibility report](../../reports/responsibility-boundaries.md)
and `responsibility-review.json` for mathematical reasons, application-side
boundaries, deferred cases and the measured validation results.

Kernel and compatibility harnesses preserve every behavior example and exact
local-module-set assertion; only import paths/expected module identities are
translated, with both local library prefixes monitored.

Baseline source reads use `scripts/baseline.py` against exact Git commits, never
paths under a retired checkout. The 525-span reconstruction and lexical source
coverage algorithm remain checked; the latter changes only its Git I/O adapter.
Pristine source hashes, the dependency lock, reference export checksums, public
types and named axiom closures are independent checks. The default checker does
not fetch history or execute the preserved upstream lakefile. Setup can fetch a
missing pinned commit in a shallow clone; failure stops setup explicitly.

Pilot lookup uses [LEMMA_INDEX.md](LEMMA_INDEX.md), generated from compiled Lean
docstrings and a small provenance/keyword index. From this project after sourcing
`../../scripts/env.sh`:

```bash
SEMANTIC_CORPUS_OUT="$LAB_ROOT/results/lemma-granularity/library-after-corpus.json" python3 pilot_measure.py library-after-corpus-replay lake env lean SemanticCorpus.lean
python3 render_lemma_index.py "$LAB_ROOT/results/lemma-granularity/library-after-corpus.json" --check
python3 semantic_search.py "$LAB_ROOT/results/lemma-granularity/library-after-corpus.json" --library --query "flat tensor section constraint kernel"
```

`--library --ablate-new-docs` removes only the latest twenty-four docstrings, keeping
the previous twenty-one. Queries were committed before editing and are nonblind.
The earlier `--comparison`, `--expansion` and default first-round query options remain available;
immutable corpora/results are in their respective reports/evidence directories.
Regenerating current metadata does not reproduce a historical corpus.

The full checker includes 30 source/API evolution tests, the inherited 31
comparator tests and 14 partition tests, the original 16 axiom closures and 81
pilot closures. Source coverage checks the pristine reconstruction; the separate
hash/diff/span/header check verifies twenty-one active exceptions and freezes the prior
ten. Selected old headers are checked literally as well as by complete type
exports; their diff alignment can change when proof blocks are extracted.
The recorder is an explicit reviewed update, not automatic acceptance or a
production-grade generic proof-evolution framework.

The previous comparison-round direct benchmark remains optional; run only without another active build:

```bash
python3 measure_samples.py --comparison
```

It elaborates one before/after source pair for each of the three comparison
modules with the same warm current dependencies and no input `.olean` reuse.
Baseline source hashes are checked. It is not a cold historical build and cannot
establish a speedup. Earlier benchmark modes remain available; prefer recorded
results to routinely repeating them. The current report separates new editing/
validation work, failed actions, dependency invalidation and already-built tooling.

The earlier proof-only timing scripts now encounter module/import changes in the
selected files; their historical timing interpretation does not carry over to
current runs. Use the recorded integration checks for current acceptance.

The [three sheaf module integration](../../reports/attach-bottom-module.md) adds
Sheaf.Basic, GradedSheaf.Defs and GradedSheaf.AttachBottom to the modern region
(128 products). Original stalkMap proofs stay intact; AttachBottom records two
explicit grading arguments. `attach-module.json` binds these exact source edits.
`stalk-equation-compat.json` permits one exact old/new equation representation
pair only after a live ordinary modern historical-type/rw/simp witness; the
complete raw difference and original baselines are preserved. Every other
record and the three-axiom limit remain checked.

The [next graph/sheaf module batch](../../reports/module-next-region.md) adds Bruhat.Basic,
Sheaf.Duality and GradedSheaf.Reindex (131 modern products). Its complete
3947-record comparison against accepted main has no new differences;
VertexDeletion remains legacy with its two rejected equation deltas retained.


The first-round (historical, `31f05da`) [semantic API experiment](../../reports/semantic-api-experiment.md) adds six
mathematical theorems in seven exact producer/client source exceptions, plus one
separately registered generated congruence declaration. It hides only
`Sheaf.quotientPullback`; `LocalCover.splitEquiv`, `CoefficientChange.map` and
`Sheaf.baseChangeQuotient` retain their computation/compatibility interfaces.
`semantic-api-source.json`, `semantic-api-types.json` and
`semantic-api-generated.json` bind this finite round without refreshing the old
source/type baselines. `SemanticApiChecks.lean` uses ordinary modern imports.
The isolated actual producer/client trials are `semantic_api_split_trial.py`
(with `--map` or `--quotient` for the two additional controls); run them only
without another active build. See the report for acceptance status and costs.


Round 2, [coefficient API evolution](../../reports/coefficient-api-evolution.md),
retains the six earlier APIs and restores quotientPullback exposure. Its former
opaque-definition exporter allowance and private historical audit copies are
removed. Nine evaluation/transport theorems support real graded/sheaf/pairing
clients. The bounded layer is `api_evolution.py`; the equivalent-implementation
trial is `api_evolution_trial.py`. Old round-1 hiding trials belong to the original
31f05da checkout. No bulk exposure or formatting migration is performed here.
