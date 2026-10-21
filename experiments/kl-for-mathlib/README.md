# KL formalization

The single maintained Lean project. Continue updating this directory in place.
Earlier stages through `85b3d1a4fa9c4f08beb718d8925d2d0ec9c50060` remain
recoverable from Git history; their experiment directories have been removed.
The current mathematical source, interfaces and module paths are unchanged by
that consolidation.

`ForMathlib/` contains 168 implementation modules that can presently form a
standalone dependency layer: general algebra/linear support, Coxeter geometry,
ordered paths and moment-graph sheaves, Hecke and equal-parameter KL polynomial
theory, and the existing Tits Bott word model. This includes specialized research
mathematics; subject specialization is not a reason for exclusion.

`OAI/KL/` contains 23 existing application modules plus the kernel-name wrapper:
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
entrypoints are import wrappers. Earlier semantic import paths are available in
the pinned historical Git trees.
The maintained project uses the paths in CLASSIFICATION.md and does not add
another 193 import wrappers.

The classification follows the official guides consulted on 2026-10-21:
[scope and AI policy](https://leanprover-community.github.io/contribute/index.html),
[review criteria](https://leanprover-community.github.io/contribute/pr-review.html),
[naming](https://leanprover-community.github.io/contribute/naming.html) and
[style](https://leanprover-community.github.io/contribute/style.html).
Candidates still need duplicate/API searches, suitable namespace/naming and
assumption review, focused Mathlib imports, proper docs and human/maintainer
review. This round does not establish that any file is PR-ready or accepted.
No Mathlib PR or community comment is published.

Changes to file responsibility use existing complete source units only:

- Polynomial files now use `Algebra/Polynomial`. Generic functional avoidance
  belongs to `LinearAlgebra/Avoidance`.
- Quotient descent and induced quotient equivalences share
  `LinearAlgebra/Quotient/Transport`; pair-projection basic/kernel/lifting tools
  share `LinearAlgebra/PairProjection`.
- Reflection evaluation and reciprocal rigidity share `Polynomial/Reciprocal`.
- The former mixed scaled-comparison file separates polynomial transfer
  evaluation, ordered-field real-power scalar identities and scaled polynomial reciprocity.
- The dihedral Hecke/KL polynomial bridge is located with KL polynomials.
  Concrete word coordinates are named `BottSamelson/TitsWords`.
- Project filenames state their roles: `SuffixFreeness`, `GraphEmbedding`,
  `TerminalImages`; general plane models and finite-rank reduction live below.

No mathematical statement or proof body is rewritten. The earlier 76 explicit
instance-name annotations and single local instance attribute are inherited.
`migration.json` and `migrate.py --check` bind all 525 units and fixed sources to
the pristine reference history. `source_check.py` verifies full source coverage.
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
The default uses the unchanged, hash-bound 3902-declaration reference snapshot.
The comparator and all 31 adversarial tests are inherited byte-for-byte.
The exporter differs solely by including ForMathlib-owned modules as well as
OAI-owned modules; the static checker enforces that exact one-line derivation.
Snapshot types are unchanged; only their bound exporter hash is updated, and
the retained independently captured reference export is parsed again on every
check. Replay verifies frozen evidence; it does not re-elaborate old Lean source.
The candidate-only import harness rejects any OAI module import;
other import, behavior and axiom checks remain active.

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

The preserved scaled-reciprocity source unit still carries two finite weighted-sum
difference helpers. Their eventual declaration-level file placement is a known
cleanup item, not an assertion that they are polynomial-specific. The final
consumer has an explicit import, avoiding dependence on an incidental transitive
import. No proof or mathematical interface is rewritten to fix that integration.

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
