# Upstream candidate staging and KL application layout

An isolated follow-up to `../kl-architecture` at
`2b5287954bd3c16015d9aab10dc3331d61065926`. All four earlier experiments,
root setup/check scripts and pristine provenance stay unchanged.

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
entrypoints are import wrappers. The prior experiment's 193 semantic import
paths remain available in that frozen experiment; the new experiment adopts
the import migration documented in CLASSIFICATION.md, rather than duplicating
all those semantic paths with another 193 wrappers.

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
`--checks-only`; add `--refresh-reference` to re-export the frozen reference.
The default uses the unchanged, hash-bound 3902-declaration reference snapshot.
The comparator and all 31 adversarial tests are inherited byte-for-byte.
The exporter differs solely by including ForMathlib-owned modules as well as
OAI-owned modules; the static checker enforces that exact one-line derivation.
Snapshot types are unchanged; only their bound exporter hash is updated, and
the warm reference is independently re-exported to verify it. The candidate-only import harness rejects any OAI module import;
other import, behavior and axiom checks remain active.

The exact Lean 4.34.1 toolchain and pinned Mathlib checkout/artifacts are shared.
Missing Mathlib artifacts fail before local compilation. Renamed local modules
are genuinely re-elaborated; .olean files are not relabelled or transplanted.
The existing per-run compiler lock bounds memory. Previous caches are preserved.
See [the report](../../reports/for-mathlib-layout.md) for actual run results and
remaining limitations; an earlier build is not evidence for this layout.

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
