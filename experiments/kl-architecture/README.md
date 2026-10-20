# Semantic KL architecture

An isolated, whole-library file migration from `../kl-kernel-transport` at
`7ddc53ba8a09ed902fefff86e67a87217518c1d4`. The three earlier experiments and
all their checks remain frozen. Work is local; see the report for actual status.

The implementation homes separate Mathlib-object supplements (`Algebra/Module`,
`LinearAlgebra`, `RingTheory`, `Data/Polynomial`, `Order`), Coxeter geometry,
general paths and moment-graph sheaves, Hecke theory, concrete Bott–Samelson
models, and KL-specific localization/comparison/invariance. Namespaces and public
names stay compatible. Old `OAI.RepresentationTheory.KazhdanLusztig.*` files are
import-only compatibility entries; implementations do not depend on them.
`OAI.Architecture` imports every semantic implementation, including unused
exports. The previously extracted kernel implementation and compatibility leaf
are unchanged.

This round moves existing mathematical units. No theorem is split, no hypothesis
is generalized and no helper API is added. Necessary compilation adaptations
explicitly pin 76 existing anonymous instance names and restore one original
local instance attribute in the Hecke inverse file. Instance values and all
mathematical proof bodies remain unchanged.

From the repository root:

```bash
bash scripts/setup.sh
bash experiments/kl-architecture/check.sh
```

Setup prepares the pinned Lean 4.34.1 and Mathlib dependencies. The experiment
shares that dependency checkout and uses separate OAI artifacts. Its runner
refuses absent Mathlib artifacts before compiling local code. A per-run compiler
lock prevents concurrent Mathlib-loaded Lean processes exceeding worker memory;
no global installation or saved cloud setting changes.

For an inexpensive structural check, or a check requiring already warm OAI:

```bash
bash experiments/kl-architecture/check.sh --static
bash experiments/kl-architecture/check.sh --checks-only
```

To independently re-export the reference types when its OAI artifacts are warm:

```bash
bash experiments/kl-architecture/check.sh --checks-only --refresh-reference
```

The normal runner uses a committed reference type snapshot, tied to the frozen
source commit and exporter hash, so future workers need not build two libraries.
This round also checks that snapshot against the live warm reference. Type
comparison preserves public names, kinds, universes, binder implicitness,
expression constructors and de Bruijn indices. It ignores binder display names
(alpha equivalence), expression metadata and compiler-private OAI owner prefixes;
it does not unfold or reduce types. This is mathematical type preservation,
not the prior experiment's stricter binder-metadata policy. The old strict
comparator remains untouched. Nine adversarial comparator tests reject changed
universes, binding, implicitness, constants, kinds and exported names.

`migration.json` records exact original spans, hashes, scope context, instance
name annotations and imports. `migrate.py --check` verifies every generated
source; `migrate.py` regenerates them. `source_check.py` additionally checks
coverage of every original non-comment code line. [MIGRATION.md](MIGRATION.md)
is the generated old-to-new file/line index and direct import map. The rationale,
provenance, executed results and limitations are in
[the report](../../reports/semantic-architecture.md). Generated logs live under
ignored `results/architecture/`.
