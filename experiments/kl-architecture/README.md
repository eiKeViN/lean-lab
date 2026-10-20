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
expression constructors and de Bruijn indices. It ignores binder display names,
expression metadata and injectively mapped compiler-private OAI owner prefixes.
For a local internal `_proof_` auxiliary whose ConstantInfo is a kernel theorem,
it retains the full proposition and uses proof irrelevance; binder metadata is
ignored only inside that proposition. Ordinary definitions, data instances and
user theorems are never unfolded or collapsed. Separate expression caches and a
DAG scope check prevent this rule from leaking into public binders. Identical
lazy-equation serialization copies are checked before projecting the unique
global environment. The prior strict comparator remains untouched. Fourteen
adversarial tests reject changed mathematical expressions and scope leaks.

Full-library compilation, independent import checks, inherited checks, sixteen
axiom closures, 3902 public types and the warm repeat pass locally. The main
axiom closure is exactly `propext`, `Classical.choice`, `Quot.sound`. This is not
an independent certification of the upstream mathematics. See the report for
all measurements, earlier failures and the granularity tradeoff.


`migration.json` records exact original spans, hashes, scope context, instance
name annotations and imports. `migrate.py --check` verifies every generated
source; `migrate.py` regenerates them. `source_check.py` additionally checks
coverage of every original non-comment code line. [MIGRATION.md](MIGRATION.md)
is the generated old-to-new file/line index and direct import map. The rationale,
provenance, executed results and limitations are in
[the report](../../reports/semantic-architecture.md). Generated logs live under
ignored `results/architecture/`.

The core graph is in [DEPENDENCIES.svg](DEPENDENCIES.svg) (195 nodes, imported
module → consumer) and [DEPENDENCIES.dot](DEPENDENCIES.dot). Reproduce size and
closure evidence with `python3 experiments/kl-architecture/analyze.py` from the
lab root; Graphviz is optional and is not required for Lean validation.
