# Whole-library responsibility and entrypoint review — 2026-10-21

Base: merged `main` at `7e1ed51e20e43b6c116f20117fdae00279deb1d9` (PR #5).
Branch: `codex/kl-module-boundaries`. The sole maintained project remains
`experiments/kl-for-mathlib`. No mathematical declaration, proof body, hypothesis
or declaration namespace is changed; there is no new general API or proof tactic.

## Coverage and review method

The review covers all **192 base implementation modules**, their declaration
anchors, immutable source-unit allocations and owned imports; all base published
compatibility and aggregate entries; and all resulting **207 implementations**,
**51 compatibility imports** and **3 aggregate/project entries**. This is a
module-responsibility and dependency review, not an independent line-by-line
proof certification or a Mathlib novelty review. It does not assume that every
module needs changing or that a complete pass makes the architecture permanent.

[The complete review record](evidence/whole-library-layout/module-review.json)
contains one decision for every base module, before/after destinations,
source hashes, current module responsibilities, all scanned declaration anchors
and actual owned imports. Unchanged modules are recorded too, grouped by their
mathematical object and role. The anchor scan is navigation evidence, not a
substitute for the complete kernel-exported 3902-public-type comparison.
[MODULES.md](../experiments/kl-for-mathlib/MODULES.md) is a generated guide to
current paths; CLASSIFICATION.md continues to index the older semantic source
and upstream assessment. No project-specific interface is invented to move
mathematics into ForMathlib.

## Changes and mathematical reasons

Paths in this section are relative to the maintained project. Each of the twelve
old homes remains an import-only compatibility entry; implementations import
new homes directly. Only existing complete source units are redistributed in
this round. The one previously approved source partition remains unchanged.

| Old home | Current responsibilities | Reason |
| --- | --- | --- |
| `Algebra.Module.Cover.Product` | `Algebra.Module.Submodule.PiIdeal` | `LocalCover.pi_mem_ideal_smul` concerns membership in an ideal multiple of a finite dependent product. Its statement has no cover, local-ring or minimality structure. It has genuine ordinary and graded sheaf consumers; the latter uses it through the ordinary product layer. |
| `Algebra.Module.Graded.AlgebraMap` | `Graded.Basis`, `Graded.PolynomialMap`, `Graded.HomogeneousMul` | These respectively define grading via a weighted basis/pairing, preservation of polynomial degree by an algebra map, and recovery of homogeneity after multiplication by a nonzero homogeneous scalar. Only the second is an algebra-map responsibility. |
| `Algebra.Module.Graded.DualAndShift` | `Graded.HomogeneousEquiv`, `Graded.FinitePieces`, `Graded.ModuleData.PairProjection`, `Graded.ModuleData.CoefficientChange.Basic` | Inverse degrees and dual pairings, finiteness of pieces, pair-projection module data and change of coefficients are different objects. Homogeneous dual support and module-data range clients now name the relevant implementation. The broad Bott stalk construction deliberately keeps the support it uses. |
| `MomentGraph.GradedSheaf.Basic` | `GradedSheaf.Defs`, `GradedSheaf.AttachBottom`, `GradedSheaf.Reindex`, `GradedSheaf.Properties` | Separate the data/section interface, bottom attachment, reindexing and preservation of free/quotient/minimal conditions. The old Basic entry still imports the operations and their dependencies. |
| `MomentGraph.Sheaf.Isomorphism` | `Sheaf.Iso`, `Sheaf.Pi`, `OrderedGraph.VertexDeletion` | Isomorphisms and stalk-extension squares are ordinary sheaf maps; dependent products and graph-coordinate deletion are separate constructions. `Sheaf.Iso` no longer imports graded sheaves. |
| `MomentGraph.Sheaf.Zero` | `Sheaf.Products`, `Sheaf.Pullback` | Zero/binary products and zero summands belong together; graph-map pullback, assignment transport and live-edge conditions are a different operation. The preserved upward-kernel pullback unit joins that operation. |
| `MomentGraph.Sheaf.Extension` | `Sheaf.BaseChange`, `Sheaf.Structure`, `Sheaf.Restriction`; two graded units move to `GradedSheaf.Extension` | Scalar extension and sections, the scalar-quotient structure sheaf, and induced-subgraph restriction have distinct responsibilities. Graded stalk lifting and actual graded boundary models belong to the graded construction layer. Ordinary core operations no longer need it. |
| `MomentGraph.Sheaf.Hom` and `MomentGraph.Sheaf.Uniqueness` | `GradedSheaf.StalkMaps` | Both statements concern homogeneous stalk maps under graded minimal-cover conditions: a split lift and a bijectivity criterion. Their actual parameters require grading, despite the old namespace/path. The two complete source units share this one object-level home; no proof is split or rewritten. |
| `Algebra.Module.Graded.Hilbert.RationalFunction` | `Graded.Hilbert.Numerator` | Its three theorems concern shifted weighted sums and uniqueness/addition of polynomial numerators with a common nonzero real evaluation factor. No rational-function structure is assumed. The shift lemma stays with its actual numerator consumers. |
| `LinearAlgebra.Reflection.Forms` | `Reflection.Bilinear`, `BilinearForm.NondegenerateExtension` | Rank-one orthogonal reflection and dihedral relations differ from extending an arbitrary real symmetric bilinear form by the dual of its radical. The latter needs no reflection group. The geometric realization imports reflection support; the Tits extension explicitly imports the general extension construction. |
| `OAI.KL.BottSamelson.Pairings` | `BottSamelson.UpperSections`, `BottSamelson.StalkCharacter`, `BottSamelson.Flabby` | Upper-set image projectivity/local denominators, character rank recurrences/Hecke coefficients, and projection-sheaf flabbiness on intervals are separate responsibilities. In particular character recurrences import Stalks but do not require upper-section projectivity or adjoint-sheaf gluing. The later character assembly names its character/flabbiness prerequisites explicitly. |

ForMathlib prefixes are omitted from the table for readability. Original
`OAI.KLInvariance.*` names, including the existing LocalCover and Realization
namespaces, stay compatible. Paths are not a claim of final upstream naming.

## Boundaries retained and remaining debt

Every retained module has a record in the coverage JSON. Important decisions:

- Generic quotient transport, pair projection, coordinate projection and kernel
  transport keep their constructions together. Tiny useful interfaces are not
  merged merely because they are short.
- `Dual.BalancedCut`, adjoint summands, integral support and Frobenius duality
  retain separate objects. No generic duality API is fabricated to unify them.
- Graded generators retain the interrelated component, subquotient, basis and
  minimal-generator construction units. Graded module data, Hilbert series and
  homogeneous duality remain distinct object families.
- Coxeter exchange, Bruhat/parabolic structure, realizations, root geometry,
  dihedral coordinates and reflection-order/path bridges remain object-level
  mathematics. The root/path bridge modules contain no Hecke/application import;
  their shared geometric hypotheses are a reason to keep those units together.
- Hecke operators retain their related real/Laurent coefficient realizations;
  similar proofs are not rewritten or abstracted. KL normalization, uniqueness,
  dihedral, parabolic and interval transport remain polynomial theory.
- Tits word models remain specialized upstream candidates. The application
  stalk, adjoint, support, comparison and localization bridges remain application
  modules because their current interfaces depend on the selected model/basis
  and proof pipeline, not because their mathematical subjects are specialized.
- The ForMathlib/application classification is retained, not re-certified as
  submission-ready. Broad Mathlib imports, OAI namespaces, naming/assumption and
  duplicate searches, human understanding and maintainer review remain upstream
  preparation. No Mathlib PR/comment or new interface extraction is performed.

Three precise residual placement debts are recorded rather than hidden:

1. `GraphEquiv` remains in the complete graded-reindex source unit, and the
   bottom-graph constructor remains in the bottom-attachment unit. Consequently
   `OrderedGraph.VertexDeletion` still imports those graded units. This does not
   make the ordinary sheaf core depend on grading. A future finer partition of
   existing declarations could remove this graph-only coupling without new API.
2. The complete structure/base-change unit includes generic `Iso.flabby` and
   `Iso.generated`. They are preserved with that unit; they are not described as
   structure-specific. A declaration-boundary partition could improve placement.
3. The existing `Module.Projective.Transport` unit combines same-range
   projectivity with projectivity of the scalar twist. A finer source partition
   could narrow the generic import. This pass does not introduce a new transport
   abstraction or weaken the existing strict source-frame policy.

## Entry organization and preservation

```lean
import OAI.KL  -- normal main-theorem entry
-- OAI.KLInvariance.combinatorial_invariance
```

Focused reusable mathematics uses its individual ForMathlib module.
`ForMathlib` is the all-candidate umbrella and must import no project module;
`OAI.Architecture` is the all-implementation audit/export umbrella. The new
project entry imports `OAI.KL.Invariance.Main`, without legacy KL entrypoints or
either broad aggregate. Existing published imports remain usable, including
all 34 original KL and two kernel entries, three earlier ForMathlib compatibility
entries and the twelve homes retired in this pass. No new experiment is copied.

The source reconstruction still binds all **525 original unit records**, **526
allocated pieces**, fixed files, 34 upstream blob hashes and 76 inherited
instance-name annotations to immutable Git source. No new source partition or
context rewrite is added. The exporter, comparator, reference snapshot,
source-coverage algorithm, sixteen-closure audit, toolchain and dependency lock
remain unchanged. Only import graph/allocation and generated headers change.

The implementation inventory changes from 192 to 207: **181 candidates**, **25
application modules** and **one project kernel wrapper**. Compatibility entries
change from 39 to 51; aggregate/project entries from 2 to 3; generated products
from 233 to **261**. Direct core edges change from 327 to **362**. These counts
are consequences, not optimization targets. Independent importability and object
ownership are the benefits; fewer lines/edges or faster proof elaboration are not
claimed. ForMathlib → OAI edges remain zero.

## Validation and reproduction

From the repository root:

```bash
bash scripts/check.sh
python3 scripts/test_checks.py
PYTHONOPTIMIZE=1 python3 scripts/test_checks.py
```

The maintained runner additionally exercises four new Lean import/entry harnesses:
ordinary sheaf operations without grading/models, homogeneous equivalences and
finite pieces without module-data/pair/coefficient-change constructions,
stalk-character recurrences without upper-section projectivity, and the focused
project entry. Existing source, type, behavior, axiom, comparator and partition
checks remain active. Static checking also rejects direct grading dependencies
from every current ordinary-sheaf implementation. The expanded Lean harness
imports all 13 current ordinary-sheaf implementations through four leaf imports,
with no missing module in the recorded closure check.

Validated checkpoint: all **28 stages** of `bash scripts/check.sh` passed.
The final incremental library completion took **133.729 s**, after reusing the
previously completed Stalks and UpperSections compilations; the warm repeat took
**4.798 s**. This is not an end-to-end cold build or a speedup measurement.
The earlier preparation was interrupted twice at safe boundaries; completed
artifacts were retained. Stalks completed once (Lake reports 152 s), and the
UpperSections job completed once (641 s). Other Lake job times can include
waiting for the serial compiler lock and are not direct elaboration benchmarks.
Two integration omissions were corrected solely by adding explicit imports:
VertexDeletion needs bottom attachment; Bott support needs interval flabbiness.
No mathematical proof was changed to resolve either failure. Preparation and
failure records remain alongside the successful checkpoint logs.

All **3902** public types match the unchanged reference: no additions, losses or
changed types. All **16** named axiom closures satisfy the allowlist; the main
closure is exactly `propext`, `Classical.choice`, `Quot.sound`. The 31 comparator
and 14 source-partition tests passed. Root regressions passed all 18 tests both
normally and with Python optimization; optimized partition tests also passed.
The original 525 source records, partition specification, fixed sources and
annotations are unchanged. Frozen reference replay is not historical Lean
re-elaboration. Mathlib artifacts were reused through `--no-build` readiness;
no full Mathlib source build or cache cleaning was performed.

Final naming/dependency sweep: `Sheaf.Hom` and `Sheaf.Uniqueness` now share
`GradedSheaf.StalkMaps`, preserving `split_stalk_graded` and
`stalk_hom_bijective` exactly. The ordinary localization file no longer imports
graded extension. Static checking now applies the no-grading boundary to every
current ordinary-sheaf implementation, not just the earlier core subset; the
Lean import harness covers the complete ordinary layer through its leaf imports.
The original checkpoint evidence remains separately under `validated-checkpoint`.
The final completion run passed all **28 stages** again. Final incremental
library completion: **322.595 s**; warm repeat: **4.806 s**; summed recorded
stage wall time: **414.660 s**. Neither Stalks nor UpperSections was recompiled
in this completion run. This is reuse of validated artifacts, not a cold-build
benchmark. [Final stage records and logs](evidence/whole-library-layout/final-validation/)
are separate from the earlier checkpoint and the preparation/failure evidence.

Final export: 3902 old / 3902 new, no missing, added or changed public type.
The comparator's relocation count refers to the older transport snapshot, not
the number of moves in this pass. All 16 axiom closures pass; all 31 comparator,
14 partition and 18 root regressions pass. The root suite also passes with
Python optimization. The complete ordinary-sheaf import harness passes and its
recorded source closure covers all 13 current implementations. All 51 published
compatibility entries preserve their originally reachable source units.
The 192 base-module review rows cover all 207 current implementations; the
receipt verifier passes. There is no remaining implementation or validation
blocker in this round. The three explicitly described finer placement debts
remain optional future work, not new APIs promised by this pass.

These are local pinned-environment preservation and compiler checks. They do
not establish Mathlib HEAD compatibility, novelty, upstream acceptance or an
independent review of this iteration; compilation alone does not certify the
intended scope of the original mathematical arguments.

The optional dated receipt verifier is
`python3 reports/evidence/whole-library-layout/verify-inventory.py`; it checks
source hashes and original-to-current coverage against this matching checkout,
including all 51 compatibility source-unit closures. It is not an ongoing
architecture freeze or an independent mathematical review. GitHub CI is a
separate publication check; local cloud validation is not CI.
