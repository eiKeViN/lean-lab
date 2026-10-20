# KL semantic file architecture

Status: local migration in progress. Starting tree: main
`7ddc53ba8a09ed902fefff86e67a87217518c1d4`. The three completed experiments
remain frozen. The new experiment is `experiments/kl-architecture`; publication
is outside this round. This is a file-responsibility migration, with unchanged
mathematical declarations and proof bodies, not a new theorem/API design.

## Design and sources

The primary source is `experiments/kl-kernel-transport` at the starting tree.
Lean is 4.34.1; Mathlib is `d13f23b723b8a846827a245b89c10fc7d3f11612`.
The pristine 34-module source is still `experiments/kl` (upstream
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`, lab transport snapshot
`70211c3350c1f203aa8f52f1809e57d7ae93ba78`). The two completed refactorings
are inherited, not redone.

Classification follows the mathematical object appearing in the declarations:

| Home below `OAI/` | Responsibility and direction |
| --- | --- |
| `Algebra/Module`, `LinearAlgebra`, `RingTheory`, `Data/Polynomial`, `Order` | Local supplements to existing Mathlib objects: graded modules, covers, tensor/dual/quotient/localization operations, reflection linear algebra, polynomial rigidity. |
| `GroupTheory/Coxeter` | Exchange and Bruhat order, realizations and roots, parabolic/dihedral systems, root orders and Dyer paths. |
| `Combinatorics/DirectedPaths` and `Combinatorics/Dihedral` | Graph schedules/transfer and the signed-dihedral counting model; these do not acquire Coxeter parameters just because KL consumes them. |
| `Combinatorics/MomentGraph` | Ordered-graph module sheaves, graded structures, morphisms, extension, decomposition, embedded images and pairings. The Bruhat adapter is explicit. |
| `RepresentationTheory/Hecke` | Concrete Hecke operators, ordinary R and dihedral/positive-word formulas. |
| `RepresentationTheory/BottSamelson` | The concrete Tits-coefficient word modules, stalks, pairings and sheaf bridges. |
| `RepresentationTheory/KazhdanLusztig/{Polynomials,Sheaves,Localization,Comparison,Invariance}` | KL-specific normalization, boundary models, geometric localization, comparison propagation and final theorem. |

Mathlib anchors were read from the pinned checkout, notably
`Algebra/Module/GradedModule.lean` (`DirectSum.Decomposition`,
`SetLike.GradedSMul`), `Algebra/Module/LocalizedModule/Submodule.lean`,
`Algebra/Module/Submodule/{Ker,Equiv}.lean`,
`LinearAlgebra/Reflection.lean` (`Module.reflection`),
`LinearAlgebra/SymmetricAlgebra/Basic.lean`, and
`Algebra/Polynomial/Reverse.lean` (`Polynomial.reflect`). These are local OAI
extensions, not proposed additions to Mathlib. Moment-graph sheaves are not
identified with Mathlib's sheaves of modules on a site.

The combkl reading aid is the documentation-only commit
`8004f18a6cab3bb1f113b48abb5d2ea4c37bcaaf`:
`docs/knowledge-base-relationships.md`, `docs/knowledge-base-relations.json`,
`docs/knowledge/concept-links.yml`, and source-comparison material. Its own
metadata anchors combkl code at `108243e05ed46235bf82dc30d4d90c794579776f`
and upstream at the same `adc7f...` revision. We retain the lab's independently
verified source identity. The guide explicitly describes an exposition graph,
not a Lean import graph. Its nine subject branches inform the responsibility
map; imports instead follow actual declaration and elaborator references in
our pinned compiled source. No upstream code or documentation was synced.

## Migration method and limits

Move complete closed namespaces/sections, replicating only trivial enclosing
scope context. The mixed `Model`, `Comparison`, and `CanonicalKL` scopes also
separate their existing Bruhat/normalization, polynomial/transfer, and
lower-half-operation/recursive-KL portions. Hypotheses and proof bodies are copied verbatim. Existing anonymous instance
names are made explicit (76 command headers), and one original local instance
attribute is restored in the separated Hecke inverse scope; instance values
are unchanged. No theorem is split and no helper/API is added.
Original public namespaces stay stable. Old module paths become import-only
compatibility shims. New semantic modules do not import those shims; the
previous kernel compatibility leaf remains available unchanged.

Coalesce units with the same responsibility only if the resulting import graph
is acyclic. Keep meaningful construction/extension phases when coalescing would
create a cycle. Private helper scope and generated instance-name order are
compatibility constraints. They can require imports beyond mathematical type
dependencies; the design does not claim all coupling disappears by moving files.
Mathlib imports remain broad in this round; dependency minimization within
Mathlib is a separate task.

The experiment owns a source-span manifest, deterministic regeneration and
old-to-new index. Validation will check frozen experiments and pins, exact
moved body bytes and coverage, acyclic semantic imports, compilation through
both new homes and legacy entries, complete public declaration names/kinds and
mathematical types, and recursive axiom closures. Binder display names and
compiler-private owner names are relocation metadata; the type comparison
will state its normalization explicitly instead of extending the prior
31-field exception table. Compilation is not an independent certification of
the original upstream mathematics.

Builds share the pinned dependency checkout and retain separate OAI artifacts.
A per-run compiler lock serializes Lean processes to fit the 16 GiB worker;
it does not change the toolchain or saved environment settings. Cache readiness
must pass with `lake --no-build build Mathlib` before any new compilation.

## Implementation checkpoint

The isolated experiment currently has 193 semantic implementation modules,
34 legacy import shims, two unchanged kernel modules and one aggregate import
(230 OAI modules). There are 525 transported units covering every one of the
35,871 non-comment reference source lines (including retained/replicated scope
context). Static source/pin/frozen-tree and acyclic import checks pass.
Foundational object APIs have no concrete Coxeter/sheaf/representation imports;
general moment-graph sheaves have no Coxeter or representation imports;
Coxeter object modules have no representation imports. Path/Hecke comparison
bridges are classified with their consumers rather than hidden in root geometry.

Compilation is still in progress at this checkpoint. Initial probes exposed
and corrected source-span section/comment boundaries, duplicate anonymous
instance names in the first annotation replay, and the separated Hecke inverse
scope's local decidability attribute. These are migration/tooling failures,
not changes to mathematical arguments. The reference's 3902 public type records
have been exported with the documented alpha-metadata normalization; the final
experiment comparison and axiom checks have not yet completed.
