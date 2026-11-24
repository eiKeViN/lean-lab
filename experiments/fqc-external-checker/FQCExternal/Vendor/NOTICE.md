These Lean files are derived from Google DeepMind's
`google-deepmind/formal-quantum-computation`, commit
`a88de8ff65d78af564b2373088ca369dc95f6547` (Apache-2.0).
Original copyright headers and LICENSE are retained.

`Core` and `Stream` retain the complete corresponding source modules. `Shared`
ends immediately before `theorem c2_0`; `Stage1` ends immediately before
`theorem c1_0`. Those slices append the two closing `end` commands. Imports of
these four modules are renamed to `FQCExternal.Vendor.*`; all other text in the
slices is retained. No upstream Lake configuration is executed.

`../../provenance/upstream.json` records full original SHA-256, Git blob SHA-1,
slice boundaries, derived hashes, selected certificate hashes and the retained
public proposition. `scripts/source.py` reproduces and checks these identities
from the exact public snapshot. Original data-bearing files are cached outside
Git; they are not imported by the admitted proof.

The trailing whitespace on upstream `Core.lean` line 772 is intentionally
retained for exact source identity. Whitespace checks on newly authored code
exclude these source-preserving vendor snapshots; their byte identity is checked
instead by the provenance verifier.

The modified executable ports `../Exec.lean` and `../Exec2.lean` derive their
arithmetic and decoding algorithms from the same snapshot (Copyright 2026
Google LLC, Apache-2.0; see LICENSE). They replace proposition-carrying decoders
with executable option/boolean checks and are explicitly part of the external
trust boundary.

The full integration generator retains original copyright/license headers in
every materialized upstream module. Six coverage data modules have selected
`c1_i`/`c2_i` proofs replaced by named external axioms. HalfPlaneCauchyWalkCore
is partitioned at namespace boundaries, as is MidTap29Coul18Stage4K2. The Coulomb
and polynomial modules are partitioned at original section/namespace boundaries.
Closed numerical evaluations use named Boolean assumptions, with original generic
analytic and circuit-semantic proofs retained. The
independent `top1D73_cov` proof is retained. Source/claim, partition and scalar
predicate locks are in `../../provenance/photochemistry*.json`. The named evaluator
retains each selected original goal, its canonical expression, dependencies and
source position in the proposition registry; its temporary native axiom is not
retained. All other upstream declaration/proof bodies remain source-derived.
