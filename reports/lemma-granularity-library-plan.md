# Library extraction plan — 2026-10-22

See [coverage](lemma-granularity-library-coverage.md) and the exact committed
[evidence plan](evidence/lemma-granularity-library/plan.json). Twenty-one old proofs
are selected across finite-character localization, projective prime cancellation,
polynomial rigidity, graded Hilbert identities and sheaf operations. The initial twenty-five-helper proposal is retained as `pre-reuse-plan.json`.
A later cross-check found the existing `hasSum_shift_coeff`, so the revised plan
keeps twenty-four new helpers, reuses that API in two old clients, and records
one helper-to-helper sharing edge. No quota was imposed.

Keep the same branch/project, old 3902 types and previous 21 added types, and ten
prior active sources. Build foundational edits in two grouped batches, then the
whole library once; preserve successful caches and failure logs. Reuse the existing
bounded evolution/type/axiom/regression tools with explicit new bindings; no API
architecture redesign or new testing framework. Short source docstrings and a
generated index remain the semantic scheme. Use real command wall/CPU records,
not output-token estimates; model token telemetry is unavailable. Checkpoints are
not completion of this larger round. Do not merge main.
