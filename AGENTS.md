# Lean lab working rules

- Work in this repository only; other workspace mounts are references.
- Each experiment owns its Lean toolchain and locked dependency manifest.
- Use `scripts/setup.sh` and `scripts/check.sh`; do not update pins incidentally.
- Preserve the KL baseline source blobs. Put mathematical changes in a separate
  experiment/branch and keep statement and axiom checks explicit.
- Never execute the large upstream lakefile preserved as reference text.
- Avoid building all of mathlib when official binary caches are unavailable.
- Report source identity, compilation, axiom checks and comparator checks as
  distinct evidence. A blocked check is not a passed check.
- Keep caches out of Git. Save focused commits/branches; do not merge substantive
  mathematical refactors without an explicit request.
