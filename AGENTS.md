# Lean project working rules

- Work in this repository only; other workspace mounts are references.
- Maintain `experiments/kl-for-mathlib` in place. Do not create another staged
  experiment copy unless explicitly requested. It owns its toolchain, locked
  dependency manifest and `.lake/packages` directory.
- Use `scripts/setup.sh` and `scripts/check.sh`; do not update pins incidentally.
- Preserve source provenance through the exact Git snapshots in
  `provenance/baselines.json`, original blob manifest and retained type export.
  Verify history and source coverage rather than requiring retired checkouts.
- Keep public-type, source-identity and axiom checks explicit. Intentional API or
  baseline changes need a documented review; do not weaken checks for a green run.
- Never execute the upstream lakefile preserved as inert reference text.
- Avoid building all of Mathlib when official binary caches are unavailable.
- Report source identity, compilation, axiom and comparator evidence separately.
  A blocked check is not a passed check; replaying frozen evidence is not a fresh
  elaboration of a historical project.
- Keep caches/results out of Git. Do not routinely clean working artifacts.
- Save focused commits; do not merge into main without an explicit request.
