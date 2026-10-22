# Lean lab

The maintained formalization is [experiments/kl-for-mathlib](experiments/kl-for-mathlib/README.md).
Use `import OAI.KL` for its main theorem; the [current module guide](experiments/kl-for-mathlib/MODULES.md)
lists focused mathematical imports and compatibility paths.
Keep editing that project in place; earlier staged experiments are preserved in
Git history rather than as parallel working trees. There is no root Lean project:
the maintained folder owns its toolchain, Lake manifest and dependency directory.

```bash
bash scripts/setup.sh
bash scripts/check.sh          # full source, build, import, type and axiom checks
```

Useful shorter commands:

```bash
bash scripts/check.sh warm     # require existing artifacts; repeat complete checks
bash scripts/check.sh static   # Git/source/baseline evidence and dependency boundaries
bash scripts/check.sh smoke    # inexpensive Mathlib smoke test
python3 scripts/test_checks.py # offline failure-path regressions
```

`kl`/`build` are aliases for full checking; `audit` is an alias for the complete
warm check. Direct project commands remain available via
`bash experiments/kl-for-mathlib/check.sh`. For interactive use, run
`source scripts/env.sh` before `cd experiments/kl-for-mathlib; lake ...`.

The Lean tree separates `ForMathlib/` (181 current upstream-candidate modules)
from `OAI/KL/` (25 application modules and one compatibility wrapper). Original
34 KL import entrypoints and two kernel import entrypoints remain as wrappers.
Previously published ForMathlib and application paths also forward to their more precise homes.
ForMathlib has no project-layer imports. Specialized Coxeter, Hecke, KL polynomial
and Tits word mathematics is included among the candidates; candidate status does
not mean submission-ready. The architecture cleanup preserved the proofs; the
active extraction pilot below is a subsequent, explicitly checked evolution.

The current tree has 261 Lean product modules. The active [comparison-pipeline lemma pilot](reports/lemma-granularity-comparison.md)
retains all 3902 baseline public types and the previous thirteen added types,
with eight further additions (twenty-one total) separately checked.
The fixed toolchain is Lean 4.34.1; Mathlib is pinned at
`d13f23b723b8a846827a245b89c10fc7d3f11612`. Dependencies and working artifacts
are owned by the maintained project's `.lake`, with shared installation/download
caches under `.cache`. Do not run `lake clean` or `lake update` routinely.
Setup reuses ready caches, refuses automatic full Mathlib source builds, and does
not change a global Lean default, shell profile or saved environment setting.
Linux x86_64 bootstrap requires bash, Git, curl, Python 3, tar and zstd.
`SKIP_CACHE=1 bash scripts/setup.sh` retains the smoke-only setup option.

Source baselines are exact reachable Git commits in
[provenance/baselines.json](provenance/baselines.json), checked against the original
34-blob upstream manifest. The independently exported 3902-type reference is
retained as checksum-bound compressed evidence, not another Lean project.
No check requires a deleted experiment directory. Setup fetches only missing
pinned history for shallow clones; checks themselves perform no history fetch.
Historical compilation is not rerun or claimed by replaying this evidence.

Across three rounds the pilot rewrites fifteen proofs in ten hash-bound source
exceptions; the previous seven active files remain frozen separately. Old statements and API
types remain unchanged. The pristine source reconstruction and historical
reference export remain intact. See [the pilot materials](experiments/kl-for-mathlib/LEMMA_INDEX.md).

See [the whole-library refinement](reports/whole-library-layout.md) for current
coverage, file responsibilities, entrypoints and validation, [the previous boundary refinement](reports/responsibility-boundaries.md), and [the consolidation record](reports/project-consolidation.md) for earlier
verification and cache results, [provenance](provenance/README.md) for licenses and
source anchors, and [historical reports](reports/README.md) for earlier stages.
Current source/type/axiom checks stay strict. An intentional future baseline or
public-API change should update its documented evidence and policy explicitly,
without creating another experiment copy or silently weakening acceptance.
