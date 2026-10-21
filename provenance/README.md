# KL provenance

- Canonical project: [OpenAI math / KL](https://github.com/openai/math/tree/main/lean/OAI/RepresentationTheory/KazhdanLusztig).
- Preserved upstream: [agoramachina/openai-math](https://github.com/agoramachina/openai-math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a), revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
- Transport snapshot: [jiajunma/combkl](https://github.com/jiajunma/combkl/tree/70211c3350c1f203aa8f52f1809e57d7ae93ba78/sources), revision `70211c3350c1f203aa8f52f1809e57d7ae93ba78`, from branch `codex/kl-source-snapshot`.
  The branch had advanced to `182360416f2335403a33a4deb0ddaf8d58129030` at retrieval;
  this lab deliberately uses the audited fixed revision, not that moving tip.
- Retrieved and rechecked 2026-10-19: all 34 KL files were copied byte-for-byte.
  Every file was also fetched independently from the fixed upstream raw GitHub
  URL and its Git blob SHA-1 matched. This is a source identity check, not a proof check.
- Pins rechecked against preserved metadata and official mathlib metadata:
  Lean `leanprover/lean4:v4.34.1`, mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.

`kl-blobs.tsv` covers the historical `experiments/kl/OAI` tree at
`7ddc53ba8a09ed902fefff86e67a87217518c1d4`. That directory is no longer a
working checkout. Run
`python3 scripts/verify.py` to compare them with the preserved upstream manifest.
`upstream.manifest.tsv` is the original broader 81-file manifest; this lab does
not claim to vendor all of its entries. Internal imports resolve within the 34
files; the only direct external module import is `Mathlib`.

The original repository and Lean Apache-2.0 licenses are retained as
`upstream-LICENSE` and `lean-LICENSE`; original file contents, attribution and
copyright headers are unchanged. New lab tooling is also licensed under the
root Apache-2.0 LICENSE. OpenAI and upstream authors retain their attribution.

`upstream-lakefile.lean.txt` is inert reference text, never executed. Its unrelated
dependencies and configuration-time clone/patch hooks are excluded from the new
minimal TOML package. `upstream-lake-manifest.json` is evidence, not the active
manifest. The active manifest contains mathlib and its eight pinned dependencies.

`challenge.lean.txt` and `comparator.json` are reference material. The challenge's
`sorry` is the expected comparator placeholder, not the implementation proof.
The implementation is `OAI.KLInvariance.combinatorial_invariance` in
`7ddc53ba8a09ed902fefff86e67a87217518c1d4:experiments/kl/OAI/RepresentationTheory/KazhdanLusztig/Invariance.lean`.
That historical baseline remains exact. The maintained project is
`experiments/kl-for-mathlib`; subsequent approved refactoring history is retained. The comparator permits only
`propext`, `Quot.sound`, and `Classical.choice`, and sets `enable_nanoda=false`.
No comparator or independent kernel-checker run is claimed by this baseline.

Bootstrap release SHA-256 values in `scripts/setup.sh` were measured from the
official HTTPS GitHub release assets on 2026-10-19; they pin the bytes for repeat
installation, not a separately authenticated signature verification. The elan
v4.2.0 installer shell was inspected, but its moving `latest` binary download was
avoided by downloading the fixed release binary. Elan was installed with
`--no-modify-path --default-toolchain none`. Mathlib's lakefile, cache CLI/network
code and ProofWidgets build hooks were inspected before cache/build use.


## Baselines after project consolidation

`baselines.json` names exact source, policy and published Git snapshots. They are
ancestors of the maintained branch and remain recoverable after deleting old
working directories. `scripts/baseline.py` checks commit availability and each
retrieved blob SHA; it neither checks out another experiment nor executes any
historical lakefile. `scripts/setup.sh` fetches a missing pinned commit if needed
for a shallow clone. Ordinary verification stays offline and fails with an
explicit recovery command if history is missing.

`kl-reference-types.tsv.gz` is the full kernel-exported reference DAG captured
and compared in the validated `85b3d1a` run. Compressed/uncompressed SHA-256,
length, exporter hash, source commit and prior verification evidence are in
`baselines.json`. The current checker decompresses and reparses all 3902 entries,
requires a complete export, and compares it with the committed type snapshot.
This preserves independent baseline evidence without a second maintained Lean
project. It is evidence replay, not a new compilation of historical source.
The current library is still built/checked separately and audited against the
three permitted axioms.

Examples (Git data, not working source copies):

```bash
git show 7ddc53ba8a09ed902fefff86e67a87217518c1d4:experiments/kl/lean-toolchain
python3 scripts/baseline.py
bash scripts/check.sh static
```

Original licenses, broader upstream manifest, challenge/comparator material and
all previously committed build/audit evidence remain retained. No remote tags,
new experiment copies or upstream contribution are required for this layout.
