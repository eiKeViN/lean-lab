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

`kl-blobs.tsv` covers the files under `experiments/kl/OAI`. Run
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
`experiments/kl/OAI/RepresentationTheory/KazhdanLusztig/Invariance.lean`.
Its body and statement have not been edited. The comparator permits only
`propext`, `Quot.sound`, and `Classical.choice`, and sets `enable_nanoda=false`.
No comparator or independent kernel-checker run is claimed by this baseline.

Bootstrap release SHA-256 values in `scripts/setup.sh` were measured from the
official HTTPS GitHub release assets on 2026-10-19; they pin the bytes for repeat
installation, not a separately authenticated signature verification. The elan
v4.2.0 installer shell was inspected, but its moving `latest` binary download was
avoided by downloading the fixed release binary. Elan was installed with
`--no-modify-path --default-toolchain none`. Mathlib's lakefile, cache CLI/network
code and ProofWidgets build hooks were inspected before cache/build use.
