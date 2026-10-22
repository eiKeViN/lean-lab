# Rejected AttachBottom trial

See [report](../../reports/attach-bottom-explicit-trial.md). These probes target the
actual maintained project with the candidate applied; final production sources
are restored to ed29a2e. They do not compile as an ordinary modern consumer of
the restored legacy AttachBottom and are not an added production test target.

To replay, use the exact base tree and ready pinned cache. From repository root:

```bash
git diff --exit-code ed29a2ef4639ea0eeabb4db8a08755bee430279d -- experiments/kl-for-mathlib scripts provenance
git apply --check reports/evidence/attach-bottom-explicit/final-candidate.patch
git apply reports/evidence/attach-bottom-explicit/final-candidate.patch
source scripts/env.sh
cd experiments/kl-for-mathlib
lake --no-build build Mathlib
lake build ForMathlib.Combinatorics.MomentGraph.GradedSheaf.AttachBottom
lake env lean ../../research/attach-explicit/ModernAttachConsumer.lean
```

For types, use fresh `LEAN_TYPES_OUT` paths with RegionTypes.lean and
ModernTrialTypes.lean. The latter's fixed expected JSON is retained in evidence:
copy it to the literal `results/attach-explicit/modern-expected.json` input path
before running. compare_region.py similarly expects the decompressed retained
reference-full.tsv there. Evidence inputs record exact paths, command and hashes.
The regional comparator must reject the candidate on stalkMap.eq_1; this is not a
production acceptance workflow. Always reverse the patch and rebuild the bounded
target afterwards, including when a command fails:

```bash
cd ../..
git apply -R reports/evidence/attach-bottom-explicit/final-candidate.patch
source scripts/env.sh
cd experiments/kl-for-mathlib
lake build ForMathlib.Combinatorics.MomentGraph.GradedSheaf.AttachBottom
```

The manifest names both explicit grading arguments and all Basic proof edits.
No proof/source allowlist, baseline, production exporter or global policy was
changed. Full-library validation was not run for the rejected candidate.
