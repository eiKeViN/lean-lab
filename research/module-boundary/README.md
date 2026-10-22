# Pinned module boundary research

See [decision report](../../reports/module-boundary-reproducers.md) for scope, limits,
policy choices, failures, costs and exact pins. All fixtures are diagnostic; none
replace production source, comparators or compatibility policy.

From repository root, use new output paths:

```bash
bash scripts/setup.sh
python3 scripts/recorded_run.py results/boundary-new/core.log python3 research/module-boundary/run_core.py results/boundary-new/core
python3 scripts/recorded_run.py results/boundary-new/project.log python3 research/module-boundary/run_project.py results/boundary-new/project
python3 scripts/recorded_run.py results/boundary-new/retained.log python3 research/module-boundary/inspect_retained.py
```

`run_core.py` checks expected successes and failures without Mathlib.
`run_project.py` requires official Mathlib artifacts before any bounded local
build and prepares exactly two shadow dependency fixtures from the immutable
rejected-131 manifest. It never rewrites production files or existing artifacts.
The source-unchanged generic failure is expected exit 1; explicit parameters,
private comparison, whole AttachBottom diagnostic and actual equation comparison
must exit 0. The local `backward.proofsInPublic` core test is diagnostic only.

The real equation comparison preserves full legacy auxiliary proofs and checks
them with the kernel under fresh names. The codec ignores only metadata and is
not connected to the production serializer or acceptance pipeline. No added
axiom, sorry, matcher waiver or global normalization is used.

To link the real defeq check to the exact historical records, after the project
suite use its shadow path and another fresh output directory:

```bash
python3 scripts/recorded_run.py results/boundary-new/fingerprint.log python3 research/module-boundary/verify_historical_fingerprint.py results/boundary-new/project/shadow results/boundary-new/fingerprint
```

This generates a one-equation probe using the unchanged production serializer
and comparator, and requires both fresh hashes to equal the retained old/new
rejected-131 fingerprints. It does not weaken or replace the complete audit.
