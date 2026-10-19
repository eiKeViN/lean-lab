# Fresh worker verification — 2026-10-19 UTC

Cache access succeeded: the initial single GET returned HTTP 200 in 0.393 s.
The exact URL was
`https://cache.mathlib.org/mathlib4-master/f/35d01d0e1a918f6e.ltar`.
Headers are in [evidence/cache-fresh-task-probe.headers](evidence/cache-fresh-task-probe.headers).
No alternate route or access-setting change was used. The fallback host was not probed.

The fresh checkout had no local toolchain or dependency caches. Full setup restored
all 8908 official cache artifacts. Lean reports 4.34.1, commit
`5045d0056413266e57c625dcd7c365b10e377c52`; Lake reports 5.0.0-src+5045d00.
Mathlib remains pinned to `d13f23b723b8a846827a245b89c10fc7d3f11612`,
with all eight manifest dependencies at their locked revisions. All 34 KL source
blobs matched the preserved upstream manifest. No mathematics was edited.

## Measured commands

| Result label | Exit | Wall seconds | Peak child RSS KiB |
| --- | --- | --- | --- |
| `cache-fresh-task-probe` | `0` | 0.393 | 10112 |
| `setup-fresh` | `0` | 528.804 | 994676 |
| `smoke-fresh` | `0` | 1.444 | 1030012 |
| `setup-warm` | `0` | 4.398 | 994164 |
| `kl-initial` | `0` | 1210.827 | 7751892 |
| `audit` | `0` | 4.299 | 7400332 |
| `kl-warm` | `0` | 3.398 | 993032 |
| `maintenance` | `0` | 5.273 | 991012 |

The probe and setup were measured with `python3 scripts/measure.py
results/<label>.log <command>`. Smoke/KL/audit use `bash scripts/check.sh
<mode> <label>`. Timings cover the recorded subprocess, excluding the source
verification and KL readiness guard in `check.sh`; RSS is the maximum child
process RSS, not aggregate parallel memory. Fresh setup includes downloads,
extraction, dependency cloning and binary-cache restoration. Initial setup used
the original cache path (including its primary-host preflight).
Warm setup used the reviewed cache-readiness helper, was measured during the
initial KL build, and skipped network cache access.

Commands executed, in order:

```bash
python3 scripts/measure.py results/cache-fresh-task-probe.log curl --fail --silent --show-error --location --max-time 20 --dump-header reports/evidence/cache-fresh-task-probe.headers https://cache.mathlib.org/mathlib4-master/f/35d01d0e1a918f6e.ltar -o /dev/null
python3 scripts/measure.py results/setup-fresh.log bash scripts/setup.sh
bash scripts/check.sh smoke smoke-fresh
bash scripts/check.sh kl kl-initial
python3 scripts/measure.py results/setup-warm.log bash scripts/setup.sh
bash scripts/check.sh audit audit
bash scripts/check.sh kl kl-warm
python3 scripts/test_checks.py
bash -n scripts/*.sh
git diff --check
python3 scripts/measure.py results/maintenance.log bash -c 'bash scripts/setup.sh && bash scripts/check.sh smoke smoke-maintenance'
```

Mathlib readiness passed without building source: all 8923 dependency targets
were up to date. **All 34 unchanged KL modules compiled successfully**, including
`Invariance`, with 8958 total Lake jobs. The initial build took 1210.827 seconds;
`IntegralPairings` was the longest module at 721 seconds. Warm KL build reused
all artifacts and passed in 3.398 seconds. No genuine source failure occurred.

**The main theorem axiom audit passed.** The exact type and proof printout are
saved in [evidence/audit.log](evidence/audit.log). Its recursive kernel closure is:

```text
'OAI.KLInvariance.combinatorial_invariance' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The audit's explicit allowlist check accepted exactly those three axioms.
No `sorryAx` or other axioms were reported. Selected command logs and complete
measurement JSON are committed in [evidence/](evidence/).

## Script review

- Replaced validation assertions with explicit failures so `PYTHONOPTIMIZE=1`
  cannot disable source/pin checks or the axiom allowlist.
- Audit parsing requires exactly one closure for the exact implementation theorem
  `OAI.KLInvariance.combinatorial_invariance`; allowed axioms remain only
  `propext`, `Quot.sound`, `Classical.choice`.
- Dependency verification now rejects tracked modifications in available checkouts.
- Setup first checks Mathlib readiness without source building and skips cache
  network access when ready. An optional `CACHE_PROBE_URL` names a deliberate
  diagnostic artifact; the official cache tool retains its endpoint configuration.
  Failed downloads and incomplete cache restoration stop setup. No source-build fallback.
- `python3 scripts/test_checks.py` passed rejection cases for missing/wrong theorem
  output, forbidden/sorryAx axioms, source hash and toolchain/mathlib pin mismatch
  under both optimization modes; stubbed warm-cache, failed-download, incomplete-cache,
  and denied-probe paths also passed. No network or Lean build in these tests.
  `bash -n scripts/*.sh` and `git diff --check` passed.

## Repository state and reproducibility

Read-only GitHub and Git transport checks found PR #1 already merged at
2026-10-19 07:32:21 UTC, merge commit `2e4ef72407451f47da1b3bf1d4ad2344b2840aab`.
Fetched current main has the same tree as the reviewed head
`a3ffb84dff9f5e5c84a723b6fd0cf5225f5e684d`. This task did not merge it.
Following the updated instruction, follow-up work is local on
`codex/kl-cache-verification`, based on that main commit. No closed-PR update,
new PR, or push has been performed. Parent coordination is required for publication.
Only lean-lab was modified; no preserved upstream lakefile was executed.

Tested setup/maintenance command for the saved environment UI:

```bash
cd /workspace/lean-lab && bash scripts/setup.sh && bash scripts/check.sh smoke
```

The equivalent combined setup-plus-smoke command passed in 5.273 seconds
(final validation, smoke result label `smoke-maintenance`). It installs exact
tools/dependencies when absent and reuses complete Mathlib artifacts. No saved UI configuration was changed or verified here. The worker
has a 4-CPU quota and 16 GiB RAM limit. No caches from the earlier worker were
present in
this fresh checkout; same-worker reuse works. Final footprint: about 4.0 GiB in
`.cache` and 8.0 GiB in the KL `.lake` (roughly 19 GiB disk remained free).
Comparator equivalence and an independent kernel checker remain outside these checks.

There are no remaining network, KL compilation, or axiom-audit blockers in this worker.
Publication is intentionally pending parent coordination after the PR merge.
