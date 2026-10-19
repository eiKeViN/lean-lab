# Baseline evidence — 2026-10-19

## Current verified result — fresh worker

The documented cache GET now returns **HTTP 200**. Full pinned setup restored
8908 artifacts; all **34 unchanged KL modules compile successfully** (1210.827 s).
The main theorem's axiom closure is exactly **propext, Classical.choice, Quot.sound**;
the explicit allowlist passed. Warm KL build passed in **3.398 s**, and warm setup
passed in **4.398 s** while skipping cache network access.

See [fresh-task commands, versions, timings, script fixes and evidence](fresh-task.md).
The earlier 403 blocker below is historical and no longer applies in this worker.
PR #1 was already merged before this follow-up; new work is retained locally for
parent-coordinated publication. This task did not merge or update the closed PR.

## Historical blocked-worker record

### Outcome

Environment and small mathlib smoke check succeeded. **Compilation of all 34 KL
modules and the main theorem, and its recursive axiom audit, remain unverified.**
The blocker is official mathlib binary-cache access, not a demonstrated source
failure. No proof bodies or mathematical statements were changed.

### Executed checks

| Check | Observed result |
| --- | --- |
| Repository identity | Empty mounted checkout, branch `work`, origin `https://github.com/eiKeViN/lean-lab.git`; `git ls-remote origin` returned no refs |
| Lean | 4.34.1, commit `5045d0056413266e57c625dcd7c365b10e377c52`, Release, x86_64-unknown-linux-gnu |
| Lake | 5.0.0-src+5045d00 |
| Elan | Fixed v4.2.0 release binary installed locally; no default toolchain set |
| Source identity | 34/34 local blobs match combkl's fixed snapshot and upstream manifest; 34/34 independently fetched upstream blobs also match |
| Import closure | All direct internal imports present; external imports are `Mathlib` |
| Lock | Official mathlib revision and its eight dependencies resolved and committed |
| Initial smoke build | `lake build Smoke`: success, 137 jobs; compiled small dependency subset from source |
| Warm smoke build | `scripts/check.sh smoke smoke-warm`: success, 0.935 s wall, 853716 KiB peak child RSS |
| First measured direct elaboration | `lake env lean Smoke.lean`: success, 1.521 s wall, 1021384 KiB peak child RSS |
| Repeated direct elaboration | Same command: success, 1.571 s wall, 1022016 KiB peak child RSS |
| Full mathlib readiness | `lake --no-build build Mathlib`: failed with missing/out-of-date artifacts, without rebuilding them |
| KL source attempt | `lake env lean OAI/RepresentationTheory/KazhdanLusztig/Coxeter.lean`: fails at line 1, missing `Mathlib.olean` |
| Axiom audit attempt | `lake env lean Audit.lean`: fails because OAI compiled modules are not yet built; no axiom closure obtained |
| Working setup path | `SKIP_CACHE=1 bash scripts/setup.sh` succeeded; smoke then succeeded |
| Full setup path | `bash scripts/setup.sh` exits 22 at the fast cache probe (HTTP 403) |
| Shell validation | `bash -n scripts/env.sh scripts/setup.sh scripts/check.sh` passed |

The initial smoke build was not timed: `/usr/bin/time` is absent, so measurement
was changed to Python `time.monotonic` plus `resource.getrusage`. The two direct
elaboration timings are both after dependency compilation; neither is a claimed
cold-install timing. Peak RSS is OS child-process maximum, not aggregate memory
across parallel workers. Raw selected logs/JSON are in [evidence/](evidence/).

### Download and integration details

1. Cloned combkl into ignored `.cache/combkl` and checked out
   `70211c3350c1f203aa8f52f1809e57d7ae93ba78`. Inspected its instructions and source
   provenance; copied only KL modules, license and relevant reference metadata.
2. Installed official elan v4.2.0 with `--no-modify-path --default-toolchain none`.
   `elan toolchain install leanprover/lean4:v4.34.1` failed with a CONNECT 403.
   Downloaded the official GitHub `lean-4.34.1-linux.tar.zst`, extracted it, and
   used `elan toolchain link leanprover/lean4:v4.34.1 <absolute-release-directory>`.
   Exact verified byte hashes and URLs are encoded in `scripts/setup.sh`.
3. Checked out official mathlib at
   `d13f23b723b8a846827a245b89c10fc7d3f11612`, inspected its configuration/cache
   sources, and generated the minimal package manifest once with
   `MATHLIB_NO_CACHE_ON_UPDATE=1 lake update`. Future setup uses the lock without
   updating. No upstream KL lakefile was executed and no compatibility patches
   were applied.
4. `lake exe cache get` built the small cache executable and attempted 8908 cached
   files. The public endpoint was blocked, so the owned cache processes were
   terminated. Both `https://cache.mathlib.org` and the documented
   `https://lakecache.blob.core.windows.net` fallback returned CONNECT HTTP 403.
   An escalated read-only curl probe was permitted but returned the same 403;
   this was not an automatic approval rejection. No cache miss triggered a full
   mathlib source build. A single-file preflight now makes setup fail promptly.
5. Built the small `Mathlib.Data.Nat.Basic` smoke import from source and ran the
   checks above. A trial direct command named a nonexistent `Basic.lean` KL file;
   it was corrected to `Coxeter.lean`, yielding the actual missing-dependency
   error preserved in evidence. `gh api` metadata lookup also returned Forbidden;
   Git transport was used for repository access.

At measurement, `.cache` occupied about 3.5 GiB and `experiments/kl/.lake` about
608 MiB. The full mathlib cache has not been downloaded. There were no suitable
pre-existing Lean installations or dependency caches in the inspected locations.
The worker had a 4-CPU cgroup quota (`400000 100000`), 16 GiB memory limit
(`17179869184`), and roughly 30 GiB initially available filesystem space.

### Theorem and assumptions

The exact implementation theorem is
`OAI.KLInvariance.combinatorial_invariance`, in `Invariance.lean`, line 547.
It takes Coxeter systems, two comparable interval endpoints and an interval
order isomorphism, and concludes equality of their `klPolynomial` values. The
entire source is byte-identical; this prose does not replace its precise type.

`provenance/challenge.lean.txt` is the comparator challenge placeholder, separate
from the implementation. Its `sorry` is not counted as a missing solution.
`provenance/comparator.json` permits `propext`, `Quot.sound`, `Classical.choice`
and disables Nanoda. **Whether the implementation depends only on these axioms
is still unknown from this run.** `Audit.lean` and the allowlist check are ready,
but neither compilation nor `#print axioms` has succeeded for the theorem yet.
No independent checker or comparator equivalence run was performed.

### Remaining steps

Enable official mathlib-cache access in the saved cloud environment's network
policy, then run from the lab root:

```bash
bash scripts/setup.sh
bash scripts/check.sh smoke
bash scripts/check.sh kl kl-initial
bash scripts/check.sh kl kl-warm
bash scripts/check.sh audit
```

If a genuine KL source failure appears after restoring the intended dependencies,
record it before editing any proof. Save the successful KL logs and axiom closure
in a follow-up commit. No saved environment UI configuration was changed or
verified by this task; the tested setup/maintenance commands are in the README.

### Authorization and cache retest — 2026-10-19 07:30 UTC

After the user added both cache hosts and approved repository publication, each
cache URL was tested once again in this existing task. Both returned HTTP 403,
`server: envoy`, `connection: close`, and a 16-byte text response. The exact
URLs were:

- `https://cache.mathlib.org/mathlib4-master/f/35d01d0e1a918f6e.ltar`
- `https://lakecache.blob.core.windows.net/mathlib4-master/f/35d01d0e1a918f6e.ltar`

Response headers are preserved in `reports/evidence/cache-retest.headers` and
`cache-fallback-retest.headers`. The new allowlist is not effective in this
running task. This may require a fresh task to receive the saved environment
changes; the cause cannot be confirmed from this worker. No alternate route or
full source build was attempted. KL compilation and the axiom audit remain
blocked at the unchanged dependency-readiness stage.

GitHub app write authorization now works: the minimal default-branch README
bootstrap is commit `58685d7d8fd726401a084039a7104bd5f965cb6d`. The prepared local
baseline was applied on top of it to branch `codex/kl-baseline-review`, resolving
the expected README add/add conflict by retaining the complete lab README.
This gives the review branch a valid PR base without merging the deliverable.

The original complete recovery bundle remains unchanged at
`results/lean-lab-baseline.bundle`, containing commit
`ef2fb63a31c610751e2bd5653f1269b247ea0ec5`. Its SHA-256 is
`4ce8764d562b7e02a31bedc122e5db86cc1666900d78aedf895c5375d6489105`.
The earlier HTTP 403 Git push/app failures were authorization errors, not
approval-review rejections. Current publication results are recorded in the PR.
