# FQC external certificate checker

This experiment executes the four certificate batches used by Google's
`TopHadStage1Tab1Shard0.c1_0` outside the Lean kernel, then admits their six-cell
coverage claims as four explicitly named axioms. The final proposition is the
same as upstream `c1_0`. It also freshly elaborates the original computational
proof as a reference; the external route is not described as kernel-only proof.

Upstream: [`google-deepmind/formal-quantum-computation` at `a88de8f`](https://github.com/google-deepmind/formal-quantum-computation/tree/a88de8ff65d78af564b2373088ca369dc95f6547).
Environment: **Lean 4.35.0**, no third-party Lake dependencies. This project owns
its toolchain and manifest, independently of the other lean-lab experiments.

## Run

Prerequisites: Linux/WSL2, Python 3.10+, and the official Lean 4.35.0 toolchain
(with its native compilation tools). An elan installation selects the local
`lean-toolchain` automatically. A standalone installation can be selected with
`export FQC_TOOLCHAIN_DIR=/absolute/path/to/lean-4.35.0-linux`.

```bash
cd experiments/fqc-external-checker
bash scripts/setup.sh
bash scripts/check.sh
```

Setup fetches four exact upstream files, verifies source identities and builds
the native `fqc_checker` executable. `FQC_UPSTREAM_ROOT=/path/to/upstream`
optionally uses a local mirror, still checking every full-file hash. No upstream
Lake configuration, mathlib download or whole-project build is required.

Check performs source/fixture identity, native execution, rejected-input tests,
result-to-claim binding, fresh kernel reference elaboration, public-type checking
and an exact external-axiom audit. It overwrites `results/acceptance.json` with
`running`/`failed` until a complete successful run publishes `passed`.

`bash scripts/check.sh check --generate-facts` regenerates the admitted Lean
facts only after successful native checks, negative tests and kernel references.
Use this explicit mode when reviewing a checker/admission change; normal checks
reject stale or edited generated facts. It does not make the admitted facts
kernel-verified computations.

All raw logs, timing observations, executable hashes and cached reference proofs
remain under ignored `results/`, `.cache/` and `.lake/`. Source and fixtures are
versioned; caches and execution results are not committed.

## Components

| Path | Responsibility |
|---|---|
| `FQCExternal/Vendor/` | Reproducible upstream logic slices, without the selected packed certificate payload |
| `FQCExternal/Entry.lean` | Kernel-checked equivalence and soundness bridge for the executable single-word checker |
| `FQCExternal/Exec.lean` | Executable dictionary and quadtree/stream decoder using upstream exact integer arithmetic |
| `Main.lean` | External JSON reader, native CLI, result echo and exit status |
| `data/c1_0/` | Four external JSON certificates, 53,041 bytes in total |
| `FQCExternal/ExternalFacts.lean` | Four external coverage axioms, with input/checker/admission source hashes |
| `FQCExternal/Claim.lean` | Upstream conjunction proof with the same public proposition and four admitted premises |
| `provenance/upstream.json` | Original blob identities, derived-source identities and retained public type |
| `scripts/source.py`, `scripts/run.py` | Restricted constructor extraction, admission binding, reference runs and audits |

The CLI executes ordinary compiled Lean code. Its checking algorithm uses exact
natural/signed-integer arithmetic, not floating-point sampling. Python performs
orchestration and admission, not the mathematical cell tests. CLI exit statuses:
0 accepted, 1 certificate rejected, 2 input/schema/IO error.

## Verification and trust

The public theorem `FQCExternal.c1_0_external` depends on exactly `propext` and
`FQCExternal.External.batch0` through `batch3`. The single-word correspondence
and soundness lemmas, actual executable entry wrapper, bit expansions, Braun
insertion and cell-check correspondences use only standard axioms (nine audited
bridge lemmas). All four executable certificates
are cross-checked by freshly elaborating upstream's original `decide +kernel`
proof. Corrupted dictionary/stream tags and absent streams/dictionaries are
rejected by both routes; input-hash and result/claim mismatches are also rejected.

The **whole executable decoder's equivalence/soundness is not proved**. Its
implementation, compiler/runtime, JSON parsing and Python admission/binding form
the explicitly trusted external chain. Hashes provide source/input identity, not
a proof of mathematical correctness. Native acceptance introduces named axioms;
neither comments nor a successful process exit are silently treated as proofs.

This experiment stops at the upstream `Stage1BatchCov`/`Stage1SquareCov` interface.
The real/complex geometric interpretation in `TopHadSu2SynthBridge`, full Stage 1,
Stage 2 and the Photochemistry correctness/resource theorems are **not built**.
No claim is made about reducing the full project's 230 GB comparator peak.
Upstream Comparator is **not run**: its original whitelist permits only the
standard three axioms, whereas this experiment deliberately admits four more.
Source identity, Lean compilation, axiom auditing and independent whole-project
comparison are distinct evidence categories.

## Measurement scope

`results/acceptance.json` records native runtime separately from build, admission
and proof elaboration. The reference is a fresh elaboration of the original
`c1_0` computational proof using already-built logic modules, not a Comparator
run. Linux `wait4` max-RSS can include inherited pre-exec memory and is not total
concurrent RAM. These small-sample measurements should not be extrapolated to
the complete Photochemistry project.

One local Linux run recorded the following checkpoint on 2026-11-24 (imports and
native executable already built). These are different verification boundaries,
not an equal-trust speed comparison:

| Phase | Observed wall time |
|---|---:|
| Four native certificate checks, including CLI startup and JSON parsing | 0.24 s total |
| Admitted theorem public-type and nine-bridge axiom audit | 0.27 s |
| Fresh elaboration of original computational `c1_0` proof | 19.14 s |
| Kernel rejection of four corrupted certificates | 1.84 s |

The recorded run also rejected three admission/binding mismatches. A subsequent
run regenerates fresh observations in `results/acceptance.json`; this table is a
checkpoint, not replayed acceptance evidence.
