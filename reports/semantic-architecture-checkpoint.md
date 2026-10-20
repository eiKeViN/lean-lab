# Semantic architecture checkpoint (2026-10-20)

This is a resumable checkpoint requested during a normal long compilation, not
completion. Environment shell/filesystem access is working. Do not terminate or
restart the live builds merely to resume this task.

## Saved implementation

Branch: `codex/kl-semantic-architecture`; base main:
`7ddc53ba8a09ed902fefff86e67a87217518c1d4`.
Implementation commits before this checkpoint: `f3185aa` and
`17b5895d2bd72dfa31ea56217e16fd87580921d1`. The checkpoint commit also saves
the final pending exporter/runner edits; its ID is in the assistant response.

Only `experiments/kl-architecture/` and the two new architecture reports changed.
All three prior experiments, root scripts and provenance are unchanged.
No push, PR, merge, saved setting or permission change was performed.

The new experiment contains 193 semantic implementation modules, 34 legacy
import-only shims, two unchanged kernel modules, and `OAI.Architecture` (230 OAI
modules total). It transports 525 original units. Old-to-new inclusive source
ranges and direct imports are generated in `MIGRATION.md`; exact source hashes,
context and annotations are in `migration.json`.

The semantic homes are Mathlib-object extensions (`Algebra/Module`,
`LinearAlgebra`, `RingTheory`, `Data/Polynomial`, `Order`); Coxeter/Bruhat,
realizations, roots and dihedral/parabolic geometry; general directed paths and
signed counting; general moment-graph sheaf APIs; Hecke operators/path bridges;
concrete Bott–Samelson words/stalks/pairings; and KL-specific normalization,
sheaves, localization, comparison and invariance.

No theorem or proof was split and no helper API was added. Mathematical bodies
are copied verbatim. Necessary adaptations pin 76 existing anonymous instance
names and restore the original local decidability instance attribute in the
separated Hecke inverse module. Public type preservation still needs the final
comparison; do not infer that it has passed from source copying alone.

## Checks actually completed

- Root `scripts/verify.py`: 34 pristine source blobs and dependency/toolchain pins
  match. Lean 4.34.1, commit `5045d0056413266e57c625dcd7c365b10e377c52`;
  Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.
- New experiment `lake --no-build build Mathlib`: ready, 8923 jobs; no Mathlib
  source rebuild or network download was started.
- `migrate.py --check`: all 230 OAI products match the exact replay manifest.
- `source_check.py`: all 35,871 non-comment source lines in all 34 reference files
  are covered, including retained/replicated context.
- Static frozen-tree, changed Lean-source allowlist and acyclic import checks pass.
  Foundation APIs have no Coxeter/sheaf/representation imports; general sheaf APIs
  have no Coxeter/representation imports; Coxeter object APIs have no
  representation imports. Live import-boundary harnesses are still pending.
- Nine adversarial Python comparator tests pass.
- The warm reference exported 3902 public type records using the new documented
  alpha-metadata normalization. A subsequent exporter edit adds an injectivity
  guard on private constants referenced by types; that guard has not yet been
  compiled. The committed snapshot values are unchanged; re-exporting and
  checking them with the final exporter is mandatory (`--refresh-reference`).
- Many new modules compiled, including Bruhat basics, Hecke operators, graded
  modules, root geometry, sheaf basics and Bott–Samelson stalks (150 s including
  compiler-lock queue time). No final full-library pass yet.

## Live builds at the recorded probe

Both build commands are under `experiments/kl-architecture`, using
`LEAN_SYSROOT=$LAB_ROOT/.cache/architecture-serial-toolchain` and
`LAKE_OVERRIDE_LEAN=true`, with a compiler lock. At the probe:

- Lake PID 16253: `lake build OAI`; exec session **73609**;
  log `results/architecture-build-third`.
- Its active Lean PID 17365 was compiling
  `OAI/RepresentationTheory/BottSamelson/Pairings.lean`, elapsed 11:11,
  RSS 7,182,656 KiB. It was still running normally. The previous experiment's
  corresponding long file took about 724 seconds; no timeout or mathematical
  source failure has been reported for this proof.
- The third invocation log has 61 newly completed/rebuilt modules, plus reused
  artifacts from earlier passes. Its last progress line is `[9072/9152]`.
  These are invocation counters, not a claim that exactly 149 current modules
  passed independently.
- Lake PID 17410: targeted integration fixes, exec session **23810**:
  `lake build OAI.RepresentationTheory.Hecke.Inverse
   OAI.GroupTheory.Coxeter.Bruhat.DiamondClosure
   OAI.RepresentationTheory.Hecke.DyerPaths.LexicographicOrder`;
  log `results/architecture-integration-fixes` (empty while queued behind the
  compiler lock). Do not launch duplicates.

The third broad invocation previously recorded a missing local Decidable
instance in Hecke inverse. Its source fix is already saved and queued in the
second command. Therefore that broad invocation is not a passing final build
even if all remaining jobs finish. Earlier interrupted probes and all metrics
remain under `results/architecture-build-{first,second,third}*`; completed
artifacts were preserved. Section/comment boundaries and the first annotation
replay bug were fixed without altering mathematical proofs.

## Resume sequence

First inspect actual live state and logs; PIDs above are observations, not
permanent identifiers. Poll existing exec sessions or logs while builds remain
active. In particular, do not queue another full build while the long pairing
module is still running: that could compile the same cold module twice.

After both existing build invocations finish, inspect their outcomes and run:

```bash
cd /workspace/lean-lab
bash experiments/kl-architecture/check.sh --refresh-reference
```

This runner verifies frozen source/pins/coverage/import direction, Mathlib cache,
then builds all current OAI modules, runs independent import checks and inherited
kernel/compatibility/signed boundary checks, audits sixteen axiom closures,
re-exports and validates the reference snapshot, compares all 3902 public types,
runs comparator tests and a warm repeat. It propagates failures. Public type
comparison ignores binder display names, expression metadata and injectively
mapped compiler-private OAI owner prefixes; all names, kinds, universes, binder
implicitness and mathematical expression structure stay exact. It does not
extend or modify the earlier 31-field exception policy.

Fix only migration/integration bugs if needed. Report a genuine source proof
failure before changing mathematics. Finish the actual checks, replace the
in-progress report text with exact results/timings/limits, commit locally, and
provide an accessible review packet or all essential evidence in the final
response. No push or merge is authorized for this round.

### Update immediately before returning the checkpoint

The long `BottSamelson.Pairings` module finished successfully (Lake reported
720 s, including lock queue time). The two Lake drivers are still running;
targeted `Hecke.Inverse` also passed (23 s including queue time), and the
revised `Order.Interval.Diamonds` passed in the targeted invocation. The broad
invocation reached `[9090/9152]`. It additionally recorded a missing
`OAI/Order/Interval/Diamonds.olean` while compiling the dihedral consumer during
integration rebuilding. This is an actual failed compilation action, not a
permission denial; do not mark it resolved until the final sequential runner
passes after both current invocations have finished. No mathematical source
change was made for it. At the last probe the active compiler had advanced to
general sheaf localization. The Pairings artifact should now be reused;
do not rebuild it cold on resume.
