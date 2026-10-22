# Three-file module integration

This stage integrates the approved pilot into the maintained project. It starts
from `3beae71a3edd8a817821d6f84eb49a9bb1a4681c` on
`codex/module-import-pilot`; the remote head and clean worktree were verified before
editing. Lean remains 4.34.1 at `5045d0056413266e57c625dcd7c365b10e377c52`,
Mathlib remains `d13f23b723b8a846827a245b89c10fc7d3f11612`. The project and
lockfile remain in `experiments/kl-for-mathlib`.

## Source and API policy

Only these three product files change:

- `ForMathlib/Algebra/BigOperators/SingleCoordinate.lean`: `module`, four
  conservatively public narrow imports, and `public section`.
- `ForMathlib/LinearAlgebra/KernelTransport.lean`: `module`, `public import Mathlib`,
  `public section`, and `@[expose]` on the three existing kernel equivalences.
- `OAI/KL/Compatibility/KernelTransport.lean`: `module`, public re-export of its
  producer, `public section`, and `@[expose]` on all three existing old-name wrappers.

No statement, proof, definition body or instance changes. `module-integration.json`
binds each before/after SHA-256 to the exact starting Git tree. The small syntax
layer has an independent hardcoded three-path/import/expose allowlist. It reverses
only those exact syntax changes before the original hash/diff-bound proof-evolution
checks, then reapplies them after pristine reconstruction and proof evolution.
All unselected products remain subject to the existing byte-for-byte reconstruction.
The original source snapshots, proof-evolution patch, public-type reference,
additional 45-type snapshot and three-axiom policy remain unchanged.

`module-import-graph.json` records every owned node's module status and each import's
`public`, `meta`, `all` flags and source line. These are explicit syntax flags;
legacy effective implementation loading is distinguished by the node module flag. The DAG generator reads these edges;
the kernel wrapper's public edge is no longer lost by a bare-import regex. The
selected import flags are checked exactly, and module/import modifiers on unselected
product files are rejected. Original theorem-header checks use the exact inverse
syntax layer; immutable source-span coverage retains its original algorithm.

## Implementation and public audits

The original `PublicTypes.lean`, `PilotChecks.lean` and `SemanticCorpus.lean` retain
their full implementation interpretation through legacy `OAI.Architecture`/`OAI.KL`
imports. The inherited exporter and comparator are unchanged. Its duplicate-record
and proof-value checks remain fail-closed; no declaration-kind exception was added.
A scoped export of the eleven selected declarations passed before the full build.

`ModernPublicTypes.lean` is a generated, bounded public consumer. It reuses the
original type serializer and its adversarial serialization controls, then checks
exactly five selected theorem names and six exposed definition names. The five
public theorems must be `axiomInfo` **and** originally `.thm`; each of the six
exposed definitions must be `defnInfo` and originally `.defn`. Only this named set
uses the public-view representation rule. The exported types are compared against
the same original/additional snapshots, retaining names, binder information,
universes and expression structure. Producer-exported axiom closures must stay
within `propext`, `Quot.sound`, `Classical.choice`. Unexpected private/proof aliases
in these selected types fail rather than gaining a new prefix-normalization rule.

`ModernCompatChecks.lean` is exactly `module` followed by the unchanged original
CompatChecks body, including its import-set assertion and all nine old-name,
`rfl`, `.val`, and inverse-map examples. Both generated audits are checked byte for
byte against their generators. `LegacyKernelEntryChecks.lean` imports both original
kernel paths and replays the same nine examples with an exact four-node closure
assertion. The `--record` path uses the same inverse syntax projection; a real
record run leaves the prior proof-evolution and added-type snapshot bytes identical.
The navigation reader explicitly recognizes the selected `@[expose]` prefix. Source-layer regressions check roundtrips, manifest
expansion/rebinding, proof/statement edits, import flags, and missing/extra/changed
public types. The existing proof-evolution tests use the exact legacy projection
as their fixture so that their original adversarial tests still exercise that layer.
The legacy SemanticCorpus export audits implementation/server documentation; it
does not establish documentation availability in the ordinary modern public view.

## Re-export boundary

The maintained owned API and the previous accidental broad Mathlib environment are
different contracts. SingleCoordinate now intentionally exposes the four imports
validated by the pilot. Clients using it or its focused compatibility path as an
arbitrary Mathlib umbrella may need to import their actual dependencies explicitly.
The main `OAI.KL` entrypoint, candidate aggregate and architecture aggregate retain
their original source entrypoints and are included in the real downstream build.
The kernel cluster retains broad Mathlib re-export and its old reduction promises.
No other implementation migration or consumer production edit is authorized by
this integration; any concrete need would be reported before expanding the scope.

## Execution identity and cost

`recorded_run.py` captures actual file hashes, Git head, tracked dirty-diff hash,
command and timestamp **before** launching each recorded command. Newly added
untracked input files and directly supplied source paths are included. Existing
identity files cannot be overwritten. The final acceptance command uses the script
and input revisions recorded for that execution; no old harness hash is inferred.
This stage does not repeat the pilot's four-grid or edit-cycle microbenchmarks.

The existing setup completed in 6.27 s using ready fixed upstream artifacts. The
initial three integrated targets built in 11.07 s. A new public-audit fixture first
failed because `theorem` was used as a variable name (4.58 s); changing that local
fixture variable to `isThm` produced the expected eleven-type result (4.86 s).
These are integration costs, not estimates of clean whole-library speedup.


The focused compatibility entrypoint resolves the two tested owned weighted-sum
names, but `MeasureTheory.Integrable` is now an unknown identifier there. A separate
explicit `import Mathlib` resolves that same symbol. This is a deliberate reduction
of accidental re-export; external code relying on it must import Mathlib or its
actual measure-theory dependency directly. No project production consumer required
such an edit. Other legacy compatibility entrypoints remain legacy: modern clients
should import the selected current module paths, not assume every old path migrated.

With all project targets ready, the read-only `lake shake --keep-public
ForMathlib.Algebra.BigOperators.SingleCoordinate` preflight now completes. It
returns status 1 with a suggestion to remove the direct public
`Mathlib.Algebra.BigOperators.Ring.Finset` edge. The approved four-import set is
retained: this keeps the documented direct-dependency policy conservative, and deleting that implied edge
would not itself establish a smaller closure. No `--fix` or `--force` was used.
This diagnostic is recorded separately from acceptance checks.


## Final acceptance and reproducibility

The final code revision passes **all 37 stages** of `scripts/check.sh warm` after
an actual full `lake build ForMathlib OAI` in this environment. The strict
implementation comparison reports 3902/3902 original declarations and 45/45 added
theorems, with no missing, extra or changed types. The separate modern comparison
reports 11/11, unchanged. Original and modern kernel reduction tests, both original
kernel import entrypoints, the KL project entrypoint, candidate aggregate and
architecture aggregate are built/tested. All sixteen main axiom closures and the
81-name pilot audit retain the original three-axiom restrictions; the main theorem
still has exactly the required three-axiom closure.

Regression results: 31 inherited comparator tests, 14 source-partition tests,
30 proof-evolution tests, seven new integration tests, and 18 root offline failure
checks pass. Fresh legacy SemanticCorpus export produces 2627 theorem records;
all 45 indexed added lemma docstrings match their compiled source, and generated
line anchors are refreshed. The existing unused-section-variable linter warnings
in IntegralSupport and Invariance.Finite remain; no proof/assumption changes were
made to suppress them.

The whole 261-product tree was compiled; exactly three production sources differ
from the starting tree, and the other 258 are byte-identical. Their allowed inverse
transforms recover the exact starting bytes, including all statements and bodies.
Fourteen original audit/snapshot/configuration files remain byte-identical (see
`scope-and-identity.json`). No production consumer import repair was needed.
Comparison relocation counts refer to the original historical transport snapshot;
this stage does not relocate any declaration's source module.

| Recorded operation | Wall seconds | Result |
|---|---:|---|
| Existing fixed-cache setup | 6.27 | ready |
| Three integrated target build | 11.07 | pass |
| Full local library build | 2163.26 | pass |
| First complete acceptance, including that build | 2288.72 | all 36 then-current stages pass |
| Final code revision warm acceptance | 133.41 | all 37 stages pass |
| Final whole-project no-build readiness | 3.99 | ready |
| Final no-change library build | 3.82 | no recompilation |

The full local build includes first compilation of many previously unready project
modules, not just an incremental consequence of the three-file change. Its per-job
Lake times include waiting for the inherited compiler lock and must not be summed
as isolated elaboration timings. The complete command peak child RSS is about
7.42 GiB, not summed parallel-process RSS. The fixed quota is four CPU and 16 GiB,
`LEAN_NUM_THREADS=4`, with the existing serial compiler gate. No before/after
whole-library speedup comparison or token telemetry is claimed. Command timing
excludes pre-launch identity hashing, report writing and operator time.

There are two explicitly distinguished accepted execution revisions. The first
full pass captures its actual older helper versions in
`full-validation.inputs.json.gz`; `first-pass-input-sources.json.gz` preserves all
18 then-dirty/untracked input files, checked against those captured hashes. After
that process ended, the record command projection, declaration navigation, and old
entrypoint fixture were finalized. `final-warm.inputs.json.gz` captures the actual
final code before its execution; the source/code/configuration hashes match the
delivered files. Final report/evidence metadata was written afterwards. No
execution-time hashes or missing measurement rows were reconstructed from a later
version. Earlier fixture attempts also retain their own captured input identities.

Run from the repository root:

```bash
bash scripts/setup.sh
source scripts/env.sh
python3 scripts/recorded_run.py results/my-integration/full.log bash scripts/check.sh
# Once artifacts are ready, the complete acceptance without rebuilding products:
python3 scripts/recorded_run.py results/my-integration/warm.log bash scripts/check.sh warm
```

Use a new result path for each recorded execution. To regenerate the bounded audit
fixtures after an intentional generator change:

```bash
python3 experiments/kl-for-mathlib/module_integration.py --write-checks
```

[Retained evidence](evidence/module-integration/) includes actual build/stage logs,
execution inputs, strict comparisons, axiom output, current full/public type exports
and checksums, the fresh corpus, source scope, boundary probes and the diagnostic
shake result. The gzip type exports can be compared offline with the unchanged
comparator; doing so rechecks captured evidence rather than re-elaborating Lean.

The integration is complete within its three-file scope. Remaining limits are the
intentional focused-path re-export reduction, ordinary modern theorem-body hiding,
and legacy status of the other entrypoints/implementations. Larger rollout, proof-
only import-phase refinement and further import minimization require their own
bounded review; no such rollout is part of this branch.
