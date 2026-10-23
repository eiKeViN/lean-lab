# Three graph/sheaf module interfaces after PR #8

The independent `codex/module-next-region` candidate migrates only
`Bruhat.Basic`, `Sheaf.Duality`, and `GradedSheaf.Reindex` under
`ForMathlib.Combinatorics.MomentGraph`. All 54 integration stages pass. The
complete 3947-record export has **zero differences against accepted main**,
including owner, kind, universes and serialized type expression. The modern
region is now 131/261 products; 130 remain legacy. This branch is for review,
not authorized for automatic merge.

## Authorized previous merge

[PR #8](https://github.com/eiKeViN/lean-lab/pull/8) was created as draft, made ready
and merged with a merge commit after checking exact accepted head
`d35dd1b879f34f371065f77375d73de84b5b3d14`. Main became
`7e28e636991b2205d14199377f33bd025b348b2d`, with parents
`bc7cc147e9742f8f6c77a53785813dbdd6960311` and that accepted head. Both accepted
and merged trees are `605376e41bbe00f3d5f38c70ae8bf3b2013e63e0`. Remote fetch,
parent inspection and tree comparison confirmed this before starting the new
branch. [Merge record](evidence/module-next/merge-record.json) preserves the
execution result. A direct read-only `gh` API call returned Forbidden; connected
GitHub tools completed the authorized workflow. No main change was overwritten.

## Scope and source protection

The new branch starts at that merge. Code checkpoint
`82b154b9b52a7026e54d105e6b5fde40be68c423` was clean when full validation began.
The only production changes are module headers, public imports/public sections
and exposed definition bodies in the three producers. No declaration statement,
proof or computational body was rewritten, and no inference fix was needed.
The exact forward/inverse transport is hash-bound in
[`module-next.json`](../experiments/kl-for-mathlib/module-next.json) and
[`module_next.py`](../experiments/kl-for-mathlib/module_next.py).

[Source identity](evidence/module-next/source-identity.json) checks all 261
products against the merge: exactly those three changed, 258 unchanged,
including restored legacy `OrderedGraph.VertexDeletion`. Existing historical
snapshots, comparison algorithm, proof-evolution policies, AttachBottom edits,
and the exact stalk-equation policy/DAG/live witness remain byte-identical.
The generated dependency graph and metrics were regenerated; checker changes
compose this bounded transport with earlier ones and add strict tests, rather
than altering the historical expectations.

Lean remains 4.34.1 (`5045d0056413266e57c625dcd7c365b10e377c52`), Mathlib remains
`d13f23b723b8a846827a245b89c10fc7d3f11612`, with a clean dependency checkout.
This execution reused the ready official-cache environment. Fresh initialization
was **not run or measured**; no dependency update or full Mathlib source build
was performed. `lake --no-build build Mathlib` passed.

## Acceptance evidence

The [54-stage manifest](evidence/module-next/stages/stages.json), all stage logs,
input identities and full exports are retained under
[evidence/module-next](evidence/module-next/README.md).

| Check | Actual result |
| --- | --- |
| Source transport, provenance, coverage, boundaries | pass |
| ForMathlib and actual OAI downstream build | pass, 9186 jobs |
| Ordinary modern three-module consumer | pass: exact names, `rfl`, `simp`, inverse law, definition body access |
| Public producer records through ordinary modern imports | 61/61, zero missing/added/type/owner differences |
| Full implementation export vs merged main | 3947/3947, zero differences or relocations |
| Original historical comparison | inherited exact stalk-equation representation difference remains raw and explicitly accepted; no new exception |
| Existing ordinary stalk historical-type/defeq/rw/simp witness | pass again |
| Audited axioms | bounded by `propext`, `Classical.choice`, `Quot.sound` |
| Existing module/rollout/source/comparator/proof regressions | pass |
| Final unchanged-input warm build | pass |

[`ModernNextConsumer.lean`](../experiments/kl-for-mathlib/ModernNextConsumer.lean)
imports only the three producers and Lean, using ordinary `import` in a modern
module. It checks Bruhat graph endpoints and label by `rfl`, label multiplication
by `simp`, reindex vertices/assignments by `rfl` and inverse by `simp`, product
and supported stalk realization by `rfl`, and the linear equivalence inverse law.
`ModernNextTypes.lean` checks all 61 historical producer types/kinds/universes and
their axioms with the existing finite alias serializer. These consumers do not
use `import all`. The legacy implementation exporter intentionally remains the
separate complete audit path.

The new full comparison reads the immutable accepted-main export from Git;
there is no new representation acceptance. The older raw comparison still
reports the single original `Sheaf.stalkMap.eq_1` expression delta. Its existing
version/hash-bound policy and live ordinary witness pass unchanged. Neither
this result nor the regional classifier grants a general defeq waiver.

## Rejected fourth module and remaining boundary

A bounded first probe additionally migrated `OrderedGraph.VertexDeletion`.
All four producers compiled, but the 379-record regional export found two type
expression differences (zero missing/added/relocated):

| Name suffix in `OAI.KLInvariance.MomentGraph` | Old hash | Trial hash |
| --- | --- | --- |
| `splitEdge.eq_1` | `1584e8805d76bb88e0e066182a02cdf8181141336082a9b0c9a53edcf099f40a` | `93dcd676c6ddd201fd3679f9e8f9ab10087070fc408c88b6cefdfe2c0dfb7763` |
| `splitVertex.eq_1` | `0b7862d103f3c1ee9eb529ea02de00b2efe8e8a999a9adb50ed866aa308a7cda` | `d26b083b999b5e04dbb9ef51316d007ebb13f17ac3234d390512bc57a894bbca` |

Both retained kind `theorem`, universe `[um]`, owner
`ForMathlib.Combinatorics.MomentGraph.OrderedGraph.VertexDeletion` and names.
A structural probe of each equation's RHS `Equiv.mk` found matching canonical
hashes for domain/codomain/toFun/invFun, and differing left/right inverse proof
field hashes. That probe does **not** classify all other portions of the type,
prove live definitional equality, or establish ordinary historical-type API
acceptance. It does not establish a mathematical inequality either.

The production file was restored exactly to merged main, and regional export
then passed all 379 records strictly. No proof rewrite, private-helper exposure,
expose removal, name deletion or compatibility waiver was introduced. The
retained trial source, scope, raw TSV, comparison and classifier allow focused
follow-up; VertexDeletion is not delivered in this migration. Any future
acceptance needs its own actual old/new-type and ordinary-consumer evidence.
Other known private/expose boundaries remain outside this batch.

## Reproduction and actual cost

From the repository root, in the existing initialized environment:

```sh
source scripts/env.sh
python3 scripts/recorded_run.py results/module-next-replay/full.log bash scripts/check.sh
```

The recorder refuses to overwrite a recorded input identity; choose a fresh
result path. Setup on a fresh machine uses `scripts/setup.sh` and its official
cache path, with initialization cost recorded separately. Focused checks are:

```sh
cd experiments/kl-for-mathlib
lake env lean ModernNextConsumer.lean
LEAN_TYPES_OUT=/tmp/module-next-types.tsv lake env lean ModernNextTypes.lean
python3 module_next.py --compare-public /tmp/module-next-types.tsv
python3 module_next.py --compare-full ../../results/for-mathlib/migrated-types.tsv
python3 test_module_next.py
```

The `--compare-full` line replays the saved export unless preceded by a fresh
full audit; it is not a fresh historical elaboration. Regional failed trial
commands and exact input hashes remain in their recorded metrics and identities.
The classifier reads the retained accepted-main and trial TSVs; restore those
in the paths at the top of its small script to rerun it, without mutating any
production source. The first classifier used the same JSON output stem as the
measurement recorder, which overwrote its result with cost metadata; its log
retains the output. The final distinct result path and narrowed interpretation
are retained, alongside both earlier logs. This was a diagnostic-output naming
correction after validation, not a Lean/checker change.

Full integration: **2233.680 s wall**, 2529.906 s child user CPU, 233.856 s child
system CPU, 7,333,184 KiB child maximum RSS. Library build: 1958.846 s wall;
final no-change warm build: 6.287 s. The pre-run record bound all **1509 inputs**;
all matched at completion. Cheap work before integration included four-module
build 27.218 s, failed regional export 14.389 s, restore build 17.678 s, safe
regional export 18.637 s, initial consumer 20.581 s, static checks 17.544 s,
and final local checks 22.276 s. Failed comparisons are preserved, not counted
as accepted runs. These are integration timings with dependency invalidation
and compiler locking, not controlled cold/warm speed comparisons. Child maximum
RSS is not total concurrent memory, and queued Lake job times must not be added.
Token telemetry is unavailable. Local results make no GitHub CI claim.

Only report/navigation/evidence files were added after the complete run; all
executed Lean sources, policies and checker inputs remain as validated. No
second full build was started after success. The next branch is pushed for
review; merging it still requires a new instruction.

## External review action blocked

The independent branch was pushed successfully. Optional creation of a **draft**
PR in `eiKeViN/lean-lab`, from `codex/module-next-region` to `main`, was rejected
by automatic approval review. Its first reason treated the earlier upstream-PR
prohibition as applicable. After verifying this is the same repository and
consulting the later delegation permitting an optional draft, exactly one retry
was rejected again: the reviewer requires direct user approval for this exact
external commitment. Both operations were denied, not uncertain; no PR was
created. No bypass or further retry was attempted. This blocks only PR creation,
not the pushed branch, completed validation, or report. Main is unchanged at
`7e28e636991b2205d14199377f33bd025b348b2d`. Direct user approval is required if a
new draft PR is desired. See [action status](evidence/module-next/pr-action-status.json).
