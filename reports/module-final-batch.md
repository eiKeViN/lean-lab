# Accepted 25-module dependency batch

This batch on `codex/module-next-region` adds 25 modern modules to the previously
accepted branch checkpoint `0917d25afb52e46cae4233d3056020ed6f881fa3`: **156/261
modern, 105 legacy**. It is not merged. Main remains
`7e28e636991b2205d14199377f33bd025b348b2d`; no PR was created or retried.

All production edits are module/public/expose transport. Declaration statements,
proofs and computational bodies remain byte-identical after independently
removing those additions. Exactly 25 products changed and 236 are unchanged;
see [source identity](evidence/module-final/source-identity.json) and the exact
[source transport](../experiments/kl-for-mathlib/module-final.json).
The scope contains 23 ForMathlib graph/algebra/Coxeter/Hecke producers and the
Sheaves/Tits OAI forwarding modules. Full paths are in that manifest.

## Acceptance and execution identity

The real `lake build ForMathlib OAI` completed all 9186 jobs at source checkpoint
`592bbcd2284d99e117489e19267d91379062544b`. The first integration then stopped at
historical type comparison because the newly composed acceptance code incorrectly
applied the new-owner check to the already established historical owner transport.
That failed run and all 37 recorded stages are retained under
[failed-full-1](evidence/module-final/failed-full-1/).

The fix checkpoint is `491f409adfcdd91e50ca1842311dbaa35e7dc017`. Only
`module_final.py`, `proof_evolution.py` and their regression test changed between
the build and final audit. No Lean, pins, proof data or source transport changed.
The complete **59-stage** `scripts/check.sh warm` run passed, beginning with
`lake --no-build build ForMathlib OAI`. It reused the completed build, freshly ran
consumers/exporters/axiom checks/comparisons/tests, and ended with the inherited
unchanged-input warm build. See [build reuse identity](evidence/module-final/accepted-25/build-reuse-identity.json),
[stage manifest](evidence/module-final/accepted-25/stages.json) and
[successful audit metrics](evidence/module-final/accepted-25/checks-acceptance.json).
All **1635 recorded inputs** matched at completion. Reports/evidence were added
afterward; this is not a claim that the initial failed run passed.

| Check | Result |
| --- | --- |
| Actual ForMathlib/OAI downstream build | 9186 jobs, pass |
| Original 3902 records plus explicit 45 additions | pass with raw differences retained |
| Complete 3947 records vs accepted 131-module branch | 8 bound type-expression pairs; zero missing/added/new-owner changes |
| Ordinary modern producer records | 661 records; 9 bound type-expression pairs; zero missing/added/relocated |
| Exact old types used with actual new declarations | all 9 pass, kernel-checked |
| Actual old helper type/value pairs under fresh names | 25 kernel-checked |
| Attributes and directed rewrite/simp | pass for all 9; simp records use of the actual equation |
| Concrete rfl/rw/simp and inverse consumers | pass |
| Audited axiom bound and source/comparator regressions | pass; propext, Classical.choice, Quot.sound only |

The original snapshots, `compare_types.py`, additional-type expectations, pins
and exact previous `stalkMap.eq_1` policy/DAG/witness remain unchanged. Its old
acceptance function is unchanged; composition keeps the older raw single delta
alongside this batch's explicit pairs. No baseline was refreshed.

## Finite representation evidence

The [finite policy](../experiments/kl-for-mathlib/module-final-compat.json) binds
Lean 4.34.1 commit `5045d0056413266e57c625dcd7c365b10e377c52`, Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`, complete old/new records (including
kinds, universes and owners), actual old and current expression DAG hashes,
old attributes and both consumer source hashes. It accepts exactly these
complete-view types, with one additional ordinary-view type:

- `OAI.KLInvariance.Dihedral.pairMatrix.eq_1`
- `OAI.KLInvariance.FiniteCharacterLocalization.diagonal.eq_1`
- `OAI.KLInvariance.MomentGraph.splitEdge.eq_1`
- `OAI.KLInvariance.MomentGraph.splitVertex.eq_1`
- `OAI.KLInvariance.ReflectionFrobenius.crossPair.eq_1`
- `OAI.KLInvariance.ReflectionSchedules.momentFunctional.eq_1`
- `OAI.KLInvariance.TitsSpace.Represents.extendedAction_eq`
- `OAI.KLInvariance.TitsSpace.height.eq_1`
- Ordinary view additionally: `OAI.KLInvariance.TitsSpace.simplePositive.eq_1`.

[`ModernFinalCompat.lean`](../experiments/kl-for-mathlib/ModernFinalCompat.lean)
uses ordinary modern imports, never `import all`. It reconstructs actual old
helper type/value declarations under fresh names, checks actual old/new types,
checks the actual new type against its stored exact expression, and kernel-checks
the actual new named declaration at the old type. It checks axiom closures,
old defeq/backward_defeq attributes and a Nat/Bool negative control. Directed
rewrite and simp use each actual equation; concrete vertex/edge inverse,
crossPair, diagonal and momentFunctional consumers also check rfl/rw/simp.
Fresh names are necessary: crossPair's old `_proof_1` had an instance type while
the new same-spelled helper has an additive-law type. Existing names cannot be
assumed to identify the old auxiliary value.

The complete and ordinary `extendedAction_eq` fingerprints differ from each
other, but both were already separately bound before full validation. A DAG
probe identifies the ordinary constant reference versus complete proof-proposition
serialization of its `_proof_1`. The exact actual type expressions agree across
the two live environments; the complete-context historical/kernel/rewrite/simp
control also passes. No serializer or proof-alias allowlist was changed to erase
this distinction. Raw hashes are not claims of logical inequivalence, and these
specific results grant no global definitional-equality waiver.

Historical owner metadata requires a different comparison context: the original
3902 declarations have their original OAI owners, whereas the already accepted
semantic port has transported them. The fix verifies **every one of the current
3947 owners** against the immutable accepted 131-module export, then verifies the
exact preexisting historical transport count and derives only the historical old
records of the same eight type pairs. The original raw `relocated=3902` is
retained. New candidate owner changes still fail. Tests reject a changed current
owner, changed historical record and wrong transport count. The baseline is the
accepted branch checkpoint 0917d25, not a claim that main already contains it.

## Rejected larger scope and decisions still open

The initial 95-module candidate excluded Structure's 35-module closure. Its 68
ForMathlib roots compiled, but a 2737-record regional audit found eight missing
old matcher names and one added name, plus nine type-expression differences.
Ordinary modern name resolution confirmed all eight old matcher names unavailable.
After restoring the six affected producers and their closure, the retained region
has zero name or owner deltas and the eight complete type pairs above. The
restored 105-module closure includes all 35 Structure dependents; these counts
must not be added. No production source directly references `.match_N`, but a
legacy control resolves all eight old names, and an extracted real CoefficientChange
modern producer breaks the old helper name in both legacy and modern clients.
The public ext theorem itself remains available.

[Interface decision material](module-interface-decisions.md) records exact names,
closure, actual access/use controls and options. Small proof-matcher compatibility
controls recover an old name through an explicit public definition, but this has
not validated all eight real helpers, ownership, duplicate serialization or the
new LocalCover helper record. No such compatibility definition or owner-policy
change was introduced into production.

The extracted actual Structure definitions demonstrate that inlining its two
quotient expressions can retain private encapsulation and vertex/upper/lower rfl
controls. Full real Structure migration is still a separate trial. It needs only
four legacy prerequisites: Cover.Local, Sheaf.Iso, Sheaf.BaseChange and Structure;
LocalCover's matcher boundary is on that path. At this evidence checkpoint,
production Structure is unchanged. No claim is made that 105 modules are migrated
or that the full Structure closure passed. Follow-up local evidence will be
recorded separately without altering this completed batch's source identity.

## Reproduction, failures and cost

In the initialized repository:

```sh
source scripts/env.sh
python3 scripts/recorded_run.py results/module-final-replay/all.log bash scripts/check.sh
# Reuse ready compiled artifacts without recompiling the library:
python3 scripts/recorded_run.py results/module-final-replay/checks.log bash scripts/check.sh warm
```

Use fresh output paths; the recorder refuses to overwrite identities. New machines
use `scripts/setup.sh` and its official cache path. Fresh initialization was not
run or measured here. Pins and a clean Mathlib checkout were verified. No dependency
upgrade or full Mathlib source compilation occurred. Focused checks are
`lake env lean ModernFinalCompat.lean`, `python3 test_module_final.py` and the
`module_final.py --compare-full/--compare-public` entrypoints with actual exports.
Comparing frozen exports alone is replay, not a fresh historical elaboration.

| Actual operation | Wall seconds | Outcome |
| --- | ---: | --- |
| 95-candidate / 68 ForMathlib roots build | 220.251 | build pass, later audit rejected names |
| Candidate regional export | 12.409 | retained raw failures |
| Restored bounded library build | 164.092 | pass |
| Old source/type capture | 135.160 | pass; initial value getter later corrected |
| Actual old helper value capture | 61.399 | pass |
| Old attribute controls | 96.246 | pass; output recovered from retained logs |
| Real full library build | 1786.104 | pass |
| Initial integration (37 stages) | 1984.066 | stopped at acceptance wiring error |
| Targeted historical wiring correction checks | 66.551 | pass |
| Final 59-stage audit, no library recompilation | 356.015 | pass |

The final audit measured 284.784 s child user CPU, 95.218 s system CPU and
7,331,908 KiB maximum child RSS. The original library build measured 2044.093 s
user and 104.828 s system CPU. UpperSections' Lake job was 1060 s; job queue/lock
times must not be summed. This is actual integration work with reused tooling,
not a controlled speed comparison. Child RSS is not total concurrent memory.
Token telemetry is unavailable; these local results make no GitHub CI claim.

Retained failed probes include incorrect import-all/non-module combinations,
fixture universe assumptions, a conditional simp rule needing its actual hypothesis,
and a rejection-message prefix regression. `ConstantInfo.value?` excludes theorem
values unless allowOpaque is true; the initial missing-value diagnosis was
corrected, not treated as an API failure. Attribute output initially shared a JSON
stem with measurement metadata; actual attributes were recovered from the nine
successful source log lines, stored distinctly and checked live. Early source
capture variants were reconstructed byte-for-byte and verified against their
recorded input hashes. Initial inefficient preparation was interrupted before
compilation; its preparation CPU/wall was not separately measured. The final
header/body source guard rejects unrecorded edits. All failures remain distinct
from successful acceptance; no proof was rewritten to chase a fingerprint.

## Follow-up: real Structure four-module trial (not delivered)

After freezing and archiving the accepted batch, a controlled temporary migration
of Cover.Local, Sheaf.Iso, Sheaf.BaseChange and Sheaf.Structure compiled the **full
real modules**, including all Structure proofs. Only the two private quotient
calls in structureSheaf were inlined; the private quotientLinear declaration
remained unchanged. Other changes were module/public/expose transport. No public
matcher compatibility definition, owner exception or type exception was added.

The ordinary modern consumer imported the real Structure producer and Lean,
without import-all. It reconstructed 20 actual old helper type/value pairs
(including the private computational quotient and old LocalCover matcher), then
kernel-checked actual new declarations at **135 historical types**, with exact
universe parameters, old equation attributes, definitional equality and three-axiom
closures. A legacy preflight checked all 136 old names/types. The sole unavailable
modern name was the known `LocalCover.splitEquiv.match_3`. Definition bodies of
vertex/upper/lower passed rfl; vertex and base-change equivalence controls passed
rfl/rw/simp. The actual old quotient and old LocalCover matcher definitions are
valid under fresh audit names in the new ordinary environment; that does not
publish their historical names or solve production ownership/integration.

The same regional exporter before/after reported **198/198 records**, no type,
universe, kind or owner differences, exactly one missing match_3 and one added
match_6. Its raw comparison therefore remains **failed**, not waived. The
orchestration command's zero exit means that compilation/consumer probes/restoration
succeeded, not that strict compatibility was accepted. See
[trial classification](evidence/module-final/structure/trial-classification.json).
Full OAI/downstream regression under this known-incompatible four-module candidate
was not run; it cannot be delivered while that old name is unavailable.

All four production files were restored exactly to accepted checkpoint a95504e.
The bounded rebuild restored **byte-identical four olean files**, and
`lake --no-build build ForMathlib OAI` then passed. All 261 production files and
all 1635 inputs of the successful 25-module audit still match; see
[restoration](evidence/module-final/structure/restoration.json) and
[final source check](evidence/module-final/structure/final-source-check.json).
No full project rebuild was repeated. The delivered modern count remains 156,
not 160. Structure is a locally supported inline candidate, not an accepted module.

Measured local trial costs: four-producer build 30.728 s, ordinary consumer 7.866 s,
regional export 13.276 s, restore build 35.603 s; orchestration including restoration
88.790 s. Final no-build readiness check 6.062 s. Failed preflight fixtures retain
syntax/type-inference mistakes and a dependent-projection rewrite attempt that
also fails on the original legacy source. The final controls use nondependent
vertex equations for rw/simp while retaining upper/lower rfl checks. Those failed
probes are not migration failures and were not fixed by editing production proofs.
