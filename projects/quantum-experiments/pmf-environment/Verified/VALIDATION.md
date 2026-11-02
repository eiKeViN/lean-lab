# PMF bridge proof validation — 2026-11-01

> 发布复现说明（2026-11-02）：本页保留原实验运行记录。当前脚本以 `history/source-baselines.json` 核对随仓库发布的源码，不再要求私人转移包或未发布 Git 对象；完整旧包校验属于此前本机证据。当前运行与发布验收见 [history](../history/README.md)。

All six revised files compile, and the full original target chain is accepted
by Lean 4.35.0. The original 36 explicit declarations and their ambient variable
contexts are unchanged. All 36 transitive axiom closures contain only
`propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx` or newly introduced
axioms occur. Original snapshots remain byte-identical.

## Exact scope

- `Bridge`: finite `ProbDistribution α ≃ PMF α`, pointwise conversions,
  both round trips, injectivity, and real finite-sum observation of PMF bind.
  The latter requires only the source carrier finite, not the target.
- `Native` and `ViaPMF`: normalized bind, pointwise formulas, associativity,
  and channel composition/associativity; `Compare` proves both operations equal.
- `ChannelProduct`: the measure of the **actual Physlib `DMChannel.on_fin`**
  at a fixed input word equals the product of coordinate measures. Coordinate
  independence follows using mathlib `iIndepFun_pi`.
- `ChannelStatistics`: real finite-sum integral observation, a finite-bound
  `MemLp 2` certificate, and additive-score variance using mathlib
  `variance_sum_pi`. Both the explicit-MemLp and automatically certified
  finite-carrier statements pass.

The input word remains fixed. Output carries `Fintype`, `MeasurableSpace`, and
`MeasurableSingletonClass` where the measure consumers need them. No finite
input or nonempty output premise was added. The general upstream expectation
and Mixable APIs are untouched. This says nothing about unconditional
independence under correlated random input. No original target was weakened.

## Repairs and observed failures

1. B01: transfer the existing real normalization using nonnegativity and
   `ENNReal.ofReal_sum_of_nonneg`.
2. B02: use PMF pointwise finiteness, `ENNReal.toReal_sum`, and finite `tsum_coe`.
   A first rewrite with unconstrained `← tsum_fintype` failed instance inference;
   an explicitly typed finite-sum equality fixes it.
3. B03: `PMF.bind_apply`, finite tsum, finite sum toReal, and toReal multiplication.
4. N01/N02: exchange finite sums, distribute multiplication, and reuse native
   normalization and multiplication associativity. The native baseline is fully
   proved, not deliberately weakened.
5. The original variance proof failed to identify the function-level finite
   sum with `totalScore`. An explicit function-extensional equality now rewrites
   the score before the direct call to `variance_sum_pi`.

The first Bridge compile also found an uncached mathlib PMF import. The official
cache for Constructions and Integrals was fetched in the existing isolated
project; no dependency pins changed and no toolchain reinstallation occurred.
Lake emits advisory warnings about importing module-system libraries from these
legacy-style experiment files; builds pass and no admission warnings occur.
The namespace `PMFBridgeDraft` is retained to preserve the original declarations;
validated sources are the copies under `Verified/`, not the frozen originals.

## Reproduce and inspect

From `projects/quantum-experiments/pmf-environment`:

```bash
source env.sh
python3 verify-proofs.py
```

The script checks pins and unchanged upstream tracked files, validates declaration
contracts against the preserved originals, runs `lake build PMFBridgeDraft`,
then independently elaborates each of the six source files with
`lake env lean Verified/PMFBridgeDraft/<Name>.lean`. It runs
`lake env lean Verified/Audit.lean`, verifies coverage of all 36 declarations and
rejects any axiom outside the three standard ones. It also rechecks the original
archive and restored experiment hashes. It removes inherited LEAN_PATH for its
subprocesses so Lake selects its freshly built library rather than old manual
objects. Every command, exit code, log and source hash is retained per run.

Accepted run: `logs/proof/validation-20261101T143238801687Z/`.
All six file elaborations, full build, audit, and preservation checks exited 0.
`logs/proof/latest-validation.txt` points to the latest successful run.
`report.json` records all 36 axiom closures, source hashes, exact commands,
versions, and assertions. `axioms.log` also prints the elaborated public types.
Earlier failure logs remain in `logs/proof/`; native work log is
`logs/native-agent.log`. Caches and run results are local and ignored by Git.

Pins: Lean 4.35.0 (compiler `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`),
mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`,
Physlib `c5a908ba7a1ee474063626bdf0470af006f9812e`.

An independent agent repaired the native file and reviewed the original
five-file contracts and fixed-input/MemLp boundaries. Final automated contract
and axiom checks cover the later variance proof repair as well.

## Evidence limits

This establishes the stated propositions and bridge compatibility in the pinned
Lean environment. Standard Lean elaboration checks and transitive axiom audits
were run; a separate kernel replay of every imported dependency was not run.
There is no matched timing/maintenance experiment or evidence of net
simplification or universal methodological benefit. The native and transported
algebraic clients both compile, but no new native variance implementation was
constructed for a cost comparison. No remote push, merge, deployment, Alioth
modification, or changes outside the isolated quantum experiment were made.
