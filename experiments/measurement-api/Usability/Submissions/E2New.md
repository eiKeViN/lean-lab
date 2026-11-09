# E2New 事实记录

## 完成范围

已完成 E2 全题。`E2New.effect E w` 定义加权效果 `∑ x, w x • E.mats x`，只对各权重要求 `0 ≤ w x ∧ w x ≤ 1`，未要求权重和为 1。`E2New.decision E w hw` 是 `POVM (Fin 2) a`，结果 0 为接受。

导出声明：

- `E2New.effect`：加权效果的定义。
- `E2New.effect_bounds`：`0 ≤ effect E w ∧ effect E w ≤ 1`。
- `E2New.decision`：二元 POVM 的构造。
- `E2New.decision_zero`、`E2New.decision_one`：两个效果分别为加权效果与其补。
- `E2New.effect_expectation`：加权效果的 Born 期望等于原 POVM 结果概率的加权和。
- `E2New.decision_prob_zero`、`E2New.decision_prob_one`：两个结果的概率分别为该加权和及 1 减该和。

## 查阅资源与公开操作

1. 首先只阅读 `Usability/LEARNER.md` 与 `Usability/problems/E2.md`。
2. 阅读获准库中的 `MeasurementAPI.lean`、`MeasurementAPI/POVM.lean`、`MeasurementAPI/EffectBounds.lean`、`MeasurementAPI/BinaryChannel.lean`、`MeasurementAPI/Probability.lean`、`MeasurementAPI/Observations.lean`。
3. 阅读原库 `vendor/physlib/QuantumInfo/Measurements/POVM.lean` 的定义部分，以及 `vendor/physlib/QuantumInfo/States/Mixed/MState.lean` 的期望值接口。
4. 用 `rg` 搜索获准 Physlib/mathlib 源码中的标量乘法单调性、正性与期望值定理；读取 mathlib `Algebra/Order/Module/Defs.lean` 中 `smul_le_smul_of_nonneg_right` 的匹配上下文。一次搜索中指定的 `QuantumInfo/FiniteDimensional` 目录不存在，其余搜索结果正常。
5. 按运行环境要求读取环境运行技能并检查环境状态；未联网、未读取凭证、未请求其他代理或查询个人/房间历史。数学证明未得到外部帮助。
6. 只编辑自己的 `E2New.lean` 与本事实记录；全部 Lean 进程均由 `python3 Usability/attempt.py --case E2New` 启动。未修改库、配置、证明预算或编译选项，未提交或推送。

## 尝试与检查结果

- `results/usability/E2New/Attempt001.log`、`Attempt001.json`：完整解答首次编译成功，Lean exit=0，耗时 6.054 秒。
- `results/usability/E2New/Attempt002.log`、`Attempt002.json`：对上述 8 个声明执行 `--audit --decl ...`。Lean exit=0，但记录器状态为 `audit_rejected`；输出将标准 `Classical.choice` 缩写为 `choice`。
- 随后仅把源码中的 `open Classical BigOperators` 改为 `open BigOperators`，移除未使用的命名空间打开声明。
- `results/usability/E2New/Attempt003.log`、`Attempt003.json`：再次对同样 8 个声明执行审计，最终状态 `verified`，Lean exit=0，耗时 6.865 秒。每个声明的公理依赖均为 `[propext, Classical.choice, Quot.sound]`。

## 具体接口问题与剩余缺口

扩展库已有 `POVM.binary`、`POVM.binary_zero` 和 `POVM.measure_apply`，直接覆盖合法效果转二元 POVM 与概率观测。结果 1 的效果可展开 `POVM.binary` 后由 `simp` 证明；加权和期望可由 `MState.exp_val`、`inner_sum` 与实数内积的标量线性化简。

唯一遇到的检查障碍是审计器对全局打开 `Classical` 后缩写的公理名称判为拒绝；移除该打开声明后审计通过。没有未完成的数学结论、失败中的 Lean 证明或剩余阻塞。无 `sorry`、自定义公理或额外数学假设。
