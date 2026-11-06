# E2Base 事实记录

- 完成范围：练习 2 全部三部分。接受结果用 `Fin 2` 的 `0` 表示，拒绝结果用 `1` 表示；权重仅假设逐点位于 `[0,1]`，没有归一化或其他数学假设。
- 提交文件：`Usability/Submissions/E2Base.lean`。
- 定义：`E2Base.testEffect`、`E2Base.binary`。
- 定理：`E2Base.testEffect_bounds`、`E2Base.binary_zero`、`E2Base.binary_one`、`E2Base.accept_probability`、`E2Base.reject_probability`。

## 查阅资源与公开操作

1. 首先完整阅读 `Usability/LEARNER.md` 和 `Usability/problems/E2.md`。
2. 阅读获准原库 `vendor/physlib/QuantumInfo/Measurements/POVM.lean`，确认 `POVM` 的矩阵、正性、归一化字段和 `POVM.measure` 的实内积定义。
3. 阅读获准 PMF 桥 `vendor/bridge/PMFBridgeDraft/Bridge.lean`；最终证明没有使用该桥。
4. 在获准 `vendor/physlib/QuantumInfo/` 中用 `rg` 搜索状态、Hermitian 矩阵、正性及迹的接口；随后阅读 `ForMathlib/HermitianMat/Order.lean` 前 165 行、`ForMathlib/HermitianMat/Inner.lean` 前 215 行和 `ClassicalInfo/Distribution.lean` 前 240 行。
5. 在上述原库与 `.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/Basic.lean` 中搜索内积和求和接口。若干试探路径（`QuantumInfo/Finite/*.lean`、`QuantumInfo/Basic.lean`、`QuantumInfo/States/Mixed.lean`）不存在，`rg` 报告路径错误；没有读取任务禁止的资料。
6. 在唯一的 Lean 提交文件中一次写入全部证明，并用规定记录器编译；随后用同一记录器对全部七个声明审计。

## 验证结果

- `python3 Usability/attempt.py --case E2Base`：`Attempt001` 编译成功，Lean 退出码 0，8.035 秒。
- `python3 Usability/attempt.py --case E2Base --audit --decl E2Base.testEffect --decl E2Base.testEffect_bounds --decl E2Base.binary --decl E2Base.binary_zero --decl E2Base.binary_one --decl E2Base.accept_probability --decl E2Base.reject_probability`：`Attempt002` 审计成功，Lean 退出码 0，4.784 秒。
- 尝试记录、源码快照和完整输出：`results/usability/E2Base/`，主要日志为 `Attempt001.log` 和 `Attempt002.log`。
- 七个声明的公理依赖均仅为 `propext`、`Classical.choice`、`Quot.sound`；没有 `sorry` 或自定义公理。
- 唯一 Lean 警告是 `testEffect_bounds` 自动包含未用的 `[DecidableEq X]` 实例；该常规实例在题目许可范围内。
- 没有修改编译预算或其他选项，也没有改动库、依赖或配置。

## 具体接口与完成情况

- 原库提供 `HermitianMat` 的 Loewner 序与实数标量保序实例；使用 `smul_nonneg`、`smul_le_smul_of_nonneg_right` 和 `Finset.sum_le_sum` 即可证明效果的上下界。
- `POVM.measure` 的实数值定义可直接化为 Hermitian 矩阵内积；接受概率使用 `sum_inner` 和 `HermitianMat.inner_smul_left`。拒绝概率直接由二元分布归一化导出。
- 无未完成证明、无剩余数学或接口阻碍、无 Lean 失败记录。
- 未请求其他代理、未联网、未使用其他求解者解答或个人/房间历史，未获得额外帮助。
