# E4New 事实记录

- 完成范围：E4 全部三项。对任意有限类型 `a b I J`、任意矩阵族和复振幅证明；仅使用有限类型及可判定相等实例，没有增加非空性或其他数学假设。
- 解答文件：`Usability/Submissions/E4New.lean`。命名空间：`E4New`。
- 细标签族定义：`fineKraus`。
- 归一化结论：`fine_normalized`；辅助结果：`fine_effect`、`sum_fine_effect`。
- POVM 构造：`originalPOVM`、`finePOVM`；效果公式：`originalPOVM_effect`、`finePOVM_effect`；遗忘标签结论：`coarsegrain_finePOVM`。
- 非选择过程结论：`nonselective_eq`，输入是任意复矩阵；辅助结果：`fine_branch`。
- CPTP 信道结论：`channel_eq`，使用 Physlib 的 `CPTPMap.of_kraus_CPTPMap`。

## 实际查阅与操作

先阅读 `Usability/LEARNER.md` 和 `Usability/problems/E4.md`。之后使用 `rg`、`cat`、`sed` 查阅获准库：`MeasurementAPI.lean`、`MeasurementAPI/Kraus.lean`、`MeasurementAPI/POVM.lean`，Physlib 的 Channels 下 `Bundled.lean`、`MatrixMap.lean`，以及对 `CPTP.lean`、`Unbundled.lean` 的符号搜索；查阅 Physlib `ForMathlib/HermitianMat/Basic.lean`；搜索 mathlib 的矩阵标量乘法、共轭转置和有限和接口，并阅读 `Algebra/BigOperators/Group/Finset/Piecewise.lean` 的有限条件求和引理。

所有 Lean 调用均通过 `python3 Usability/attempt.py --case E4New`，未修改编译预算、库、工具链或配置。仅修改本提交的 `.lean`、`.md`；记录器自行生成其记录。没有联网，没有请求其他代理，没有读取其他求解者材料，没有提交或推送，没有得到外部帮助。

## 编译和具体障碍

- Attempt001：模块中的公开声明无法使用私有导入，改为 `public import MeasurementAPI`。
- Attempt002–006：修正标量乘法的交换次序；移除不存在的 `HermitianMat.mat_ite`，改用 `apply_ite`；CPTP 的底层矩阵映射通过 `change` 展开，再使用输出相等定理。遗忘标签时的嵌套筛选和未被尝试的 `sum_ite_eq'` 化简完成，最终显式使用 `Finset.sum_eq_single`。
- Attempt007：整份证明编译成功，Lean 退出码为 0，耗时 3.102 秒。
- Attempt008：审计的 Lean 编译成功，但记录器标记 `audit_rejected`。输出将标准公理 `Classical.choice` 因 `open Classical` 打印成 `choice`。移除无必要的 `open Classical` 后重新审计；没有改变证明或公理依赖。
- Attempt009：对以上全部 12 个定义和定理执行 `--audit --decl ...`，状态 **verified**，Lean 退出码为 0，耗时 3.151 秒。公理依赖均仅为 `propext`、`Classical.choice`、`Quot.sound`。没有 `sorry` 或自定义公理。

全部源文件快照、编译输出、退出码和耗时保存在 `results/usability/E4New/`。最终证据为 `Attempt009.log`、`Attempt009.json`；最后的失败记录为 `Attempt008.log`、`Attempt008.json`。剩余阻塞：无。编译仅有部分辅助定理的未使用节变量提示。
