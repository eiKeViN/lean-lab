# E4Revisit：明确标记的后续迭代

本次属于 round2 后续迭代，不是新的独立首轮试验。我保留首轮 E4New 的经历，并阅读了自己的 `E4New.lean` 和 `E4New.md`；没有修改这两个文件。任务指定当前库版本为 `c2d87ebfa012f98ef11d57f99b51d683d9e828c0`。

## 完成范围与声明

E4 全部三项均完成，保持对任意有限系统和标签类型、任意满足原题归一化条件的矩阵及复振幅成立，没有增加非空性等数学假设。

命名空间为 `E4Revisit`，所有 12 个声明均经过最终 audit：

- 细标签族：`fineKraus`。
- 效果计算与求和：`fine_effect`、`sum_fine_effect`。
- 归一化：`fine_normalized`。
- POVM 构造：`originalPOVM`、`finePOVM`。
- POVM 效果公式：`originalPOVM_effect`、`finePOVM_effect`。
- 遗忘细标签：`coarsegrain_finePOVM`。
- 任意复矩阵上的分支计算与非选择输出相等：`fine_branch`、`nonselective_eq`。
- 由归一化 Kraus 族构造的 CPTP 信道相等：`channel_eq`。

## 实际复用与整理

重新阅读 `Usability/LEARNER.md`、`Usability/problems/E4.md` 后，使用 `rg --files`、`cat` 阅读当前 `MeasurementAPI/Kraus.lean`、`MeasurementAPI/POVM.lean`、`MeasurementAPI/Marginals.lean` 和 `MeasurementAPI.lean`，以及自己首轮的两个提交文件。未读取其他求解者文件、设计讨论、Git 历史、其他实验或个人历史。

复用了自己首轮的矩阵标量计算、归一化、POVM 构造、任意矩阵的输出求和及 CPTP 外延证明。保持使用既有 `POVM.ofKraus`、`POVM.ext`、`CPTPMap.of_kraus_CPTPMap` 和 `CPTPMap.ext`。

实际发生的库接口改善是：当前入口导出的 `POVM.coarsegrain_fst_mats` 直接给出产品标签的第一边缘效果。`coarsegrain_finePOVM` 使用该公式后，只需投影为矩阵并调用 `sum_fine_effect`；不再在本提交中展开筛选求和及逐项使用 `Finset.sum_eq_single`。

另行整理了实例作用域：删除首轮提交中不必要的 `DecidableEq b`、`DecidableEq I`、`DecidableEq J`；辅助定理分别只保留实际使用的有限类型实例。主 POVM 与 CPTP 结论保留有限 `a b I J` 和 `DecidableEq a`。`nonselective_eq` 只要求有限 `a I J`，无需在该代数结论中要求有限 `b`。这些整理没有增加题目假设。

## 验证、障碍与帮助

全部 Lean 调用使用 `python3 Usability/attempt.py --round round2 --case E4Revisit`，没有修改预算、配置、库或依赖。

- Attempt001：整份文件编译成功，Lean 退出码 0，耗时 2.974 秒，没有警告。
- Attempt002：使用 `--audit` 和 12 个 `--decl E4Revisit.…`；状态 `verified`，Lean 退出码 0，耗时 3.048 秒。全部声明仅依赖标准公理 `propext`、`Classical.choice`、`Quot.sound`，没有 `sorry` 或自定义公理。

记录目录为 `results/usability/round2/E4Revisit/`；最终审计证据是 `Attempt002.log`、`Attempt002.json`，并保存源文件快照。本次没有失败尝试，也没有剩余阻塞。

本次一次编译后通过审计，但我已熟悉题目并实际复用了首轮代码；不将耗时或尝试次数的变化归因于库。可以直接观察到的改善仅是边缘效果接口替代了本地筛选求和证明，以及实例作用域整理。

没有联网、调用其他代理、请求外部帮助、提交或推送；除本次 `E4Revisit.lean`、`E4Revisit.md` 及记录器自行生成的记录外，没有修改文件。
