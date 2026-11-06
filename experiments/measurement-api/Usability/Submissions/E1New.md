# E1New 事实记录

- 任务：E1，有限 POVM 的等价重命名；允许使用扩展库 MeasurementAPI。
- 完成文件：`Usability/Submissions/E1New.lean`。
- 完成范围：全部三部分；对任意有限坐标集、结果集及双射成立，没有添加非空性或其他数学假设。

## 已查阅资源与公开操作

- 先阅读 `Usability/LEARNER.md` 和 `Usability/problems/E1.md`。
- 使用 `rg` 搜索获准库中的重命名、等价和求和接口。
- 阅读 `MeasurementAPI.lean`、`MeasurementAPI/POVM.lean`、`MeasurementAPI/Probability.lean`、`MeasurementAPI/Observations.lean` 及原 `vendor/physlib/QuantumInfo/Measurements/POVM.lean`。
- 阅读 mathlib 的 `Mathlib/Algebra/BigOperators/Group/Finset/Defs.lean` 中 `Equiv.sum_comp` 对应源码。
- 按执行环境要求读取云环境运行说明并检查环境状态；没有进行网络操作。
- 仅在指定解答文件中写入 Lean 代码；所有 Lean 调用均通过指定记录器。

## 定义与结果

- `E1New.rename`：效果直接定义为 `E.mats (e.symm y)`；正性沿用原 POVM，归一化使用 `e.symm.sum_comp`。
- `E1New.rename_mats`：所要求的效果公式。
- `E1New.rename_probability`：对应结果的概率作为原 `ProbDistribution` 概率子类型元素相等。
- `E1New.rename_inverse`：沿逆双射再次重命名得到原 POVM。
- 概率证明使用 `POVM.measure_apply`，逆重命名证明使用 `POVM.ext`。

## 验证记录

1. `python3 Usability/attempt.py --case E1New`
   - `Attempt001`：compiled；Lean exit 0；2.563 秒。
   - 日志：`results/usability/E1New/Attempt001.log`。
2. `python3 Usability/attempt.py --case E1New --audit --decl E1New.rename --decl E1New.rename_mats --decl E1New.rename_probability --decl E1New.rename_inverse`
   - `Attempt002`：verified；Lean exit 0；2.656 秒。
   - 日志：`results/usability/E1New/Attempt002.log`。
   - 四项审计均仅报告标准依赖 `[propext, Classical.choice, Quot.sound]`；没有 `sorry` 或自定义公理。

## 障碍、帮助与余项

- 没有遇到编译失败或未解决的数学、接口问题。
- 查阅 mathlib 源码后确认了双射求和定理的名称和方向。
- 没有向其他代理或外部人员求助，没有联网求解，没有读取其他求解者文件或受限讨论资料。
- 无剩余缺口或阻碍。
