# E3Base 事实记录

- 任务：独立完成 E3；只使用原 Physlib/mathlib，允许但未使用 PMF 桥。
- 已阅读：`Usability/LEARNER.md`、`Usability/problems/E3.md`；原库 `QuantumInfo/Measurements/POVM.lean`、`ClassicalInfo/Distribution.lean`、`ClassicalInfo/Prob.lean`；mathlib `Algebra/BigOperators/Group/Finset/Basic.lean` 的有限纤维求和部分。通过 `rg` 搜索了上述获准库中的相关定义和定理。
- 环境：按照环境技能执行了一次只读状态检查；未联网、未读取个人/房间历史，未调用其他代理，未读取扩展库或其他求解者文件。
- 第一版公开操作：构造每个纤维的 Hermitian 矩阵和；用有限和非负性与 `Finset.sum_fiberwise` 给出 POVM 的证明；把原库 `measure` 的概率显式转为实数，记录其实部迹公式；用 `sum_inner` 和有限和三角不等式证明收缩。
- 所有 Lean 调用均使用 `python3 Usability/attempt.py --case E3Base`；编译选项未修改。
- Attempt001 失败：模块的 `public section` 使用了私有导入中的 `Fintype`。把入口改为 `public import QuantumInfo.Measurements.POVM`。
- Attempt002 编译成功（3.827 秒），完整证明均已完成。出现的警告只是部分定理自动携带了未使用的 `[DecidableEq X]`，属于题目允许的常规实例，不影响结果。
- Attempt003 最终审计成功（6.409 秒，Lean exit=0）；记录位于 `results/usability/E3Base/Attempt003.log`，对应源文件快照为 `results/usability/E3Base/Attempt003.lean`。审计了 `E3Base.coarse`、`E3Base.coarse_mats`、`E3Base.born`、`E3Base.born_eq_re_trace`、`E3Base.coarse_born`、`E3Base.abs_sum_fibers_le`、`E3Base.coarse_measure_l1_le`。全部只依赖标准公理 `[propext, Classical.choice, Quot.sound]`；没有 `sorry`、自定义公理或额外数学假设。
- 完成范围：`coarse` 构造题目规定的 POVM，`coarse_mats` 给出效果公式；`born` 直接使用原库 `POVM.measure` 的实数概率，`born_eq_inner` 和 `born_eq_re_trace` 连接 Born 公式；`coarse_born` 给出纤维概率和；`coarse_measure_l1_le` 完成任意两个密度矩阵的题目不等式。不要求标签映射满射，也不假设态满秩或可交换。
- 具体接口问题：首次编译使用普通 `import` 而后续声明处于 `public section`，导致 `Fintype` 只被私有导入；改成 `public import` 后解决。没有未解决的数学或接口障碍。
- 外部帮助：无其他求解者或代理帮助；只使用获准库的源码、注释和 Lean 编译反馈。
