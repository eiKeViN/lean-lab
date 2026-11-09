# 求解环境与数学约定

这是一个独立的自然语言到 Lean 的形式化任务。题目中的有限 POVM 是一族正半定 Hermitian 矩阵，和为单位矩阵。密度矩阵为正半定、迹为 1 的矩阵；Born 概率取 Tr(Eₓρ) 的实数值。Kraus 算子的输入坐标对应矩阵列，输出坐标对应矩阵行。二元判决中结果 0 表示接受。

项目位置：`/workspace/lean-lab-measurement/experiments/measurement-api`。固定 Lean 4.35.0，mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679，Physlib c5a908ba7a1ee474063626bdf0470af006f9812e。环境和依赖已准备完成。

按分配的资源范围自主寻找已有定义、定理和数学事实：

- 原有资源：`vendor/physlib/QuantumInfo/`、`.lake/packages/mathlib/Mathlib/`，以及已有 PMF 桥 `vendor/bridge/PMFBridgeDraft/Bridge.lean`。正常入口是 `QuantumInfo.Measurements.POVM`，其他模块可以按需导入。
- 获得扩展库的任务还可以使用 `import MeasurementAPI` 并查阅 `MeasurementAPI/` 下全部库源码和文档注释。该入口仍使用 Physlib 原有的对象类型。
- 请不要读取设计讨论、Git 历史、`Contracts/`、`Comparison/`、`evidence/`、其他实验、其他求解者的文件或记录。分配的题目、当前说明和获准的库源码足够开始工作。不要使用个人记忆/房间历史来取得本任务之外的上下文。

可以执行 `rg`、阅读文件、在自己的解答文件中使用 `#check` 等正常探索。不要修改库、依赖、工具链或配置，也不要调用其他代理、联网求解、推送或提交。

在分配的单个 `.lean` 文件中写定义与定理，使用自己的命名空间；导出的结果应可供复用。可以采用项目通常的模块格式：文件首行为 `module`，公开依赖使用 `public import`，导入后写 `@[expose] public section`。题目的具体 Lean 陈述和命名由你自行决定。这一模块说明在首轮观察到导入可见性问题后补充；首轮说明的原文保留在协议提交 321c723。

所有 Lean 调用通过记录器进行，避免丢失中间失败与源文件版本：

```bash
python3 Usability/attempt.py --case 分配编号
python3 Usability/attempt.py --case 分配编号 --audit --decl 你的命名空间.结果名
```

若后续任务明确指定 round2，给上述命令添加 `--round round2`。首轮说明与记录仍保留原版本。

要测试一个检查命令或不同证明，也修改同一个解答文件并调用记录器。每次记录器保留源文件、完整编译输出、退出码和耗时；每个 Lean 进程最多运行 120 秒，使用一个线程。若修改证明预算等编译选项，请在事实记录中说明。

不要引入 `sorry`、自定义公理或绕过内核的断言。最终对主要定义/定理执行 audit，并提供所有结果的名称。如果某部分未完成，保留可编译的已完成部分和最后的失败记录，清楚说明缺少的结论。

从收到任务起最多工作 25 分钟。请在自己的事实记录 Markdown 中简要记下：查过哪些资源、尝试了哪些公开操作、遇到的具体障碍、是否得到外部帮助、最后完成了什么。无需给出私有思考过程。优先完成题目，不把额外封装或代码行数当作目标。
