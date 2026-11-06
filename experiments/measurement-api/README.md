# 有限测量接口：可编译的 Physlib 实验

本实验将有限 POVM 的构造、信道拉回和结果合并接成一条使用链，并用 Physlib 的**完整假设检验文件**检验迁移。核心结果是：调用者提供测试效果及其数学条件，库提供测量对象、经典输出公式和组合律；过程语义继续由选定的 Kraus 实现承担。

实验使用固定 Lean **4.35.0**、mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`、Physlib `c5a908ba7a1ee474063626bdf0470af006f9812e`，并复用 lean-lab 既有有限 PMF 桥。所有环境和产物由本目录独立管理。

## 已实现的接口

主入口：`import MeasurementAPI`。

| 文件 | 解决的问题 | 直接复用 |
| --- | --- | --- |
| [POVM.lean](MeasurementAPI/POVM.lean) | 任意有限 POVM 的正幺搬运、Heisenberg 拉回、结果粗粒化；二元测试与输出公式 | Physlib `PUMap` 的映射类、`hermDual`、`exp_val_hermDual`；mathlib 纤维求和 |
| [Probability.lean](MeasurementAPI/Probability.lean) | `ProbDistribution.pushforward` 及恒等/复合/实数观察规则 | 既有 `Bridge.toPMF/ofPMF`；mathlib `PMF.map` |
| [Observations.lean](MeasurementAPI/Observations.lean) | 量子预处理、测量、经典重标记的完整观察等式 | 上述两层的组合律 |
| [BinaryChannel.lean](MeasurementAPI/BinaryChannel.lean) | 为两个输入态返回同一个二元 CPTP 信道和所需输出等式 | `POVM.measureDiscard`、硬币分布与期望值界 |
| [Kraus.lean](MeasurementAPI/Kraus.lean) | 从选定的归一化 Kraus 族提取 POVM，并证明分支迹等于结果概率 | 现有 PSD、HermitianMat 和矩阵迹循环规则 |
| [EffectBounds.lean](MeasurementAPI/EffectBounds.lean) | 一般效果和有限事件效果的单位算子上界 | mathlib 有序有限和与 POVM 归一化 |

例如，正幺映射 `F : PUMap b a ℂ` 已具有线性和保单位实例。`mapEffects` 的归一化证明直接写成：

```lean
normalized := by rw [← map_sum, P.normalized, map_one]
```

完整观察管线的契约是：

```lean
((P.pullback N).coarsegrain f).measure ρ =
  (P.measure (N ρ)).pushforward f
```

正幺/正保迹映射足以服务独立系统的概率观察；涉及辅助系统的物理操作时，调用者可使用已有 CPTP 对象的相应视图。接口没有添加新的全局类型类实例。

## 真实客户的前后对照

固定 Physlib 的 `QuantumInfo/ResourceTheory/HypothesisTesting.lean` 中，`OptimalHypothesisRate.Ref81Lem5` 原来局部构造 `{T,1−T}`，随后展开 `measure`、硬币分布和内积，得到 DPI 所需的二元信道。

本实验生成原文件的两个隔离版本：Before 保留原文；After 只增加一个导入并替换该局部证明块。整个文件的其他内容保持原文。After 的调用点为：

```lean
obtain ⟨Φ, hρ, hσ⟩ := POVM.binary_channel_for_pair
  T T.prop.right ρ σ p q
  (by simpa [p] using hT₂)
  (by dsimp only [q]; rw [← hT₁])
exact ⟨Φ, hρ.symm, hσ.symm⟩
```

两份**完整文件**均已编译；目标定理的打印签名和公理集合一致，证明预算沿用原文件。可查看 [精确差异](evidence/hypothesis.patch)、[共同签名](evidence/hypothesis-type.txt) 和 [验收记录](evidence/acceptance.json)。这是局部重复证明向库接口的迁移证据，不作为长期维护成本或性能提升的测量。

`binary` 的标签沿用 Physlib：**0 表示接受**。新接口仍返回 Physlib 原有的 `POVM`、`CPTPMap`、`ProbDistribution`。

## 组合体验与过程边界

[Pipeline.lean](Contracts/Pipeline.lean) 检验了信道拉回与经典结果合并相容、连续两次重标记、信道复合、接入 PMF 客户，以及非满射标签和零维载体的边界情况。

[ProcessSeparation.lean](Contracts/ProcessSeparation.lean) 给出完整 Lean 见证。对两个测量结果 i，取

\[
K_i=|i\rangle\langle i|,\qquad L_i=|0\rangle\langle i|.
\]

两个 Kraus 族都归一化，并产生相同的 POVM。`same_branch_trace` 还证明其结果迹对**所有输入矩阵**都相同。但输入 `|1⟩⟨1|` 经两个总信道分别变成 `|1⟩⟨1|` 和 `|0⟩⟨0|`；代码证明了总信道和输出态不相等。

因此 `ofKraus` 只提取所选实现的概率视图。Physlib 的 `measurementMap` 仍使用它原有的规范状态更新；不能由 POVM 相等自动替换过程。此次没有引入新的通用 instrument 结构。

## 复现和证据

在本目录运行：

```bash
bash scripts/setup.sh
bash scripts/check.sh
```

`setup.sh` 核对下载的 Lean 压缩包、取得锁定依赖，并只下载所需 mathlib 导入闭包的官方缓存。Physlib 作为固定源码库使用，本实验提供自己的 Lake 配置。环境不修改其他实验的工具链或缓存。

旧 PMF 桥使用旧模块格式。为接入新的 `module` 文件，本实验在 `vendor/bridge` 生成一份仅调整模块可见性的适配副本，原证明正文保持一致；[适配差异](evidence/bridge-module.patch) 和 [输入身份](evidence/comparison-sources.json) 均已保存。检查程序会核对这些已记录差异，避免静默刷新基线。

实际验收结果：

- 28 个 API 声明与 20 个命名使用契约完成类型/公理输出检查；另有匿名最小假设示例随文件编译。最初版本的 API 数为 26，独立练习前的基础检查增加了两条一般效果上界定理。
- 两个完整假设检验版本完成编译，目标定理签名和公理集合一致。
- 被检查声明仅依赖 `propext`、`Classical.choice`、`Quot.sound`；没有 `sorryAx` 或新增的其他公理项。
- 核对了 82 份固定 Physlib 源文件；本轮实际编译 55 个 Physlib 依赖模块，另编译原假设检验文件的两个独立版本。身份覆盖与编译覆盖分别记录。

完整日志保存在忽略目录 `results/`；Git 保留 [精简验收快照](evidence/acceptance.json)、[公开类型](evidence/public-types.txt)、[失败及修复记录](evidence/failures.json) 和来源清单。维护者有意更新代码与证据时，可使用 `scripts/check.sh --record`；它不跳过任何检查。

## 设计判断与范围

Lean-QEC 案例启发本轮把独立数学条件、保留结构的变换和标准库桥接做成公共能力。测量场景已拥有合适的 POVM/信道载体，因此本轮选择扩展它们。公共证明工作集中到映射类、有限和及观察公式；调用者继续提供 T 的选择、概率规格和物理实现等主动数据。

新增库代码与模块适配本身需要维护。编译中曾出现子类型概率转换超时、广泛 simp 递归、Hermitian 载体展开及状态/矩阵作用边界等具体问题，均有实际诊断与修复记录，没有通过提高证明预算或放宽公理检查来解决。

本轮验证范围是上述 Physlib 使用链；此前 QIT instrument 的依赖组合和反馈草案仍未在本实验验证。依赖维度、随机/连续结果、归一化后选择态及完整协议迁移也未纳入。依赖使用锁定的官方缓存，未独立重检所有依赖的内核证明。
