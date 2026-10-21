# ForMathlib 候选层与 KL 项目布局（2026-10-21）

本轮从已独立审阅通过的 `2b5287954bd3c16015d9aab10dc3331d61065926`
出发。先已将这个原样检查点发布到
[`codex/kl-semantic-architecture`](https://github.com/eiKeViN/lean-lab/tree/codex/kl-semantic-architecture)，
远端回读 SHA 与上述提交完全一致。没有强推、PR 或合并 main。

后续整理位于独立实验 `experiments/kl-for-mathlib`；原始、signed-ranks、
kernel-transport 和 kl-architecture 四个实验及其脚本原样保留。当前内容先按
现有数学对象、接口和依赖组织；未来通用接口抽取不在本轮。

## 依据与判断边界

2026-10-21 实际读取的官方页面：

- [贡献范围与 AI 规范](https://leanprover-community.github.io/contribute/index.html)：
  研究数学可能在范围内，但接收还涉及维护及审稿专长，不能把所有数学都视为
  必然接收；新理论的适合程度仍需社区判断。Coxeter、Bott–Samelson、KL 的
  专业性本身不是排除理由。
- [审稿指南](https://leanprover-community.github.io/contribute/pr-review.html)：
  检查文档、位置、重复结果、导入负担、接口与库集成；编译通过不足以证明
  一个贡献已经准备好提交。
- [命名](https://leanprover-community.github.io/contribute/naming.html)和
  [风格](https://leanprover-community.github.io/contribute/style.html)：文件命名采用
  UpperCamelCase；后续上游整理仍需处理 namespace/声明名、模块文档、头部及
  合理导入。本轮不批量改声明名或 proof style 来冒充已达到贡献标准。

`ForMathlib` 单向依赖是本项目选择的架构目标，不是 Mathlib 指定的目录规范。
分类区分数学适合性、当前接口能否自成依赖层、是否已可提交。暂留项目也不表示每个文件都必须
新增接口才可上游化：有的只需现有 API 改接，有的可能需要未来接口整理；本轮
不为移动目录做这些改写。候选层不是
“可直接提交”的清单。官方 AI 规范涉及披露使用、贡献者本人理解及人工审阅；
本轮没有向 Mathlib 发 PR、GitHub 评论或 Zulip 消息。

编译依赖继续固定在 Lean 4.34.1（`5045d0056413266e57c625dcd7c365b10e377c52`）
和 Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`。pristine 34 个 blob
仍对应 upstream `adc7f1241b42e322a6451854ab7e4b4c146bf78a`，运输快照
`70211c3350c1f203aa8f52f1809e57d7ae93ba78`；精确跨度直接绑定
`kl-kernel-transport` 在 `7ddc53ba8a09ed902fefff86e67a87217518c1d4` 的源码。
指南是本轮读取的
现行页面；未把依赖升级成 Mathlib HEAD，也未做针对其 HEAD 的提交就绪验证。

## 当前分类：全库覆盖，不按学科黑名单

完整机器记录 `upstream-assessment.json` 逐项覆盖前一轮 193 个语义模块，
包含当前归属、源码正则提取的声明线索及原文件行号（不是完整全局声明导出）、分类依据和待整理事项；可读索引为
`CLASSIFICATION.md`。两个稳定 kernel 文件另外明确归为通用候选与兼容包装。

| 当前归属 | 内容与实际依据 | 保留的不确定性 |
| --- | --- | --- |
| `ForMathlib/{Algebra,LinearAlgebra,RingTheory,Order}` | 一般环/模/线性映射/对称代数、局部化、分次结构及数值恒等式。例如 `LinearDescent.descend` 只需交换环、满射线性映射和保核条件；`QuotientEdge.iso` 仅需线性等价及核对应；并不需要 graph 或 KL 对象。 | 一些结果很可能能改写为现有 Mathlib API 的直接使用；本轮没有逐条证明新颖性，也没有扩大假设或重写接口。 |
| `ForMathlib/GroupTheory/Coxeter` | `CoxeterSupport.reflectionAction`、Bruhat 关系与子词、抛物包含、实现和二面体根理论使用 Mathlib `CoxeterSystem`/`CoxeterMatrix` 的任意系统，而非一个固定例子。 | 与当前/未来 Coxeter API 的重复和命名整合仍需细查；这是研究数学候选，不是已获上游批准。 |
| `ForMathlib/Combinatorics/{DirectedPaths,Dihedral,MomentGraph}` | 有序路径/dispatch/transfer、整数 signed-count 模型及一般 `OrderedGraph`/`Sheaf`；Bruhat 适配显式独立。`Sheaf.ModelSum`/`ScaledImages` 仍使用已有图/sheaf 对象，没有新造类。 | 自定义表示与已有图、graded module API 的集成、哪些短数值辅助值得独立贡献，仍需后续评估。 |
| `ForMathlib/RepresentationTheory/{Hecke,KazhdanLusztig/Polynomials}` | 任意 Coxeter 系统上的 Hecke 算子、普通 R、等参数 KL 规范/构造/唯一性、路径与二面体公式；`NormalizedKL` 的参数是任意 `cs` 和多项式族，不是最终 invariance 模型。 | 成套新理论的维护/审稿成本较高；`Classical.epsilon` 选择与规范的组织、与库中同类结构的关系，未在本轮重设计。 |
| `ForMathlib/RepresentationTheory/BottSamelson/TitsWords` | 任意有限 Coxeter 数据的实 Tits 实现、word 坐标及基本构造，依赖只在候选层内。因此没有因 Bott–Samelson 专业性将其排除。 | 当前只实现特定的实 Tits 系数模型，并非一般 realization API；这不使数学无上游价值，但未来是否采用该接口尚待判断。 |
| `OAI/KL/{BottSamelson,Sheaves,Localization,Comparison,Invariance}` | 当前 stalk/kernel 构造消费旧 kernel 名包装；basis-specific `FreeSheaf`、`SectionDualityObligation`、根标签边界、scaled comparison 传播及最终有限情形的组合按此证明架构组织。保留现有依赖，不为搬目录抽取通用接口。 | 这些也是可能上游化的数学；留在这里表示当前组织依赖此应用接口，不表示该学科不适合 Mathlib。未来可研究一般 realization/sheaf/model bridge。 |
| 兼容与构建设施 | `OAI/KL/Compatibility/KernelTransport` 三个旧名字的包装；34 个原 KL import 入口和两个 kernel import 入口；两个聚合入口、验证器及 manifest。 | 它们是项目设施，不作为额外上游数学贡献计数。 |

当前实际文件证据（路径相对新实验）：

- `ForMathlib/LinearAlgebra/Quotient/Transport.lean`：`LinearDescent.descend`、
  `KLInvariance.QuotientEdge.iso`、`QuotientEdge.descend`。
- `ForMathlib/GroupTheory/Coxeter/Exchange.lean`：`CoxeterSupport.reflectionAction`；
  `.../Bruhat/Defs.lean`：`BruhatLE` 与 `Interval`。
- `ForMathlib/Combinatorics/MomentGraph/Sheaf/Basic.lean`：`OrderedGraph`、`Sheaf`；
  `.../Sheaf/Models.lean`：`ModelSum` 与 `ScaledImages`。
- `ForMathlib/RepresentationTheory/KazhdanLusztig/Polynomials/Normalized.lean`：
  `NormalizedKL`、`klFamilies`、`klPolynomial`。
- `ForMathlib/RepresentationTheory/KazhdanLusztig/Polynomials/IntervalTransport.lean`：
  `rankDifference_subinterval_lt`、`rTilde_transport_all`、`scaledKL_transport`；
  `ForMathlib/Combinatorics/MomentGraph/Bruhat/PlaneModel.lean`：
  `PlaneBasis.modelLabel`、`model_flabby`、`model_quotient`。
- `ForMathlib/RepresentationTheory/BottSamelson/TitsWords.lean`：
  `TitsSpace.SymmetricCoefficient`、`coefficientAction`、`simpleCoordinates`。
- `OAI/KL/Sheaves/FreeModel.lean:23,75`：`SectionDualityObligation`、`FreeSheaf`；
  `OAI/KL/BottSamelson/Stalks.lean:1100`：`bottHeadKernelEquiv`；
  `ForMathlib/RepresentationTheory/KazhdanLusztig/Polynomials/FiniteRankReduction.lean:16`：`FiniteIntervalModel`；
  `OAI/KL/Comparison/SuffixFreeness.lean:198`：`FreeSuffixes`。

这些引用可回溯 `MIGRATION.md` 的固定原源码跨度。本轮不独立认证 upstream 的
原数学证明；编译、类型、公理、迁移与分类依据是不同层次的证据。

## 目录与责任变化

```text
experiments/kl-for-mathlib/
  ForMathlib/
    Algebra/Polynomial/                 # 修正原 Data/Polynomial 归属
    Algebra/Module/, LinearAlgebra/     # 当前通用代数与线性工具
    GroupTheory/Coxeter/                # 包含研究领域扩展
    Combinatorics/                      # 路径、signed model、sheaf
    RepresentationTheory/             # Hecke、KL 多项式、Tits word
  OAI/KL/
    BottSamelson/, Sheaves/, Localization/, Comparison/, Invariance/
    Compatibility/KernelTransport.lean
  OAI/RepresentationTheory/KazhdanLusztig/*.lean  # 原 34 个入口包装
  ForMathlib.lean                       # 只导入候选层
  OAI/Architecture.lean                # 全实现聚合
```

- `Data/Polynomial` 改为 `ForMathlib/Algebra/Polynomial`，与固定 Mathlib 的
  `Algebra/Polynomial/Reverse.lean` 锚点一致；泛型线性泛点/避免引理移到
  `LinearAlgebra/Avoidance`，不因证明使用多项式就归入多项式 API。
- 将满射下降、商同构和诱导商映射的三个旧模块合为
  `LinearAlgebra/Quotient/Transport`；将同一 pair-projection 对象的
  Basic/Kernel/Lifting 合为 `LinearAlgebra/PairProjection`。按已有对象责任合并，
  不按行数阈值合并。
- 将 reflect evaluation 与 reciprocal rigidity 合为 `Polynomial/Reciprocal`。
  原 mixed scaled-comparison 的三个完整单元分别归入 `TransferEvaluation`、
  `Algebra/Order/Field/RealScaling`、`Polynomial/ScaledReciprocity`；
  没有拆证明或添加引理。
- 原 `Quotient/EdgeImage` 只有一般线性映射核在标量商下的饱和、单射与自由像
  结果，改名 `Quotient/KernelReduction`；实际无直接实现消费者，保留原导出，
  不虚构使用场景。
- 二面体 Hecke/KL 多项式桥接归到 `KazhdanLusztig/Polynomials/Dihedral`；
  word 文件命名为 `BottSamelson/TitsWords`，表明当前实现选择。
- 项目文件按现有责任命名：`SuffixFreeness`、`GraphEmbedding`、
  `TerminalImages`；一般 plane sheaf 模型与 finite-rank reduction 已归候选层。

当前 168 个候选实现、23 个项目数学实现和一个 kernel 包装，共 192 个 core
实现模块（前轮 195）。加 36 个兼容入口和两个聚合入口，共 230 个产品模块
（前轮也是 230）。525 个原单元不变；core 直接 import 边从 325 变为 326，
仅是记录，不作为整体复杂度或速度提升的证明。导入闭包与文件责任比行数更重要。

所有候选 imports 都指向候选层或 Mathlib；没有候选→项目反向边。
`ForMathlibChecks.lean` 还会实际导入完整候选聚合并检查环境中没有 `OAI.*`
模块导入。声明仍在兼容的 `OAI.*` namespace，不与模块导入归属混淆。

兼容范围明确：保留原 34 个 KL import 路径和两个 kernel import 路径；本轮
采用新的语义 import 路径。前轮 193 个语义路径在冻结的 `kl-architecture`
实验仍原样可用，新实验不额外创建 193 个空包装。声明名和类型继续要求完整
对照；依赖旧语义 import 路径的新消费者应按 `CLASSIFICATION.md` 更新 imports。

## 验证与缓存

原工具链、依赖清单与 Mathlib 缓存复用；Mathlib cache-only 预检已通过。
新逻辑模块路径导致本库需要真实重新 elaboration，不把旧 `.olean` 改名搬用。
此前实验及其缓存保留。本轮全库与主定理入口已编译成功（9155 jobs）；
随后 `--checks-only --refresh-reference` 的 22 个阶段全部通过。以下是新布局
实际执行结果，没有把前轮通过代替本轮验收。

比较器、31 个反例测试及类型规范化规则保持原样。`PublicTypes.lean` 仅将
所属模块枚举范围由 `OAI.*` 扩大至 `OAI.*` 与 `ForMathlib.*`；静态检查要求
它与前轮源码只相差这一行。参考快照全部声明记录保持不变，仅更新绑定的
导出器哈希，并用 warm 参考环境独立重导出核对。严格 theorem 序列化副本政策、空/截断导出拒绝、
固定覆盖和非空 private 改写拒绝都保留；没有放松比较政策或增加例外。

复现：

```bash
bash scripts/setup.sh
bash experiments/kl-for-mathlib/check.sh
```

只做结构检查：`bash experiments/kl-for-mathlib/check.sh --static`。
缓存齐备后可以使用 `--checks-only --refresh-reference`；参考未 warm 时默认
快照避免为比较而第二次构建整库。没有新增工作流、保护规则或环境设置。

按实际声明复核后，原 Invariance/Induction、Invariance/FiniteModel 和
Localization/PlaneModel 也移入候选层：它们当前已有任意 interval/order-iso、
finite-generator parabolic reduction 和 PlaneBasis sheaf adapter 的接口，
不需要新抽象。这个修正是逐源码判断，而非根据原文件名决定“专用”。
finite-rank reduction 指有限生成子集的抛物系统，不声称该抛物群有限。

### 已修复的集成问题与保留的整理边界

首次本库构建运行 1823.787 秒后在末端 `SuffixFreeness` 失败：拆分旧
ScaledComparison 的导入后，`Comparison.matrix_difference_single` 的原间接
依赖不再可见。该引理本体仍在完整迁移的 ScaledReciprocity 单元中；修复仅
增加一条直接 import，没有改证明、命题或比较器政策。长 stalk/pairing 已成功
构建，其产物随后复用，未从头重跑。

当前 `ScaledReciprocity` 的原始完整单元仍附带两个有限加权和差分引理
`matrix_difference_single` / `matrix_difference_le`；这是尚可细化的内容归属，
不是声称它们属于多项式对象。为保持本轮完整单元重放简单且不再扩张重组范围，
未新增 source-span 切片格式。未来可在完整声明边界移动这两个引理；不需要新
数学接口。候选状态不掩盖这项上游整理工作。

第二次增量构建还发现 `Invariance.Finite` 原来间接使用的 transfer-evaluation
引理不再可见，已对其实际使用的两个候选模块添加直接 imports，并检查拆出
全部九个辅助声明的使用点。另将 kernel/compatibility 测试的模块名预期随
迁移更新，仍精确断言完整本地模块集合，原行为 examples 原样保留。

公理审计后，固定覆盖要求曾正确拒绝只导出 787 项的旧模块选择器；漏掉的
是 ForMathlib 所属模块，不是降低覆盖标准即可接受的情况。已扩展枚举范围，
未改类型规范化、序列化副本严格比较、固定 3902 项、空/截断拒绝或 private
改写政策。最终验收状态以完成后的阶段记录为准。

## 最终执行结果

```bash
bash experiments/kl-for-mathlib/check.sh --refresh-reference
bash experiments/kl-for-mathlib/check.sh --checks-only --refresh-reference
```

第一条在修复 imports 后完成全库构建；其后发现并修正检查入口的模块名预期。
第二条在扩展导出器所属模块范围后完成最终全部验收。记录也保留此前失败，
不把失败阶段改写为通过。

| 检查 | 最终结果 |
| --- | --- |
| 原始身份与 pins、前四实验/脚本/provenance 冻结 | 通过 |
| 525 单元一一分配、34 文件 35871 非注释行覆盖 | 通过，未改变数学命题/证明正文 |
| 全库与主定理入口 | `lake build ForMathlib OAI` 成功，9155 jobs |
| 候选层、一般对象层、领域层独立导入 | 三个实际 Lean harness 全部通过；候选→项目边为 0 |
| kernel/兼容/边界行为 | 全部通过；kernel 模块身份断言按新路径精确更新 |
| 公理闭包 | 16 项通过；主定理恰为 propext、Classical.choice、Quot.sound |
| 公开声明 | 3902 → 3902，缺失/新增/规范化类型变化均为 0；3902 项模块归属改变 |
| 参考快照 | 同一更新后导出器独立重导出 warm 参考，核对通过 |
| 比较器反例 | 31 项通过；另有 8 个 theorem 记录变体、3 个不支持 definition 重复案例拒绝检查 |
| private 名审计 | 两边实际改写清单 []；未改名名字集合相同、并集1899；跨环境交集[] |
| warm repeat | 成功，4.426 秒 |

类型比较的数学规范化与前轮相同：忽略 binder 显示名/表达式 metadata，
仅将内核导入的内部 theorem proof 辅助按完整命题表示；公开 binder 隐显性、
常量、宇宙和表达式结构继续比较。不是逐项 raw serialization 相同或每项
isDefEq 证书。实际编译器 proof alias 数参考 141、新布局 150；序列化副本
各 1。无新增类型例外或允许公理。

最终验收各阶段实际 wall 秒（完整命令、CPU 时间和累计子进程 RSS 高水位
见 `reports/evidence/for-mathlib-acceptance-stages.json`）：

| 阶段 | Wall 秒 | 退出码 |
| --- | ---: | ---: |
| `frozen-tree` | 0.004 | 0 |
| `baseline-identity` | 0.358 | 0 |
| `source-transport` | 0.210 | 0 |
| `source-coverage` | 0.338 | 0 |
| `classification-and-boundaries` | 0.047 | 0 |
| `lean-version` | 0.767 | 0 |
| `mathlib-ready` | 3.207 | 0 |
| `oai-ready` | 4.409 | 0 |
| `ForMathlibChecks` | 4.285 | 0 |
| `ImportChecks` | 4.503 | 0 |
| `DomainImportChecks` | 4.141 | 0 |
| `KernelChecks` | 4.938 | 0 |
| `CompatChecks` | 4.672 | 0 |
| `BoundaryChecks` | 4.921 | 0 |
| `Audit` | 3.992 | 0 |
| `reference-ready` | 4.202 | 0 |
| `reference-types` | 11.128 | 0 |
| `reference-snapshot-check` | 2.622 | 0 |
| `migrated-types` | 11.131 | 0 |
| `type-comparison` | 2.530 | 0 |
| `comparator-tests` | 0.075 | 0 |
| `warm-build` | 4.426 | 0 |

完整构建成功阶段耗时 57.651 秒，复用前述本库产物；不称
为最终布局从零冷编译时间。初次本库构建 1823.787 秒在末端 import 缺失
处失败，随后一次增量构建 123.869 秒发现另一处 import 缺失。源码长模块
确实曾在初次构建编译，后续未重复：Lake 显示 stalk 153 秒、pairing 656 秒，
都包含编译锁排队。没有全量 Mathlib 源码构建、速度提升或统计显著性结论。

证据保存在 `reports/evidence/for-mathlib-*`，原始导出与完整运行日志保留在
忽略目录 `results/for-mathlib*`。正常 fresh worker 使用已绑定的参考快照，
无需为对照第二次构建整个参考库。没有新增环境设置、依赖安装、工作流或
保护规则；上述为本地云端验证，不是 GitHub CI 通过声明。

本轮分类与目录边界仍属于可继续审阅的判断；Mathlib HEAD 构建、Mathlib
全套 lint、逐引理查重及维护者接收未验证。前轮独立审阅不自动覆盖本轮新
目录、检查入口和模块枚举适配；本轮没有声称新的独立审阅已完成。
