# KL 语义责任盘点与首个整理切片

本轮结论：采用 Mathlib 的对象/API 作为分类锚点，但不要把现有 34 个文件直接改成若干“层”。先抽出 `BottSamelson.lean` 中的三个核运输构造，形成可单独导入的线性等价扩展，保留所有旧名字、类型和导入入口。暂不从 signed-dihedral 再开一轮，也不把 moment-graph sheaf 改造成 Mathlib 的拓扑/站点层。

本报告是源码盘点和待执行设计，不是新 Lean 实现或新编译结果。

## 1. 工作状态、来源与检查范围

- 当前本地分支 `codex/kl-semantic-map`，起点 `7225842219ed3844b2fbd9cf3d95f9b65bec862c`；这是已完成 signed-ranks 轮的最终代码/报告。开始时工作树干净。保留原有报告及缓存，本轮只新增本报告。
- pristine 基线为 `experiments/kl`，对应已发布主线 `dc7adaa35047517a600a2b80ff5aefcf28eb905a`。本轮分析对象为 `experiments/kl-signed-ranks`；除 `DihedralIntervals.lean` 外，另外 33 个 KL 源文件与 pristine 一致。没有修改任何 Lean、配置、验证脚本或其他仓库。
- 锁定 Lean：`leanprover/lean4:v4.34.1`；Mathlib：`d13f23b723b8a846827a245b89c10fc7d3f11612`。直接读取本地该提交源码，没有拿最新版文档代替锁定源码。
- 本轮执行 `python3 scripts/verify.py` 成功：34 个基线 blob、工具链 pin、已存在依赖 checkout 的提交及 tracked 内容匹配。读取工具链文件及 Mathlib `git rev-parse HEAD`，结果与上述 pin 一致。
- 两个实验的 `Invariance.olean` 均存在；signed-ranks 的 `.lake/packages` 仍链接到 `../../kl/.lake/packages`，共享依赖，实验自身 build 目录独立。这里只确认文件/布局存在，没有新运行 Lean 或 warm build。
- 既有证据 `reports/evidence/signed-ranks-results.json` 记录：3897 个旧公开声明类型保留，新增两个 pair helper；八个审计目标的闭包均为 `propext`、`Classical.choice`、`Quot.sound`。这是上一轮结果，本轮未重测，不构成对原论文数学范围的独立认证。
- 已读 `AGENTS.md`：保留 pristine、实验单独固定版本、使用自有脚本、禁止运行保存的 upstream lakefile、避免无缓存 Mathlib 全量编译、各类验证分开报告。checkout 无 `.agents` 目录，`/workspace/.agents` 为空；没有发现适用于本轮的 checkout skill 指引。
- 阅读方法：提取全部 34 模块直接 imports、声明与 namespace 索引；逐项核查下表代表声明的签名、证明所用对象及实际调用点。调用检索包含点记法，例如 `hC.scaledImages`，不是只查全名字符串。没有穷举验证 Mathlib 中每个可能同义定理。

以下路径约定完整展开如下：

```
K = experiments/kl-signed-ranks/OAI/RepresentationTheory/KazhdanLusztig/
M = experiments/kl/.lake/packages/mathlib/Mathlib/
```

`K/File.lean:行号` 和 `M/路径:行号` 均指本轮读取的固定源码，不是拟建路径。表内声明名称均写出完整 namespace。

## 2. 全局语义责任与依赖方向

建议按“对象是谁、保证什么、服务谁”分类。下面是期望的职责方向，不声称现有 import 已实现这些边界：

```
Mathlib 对象与基础 API
  ├─ 本地通用补充：整数/有限计数、核与像运输、分次线性代数、实数级数/多项式刚性
  ├─ Coxeter/Bruhat/Hecke/KL 组合对象
  └─ 有序图上的模与分次 sheaf 接口
          ↓
Coxeter 实现、根与反射几何 + Bott–Samelson/边界模型及其桥接
          ↓
路径与反射次序、秩二计数、局部化与嵌入像比较
          ↓
Hilbert 比较传播、有限模型运输、组合不变性主定理
```

通用对象性质应只依赖其对象的 Mathlib API；具体坐标模型依赖基础对象；桥接定理明确连接模型与领域对象；应用消费桥接接口。无需为这个分类增加 typeclass。实现辅助如枚举、选基、有限性实例，应跟随真正消费它的构造，不能仅因证明短就移入“通用”目录。

全部 34 模块的责任覆盖如下。每行刻意记录交叉责任，不能据此整文件机械搬迁：

| 现模块 | 从声明识别的责任与混合点 |
| --- | --- |
| `Model` | `BruhatStep`/`BruhatLE`、区间与秩差；`NormalizedKL`/选定多项式族。组合对象和最终规范在同一入口。 |
| `Coxeter` | 在 Mathlib `CoxeterSystem` 上构造 `CoxeterSupport.simpleAction`、词作用与交换/反射支撑。不是新 Coxeter typeclass。 |
| `Bruhat` | 强 Bruhat 性质、区间有限性/简单反射升降与 R 递推准备。 |
| `Hecke` | Finsupp 表示中的 Hecke 算子、词、bar 和 R 值；表示实现与代数性质混合。 |
| `OrdinaryR` | Laurent 表达到普通多项式的桥接、R 递推与卷积。 |
| `CanonicalKL` | 通用低次截断 `CanonicalP.lowPart` 与具体 KL 递归构造/唯一性混合。 |
| `Dihedral` | 二面体词/区间及 KL 特例；开头 `intervalIso_restrict` 实际是一般区间运输。 |
| `Comparison` | 低次多项式倒数刚性与正 elementary transfer 的传播；两者都不需 Coxeter 参数。 |
| `ModuleAlgebra` | 素元/局部化成员判别、自由覆盖、分次投影、正理想、实值 Hilbert 和；包含多个一般代数责任。 |
| `GradedModules` | 与 Mathlib 分解兼容的分次 Nakayama、齐次生成/基、`ModuleData` 及子/商/核/像。 |
| `ReflectionPlane` | 任意域上的线性形式满射、两反射乘积的像与根平面恢复；签名无 Coxeter 数据。 |
| `Tits` | Bruhat 图适配、Tits/扩张/Cotangent 实现、根反射与抛物子群；一般非退化双线性扩张也埋在其中。 |
| `ReflectionSchedules` | 有限多项式避零辅助、根/平面与路径 dispatch 构造；数值辅助与领域调度混合。 |
| `Sheaves` | 有序图、顶点/边模及限制映射、sections/flabbiness/boundary 的领域无关 moment-graph 接口。 |
| `GradedSheaves` | 分次 sheaf 到非分次 sheaf 的桥接、图/同构/商边运输；另有一般 `EmbeddedModule` 缩放像辅助。 |
| `HilbertSeries` | 单项式级数、分次核/像的等价与维数、Hilbert 加法；不是只有 Hilbert 形式级数定义。 |
| `MinimalExtensions` | 分次覆盖、边界最小延拓、一般 sheaf 的积/拉回/下延拓与商边同构。 |
| `SheafMorphisms` | 开头实际上是 `Graded.NonnegativeBasis`/character，后有 Bruhat 边界 sheaf 与模型；文件名不足以描述责任。 |
| `Decomposition` | sheaf character 分解、一般 `PairProjection` 商模、二面体平面基、反射 Frobenius 构造。 |
| `Frobenius` | 对称代数的具体反射作用、固定环/trace/对偶，以及一般限制配对、twist/格的桥接。 |
| `BottSamelson` | 实际 word stalk/投影 sheaf 与升降短正合列；夹有一般 tensor 辅助、核运输、换系数/分次运输。 |
| `IntegralPairings` | 一般级数分子唯一性、积分支撑/对偶、具体 Bott 兼容/投影和完美配对。 |
| `BalancedPairings` | 一般下降、共轭像、伴随直和对偶；分次 sheaf image/split 与具体 Bott 伴随桥接。 |
| `Support` | 一般支撑/对偶与换系数等价，分次 sheaf 配对，以及 Bruhat/Bott 的应用。 |
| `CharacterReciprocity` | 一般 sheaf `LocalModels`/有限 `ModelSum`/`ScaledImages`，以及实际边界配对与 character 互反。 |
| `DyerPaths` | 一般有限和消去、character 互反的应用、秩二根序与 Dyer 路径多项式。 |
| `ReflectionOrders` | 一般 dispatch 的线性/列表性质、数值排序稳定性与根序路径应用。 |
| `DihedralIntervals` | 二面体词/结构 sheaf、一般插值/有限计数、signed 坐标模型、平面几何计数桥接；明显横跨责任。 |
| `PlaneLocalization` | 一般对称代数商等价、一般 local-model 分解、具体余陪集/平面局部化桥接。 |
| `EdgeLocalization` | 区间同构运送边/score/schedule、一般 sheaf 同构/配对拉回、具体局部交叉配对。 |
| `PositiveTransfer` | 一般分次像/Hilbert 递增界、具体局部交叉对称性与比较调度状态。 |
| `TerminalKernels` | 一般 sheaf 缩放像同构运输、平坦 base change 核像、标量商/分母成员判别；具体平面边界应用。 |
| `SimultaneousInvariance` | 上区间/图包含、自由后缀与缩放多项式倒数桥接，拼接有限情形不变性。 |
| `Invariance` | 小区间归纳运输、有限抛物模型及最终任意 Coxeter 系统的不变性。 |

实际 imports 的关键事实：`GradedSheaves` 不仅导入 `Sheaves`、`GradedModules`，还导入 `ReflectionSchedules`；后者导入 `Tits` 和 `ModuleAlgebra`，`Tits` 导入 `Bruhat`、`Dihedral`、`ReflectionPlane`、`Sheaves`。所以当前一般分次 sheaf 入口已经带入大量领域内容。

后半段实际是一条很长的链：`SheafMorphisms → Decomposition → Frobenius → BottSamelson → IntegralPairings → BalancedPairings → Support → CharacterReciprocity → DyerPaths → ReflectionOrders → DihedralIntervals → PlaneLocalization → EdgeLocalization → PositiveTransfer → TerminalKernels → SimultaneousInvariance → Invariance`（箭头表示左侧被右侧导入）。主定理的 import 闭包覆盖全部 34 个模块。整理应逐次切断不必要的领域依赖，不能只改文件夹名后宣称分层完成。

## 3. Mathlib 对照与代表声明归属

分类：**①** 已有可复用 API/可组合构件；**②** 对象确实一致，本地补的是专门结论或便利接口；**③** 只有组织惯例或相关数学主题相似，不能直接替换对象；**④** 当前 KL 或其具体模型的内容。②只表示在所检索/读取的 API 中未找到直接同型入口，不是全 Mathlib 缺失证明。一个声明可同时含①构件和②结论。

| 完整声明与现位置 | 拟归属、签名依据与实际消费者 | 固定 Mathlib 对照 / 分类 |
| --- | --- | --- |
| `OAI.KLInvariance.BruhatLE`，`K/Model.lean:18` | Coxeter 的强 Bruhat 关系；定义是长度严格增长的左反射步的 `ReflTransGen`。`Bruhat.lean:19` 的 `OAI.KLInvariance.bruhat_refl`、`:22` 的 `bruhat_trans` 直接消费。 | `M/GroupTheory/Coxeter/Basic.lean:157` 的 `CoxeterSystem`、`Length.lean:75` 的 `CoxeterSystem.length`、`Inversion.lean:66` 的 `CoxeterSystem.IsReflection` 为同一现成对象①；检索该 Coxeter 子树未见 Bruhat 名称。新关系/定理归对象扩展②，不能换成弱序或未经证明等价的 `Set.Icc`。 |
| `OAI.KLInvariance.NormalizedKL`，`K/Model.lean:55` | KL 规范接口：R 递推、P 次数界及真正区间上的互反；由 `klFamilies`/后续构造与唯一性使用。 | 使用 Mathlib `Polynomial.reflect`，`M/Algebra/Polynomial/Reverse.lean:88`①；整个 normalization 是本项目④，不能因为返回多项式就归通用 Polynomial。 |
| `OAI.KLInvariance.Comparison.low_degree_zero_of_eval_reciprocal`，`K/Comparison.lean:24` | 实多项式/评价刚性：`2 * natDegree < d`，在 `(0,1)` 满足倒数关系则为零。`:50` 的 `eq_of_eval_difference_reciprocal` 消费；后者由 `K/SimultaneousInvariance.lean:333` 消费。 | 同一 `Polynomial` 对象；`M/Algebra/Polynomial/Reverse.lean:95,190` 的 `coeff_reflect`、`eval₂_reflect_mul_pow` 已被证明体直接使用①；刚性结论是局部补充②。建议从 transfer 的状态传播责任分开。 |
| `OAI.KLInvariance.Graded.component`，`K/ModuleAlgebra.lean:280` | 分次模线性投影；只需内部 `Submodule` 分解，无图/根。实际用于 `K/HilbertSeries.lean:211,274`、`K/BottSamelson.lean:1389`。 | `M/Algebra/DirectSum/Decomposition.lean:261` 的 `DirectSum.decomposeLinearEquiv` 与 `M/Algebra/DirectSum/Module.lean:186` 的 `DirectSum.component`、子模 `subtype` 可组合得到同一投影①；尚未 Lean 检查替换后的 definitional behavior。 |
| `OAI.KLInvariance.Graded.ModuleData`，`K/GradedModules.lean:1051` | 有限、非负的内部 ℤ 分次模 bundle；字段含 `ModuleCat`、decomposition、graded scalar action、nonneg、finite；`K/GradedSheaves.lean:20` 的顶点/边字段直接使用。 | `M/Algebra/Module/GradedModule.lean` 文档和 `DirectSum.Decomposition`、`SetLike.GradedSMul` 是同一底层框架①。`ModuleData` 额外捆绑有限性/非负性，不等于 Mathlib `DirectSum.Gmodule`；归本地有限非负分次模接口②，不增新 class。 |
| `OAI.KLInvariance.Hilbert.value`，`K/ModuleAlgebra.lean:506` | `∑' n : ℤ, (finrank(piece … n):ℝ)*q^n`，是实数收敛/不等式所用的数值函数；同段 `pieces_eq_of_value_eq:530` 消费。 | `M/RingTheory/Polynomial/HilbertPoly.lean:117` 的 `Polynomial.hilbertPoly` 输入多项式并返回最终系数增长多项式，签名和意义不同③。归分次维数的实值生成函数，不直接重命名为 Mathlib hilbertPoly。 |
| `OAI.KLInvariance.ReflectionPlane.range_preReflection_product_sub_id`，`K/ReflectionPlane.lean:44` | 任意域/模/独立线性形式下，两 preReflection 乘积减 id 的 range 等于二根 span；`:68` 的 `range_reflection_product_sub_id` 消费，再供 `Tits.lean:2025` 平面恢复应用。 | `M/LinearAlgebra/Reflection.lean:71,101` 的 `Module.preReflection`、`Module.reflection` 正是同一对象①；range/span 结论②，适合 `OAI` 自有线性反射扩展，不应按 KL 应用身份固定在 KL 命名下。 |
| `OAI.KLInvariance.MomentGraph.Sheaf`，`K/Sheaves.lean:28` | 有序图顶点/边上的模及两条线性映射；`CompatibleOn`/`Flabby` 和 `GradedSheaf.forget` 消费。归 moment-graph sheaf 自有接口。 | `M/Algebra/Category/ModuleCat/Sheaf.lean:35` 的 `SheafOfModules` 需要带 Grothendieck topology 的范畴和环 sheaf；当前结构没有这些数据。只是 sheaf 组织相近③，不可直接改 namespace 声称对象兼容。 |
| `OAI.KLInvariance.kernelSourceEquiv`、`OAI.KLInvariance.kernelTargetEquiv`、`OAI.KLInvariance.kernelMixedEquiv`，`K/BottSamelson.lean:1551,1971,1999` | 核在源/靶等价和限制标量下的运输；签名无 Coxeter、sheaf、word。源版本用于 `TitsSpace.bottHeadKernelEquiv:1578`；mixed 用于 `bottHeadRightKernelEquiv:2045`；靶版本目前无调用者。 | `M/Algebra/Module/Submodule/Ker.lean:85,329` 的 `LinearMap.ker_comp`、`LinearEquiv.ker_comp`，`Submodule/Equiv.lean:37,57,77` 的 `LinearEquiv.ofEq`、`ofSubmodules`、`ofSubmodule'`，`Equiv/Basic.lean:48` 的 `restrictScalars` 是①；三个便利构造为②。适合 `LinearEquiv` 对象的本地扩展，首片详见下节。 |
| `OAI.ConjugateRange.conjugate`、`OAI.ConjugateRange.equiv`，`K/BalancedPairings.lean:980,999` | 线性自同态共轭及其 range 等价。外部真实消费者只有 `OAI.KLInvariance.TitsSpace.bottImageSectionWordEquiv`，`:1226–1232`；map_bijective 等为内部支撑。 | `M/Algebra/Module/Equiv/Basic.lean:725,728` 的 `LinearEquiv.conj`/`conj_apply` 已定义同一共轭（此处方向是 `e.symm.conj f`）①；range 等价可用 `Submodule/Map.lean:739` 的 `LinearEquiv.submoduleMap` 和 range_comp 组织②。只有一个外部消费者，暂不另造大型 conjugation 抽象。 |
| `OAI.KLInvariance.EmbeddedModule.scaled`、`OAI.KLInvariance.EmbeddedModule.map_scaled`，`K/GradedSheaves.lean:654,657` | 缩放嵌入子模及线性等价的 map；只有同段 `map_eq_scaled_iff:665` 调用 `map_scaled`，未找到外部消费者。 | `M/Algebra/Module/Submodule/Pointwise.lean:216` 的 `Submodule.mem_smul_pointwise_iff_exists` 已提供同一 scalar image 的成员接口①。应归一般 Submodule 责任，但当前无跨模块复用证据，不先扩成新库。 |
| `OAI.KLInvariance.MomentGraph.Sheaf.ScaledImages`、`OAI.KLInvariance.MomentGraph.Sheaf.scaledImages_iff`，`K/CharacterReciprocity.lean:443,450` | 上行核经 lower/upper 映射后的嵌入子模相等，不只是抽象同构；由 `prod_scaledImages:508`、`pi_scaledImages:526`、`K/TerminalKernels.lean:73` 消费。 | 其 submodule map/pointwise scalar 部分直接用上述 `Submodule.mem_smul_pointwise_iff_exists`①；图、Outgoing、upwardKernel 是本地 sheaf 对象，整体属于该对象接口②，不是通用线性映射一句话替代。 |
| `OAI.KLInvariance.MomentGraph.Sheaf.ModelSum.scaledImages`，`K/CharacterReciprocity.lean:548` | 沿本地有限模型和归纳传播性质；`K/TerminalKernels.lean:261` 的 `hC.scaledImages` 是真实应用，同时前一行 `j.symm.scaledImages` 调用 `OAI.KLInvariance.MomentGraph.Sheaf.Iso.scaledImages`（`:19`）。 | Mathlib 的积/线性等价组织可参考③，`ModelSum` 是本地归纳谓词，非现成 semisimple/category decomposition。模型传播与同构运输应分文件责任，但该主要组合应用只有一处，不伪造更多消费者。 |
| `OAI.KLInvariance.SymmetricPlaneIdeal.quotientEquiv`，`K/PlaneLocalization.lean:56` | 对任意子空间 `P`，`Sym(V)/⟨ι(P)⟩ ≃ₐ Sym(V/P)`；无平面维数或 Coxeter 假设。`:102` 的 ideal/ker 结论消费。 | `M/LinearAlgebra/SymmetricAlgebra/Basic.lean:99,113,120` 的 `SymmetricAlgebra.lift`、`lift_ι_apply`、`algHom_ext` 是同一对象①；完整商等价在读取的 Basic/Basis API 未见直接入口②。归 SymmetricAlgebra quotient 扩展；独立拆片比核运输更大。 |
| `OAI.KLInvariance.SignedDihedral.odd_add_abs`，`K/DihedralIntervals.lean:1455` | `Odd (i+z) ↔ Odd (i.natAbs+z.natAbs)`；只有整数/自然数奇偶。`odd_add_natAbs:1458`、`odd_sub_natAbs:1461`、`arrowAfter_next:1507` 等消费。 | 证明已直接用 `M/Algebra/Ring/Int/Parity.lean:75,91,94` 的 `Int.odd_add`、`natAbs_even`、`natAbs_odd` 及 `Nat.odd_add`①。可归本地 `Int` 奇偶桥接；不必为四个 rw 再造 tactic。 |
| `OAI.KLInvariance.SignedDihedral.eligible_ranks_card`，`K/DihedralIntervals.lean:1027` | 纯 ℕ/Finset 奇数等差子集计数；`countAfter_base:1541`、`positiveCount_formula:1634` 两个直接消费者。 | `M/Data/Finset/Card.lean:356` 的 `Finset.card_bij` 已在证明中使用①；具体 filter-card 结论②，责任归有限区间奇偶计数。没有 `Before`、根、反射假设。 |
| `OAI.KLInvariance.SignedDihedral.arrowAfter_pair`、`OAI.KLInvariance.SignedDihedral.arrowAfter_pair_below`，`K/DihedralIntervals.lean:1518,1533` | 对 `Before` 定义的 signed 模型归一化，直接/间接供 `countAfter_base`、`countAfter_pos_formula`、`countAfter_neg_formula` 三个真实消费者。 | 用 Int/Finset 算术①，但接口依赖具体 `arrowAfter`/`Before`，归带符号二面体模型④，不应为了可复用外观改成一般全序计数。 |
| `OAI.KLInvariance.TitsSpace.PlaneBasis.afterIndicator_same`、`OAI.KLInvariance.TitsSpace.PlaneBasis.laterCount_difference`，`K/DihedralIntervals.lean:1847,1954` | 前者把实际根/平面模型的 indicator 接到 signed 坐标；后者把数值计数结论运回几何并服务终端局部化。 | 依赖本地 `PositiveRoot`、`planeSubgroup`、平面基和 signed API；属表示桥接/领域应用④。不能随整数辅助一起搬入 `Int`。 |
| `OAI.KLInvariance.combinatorial_invariance`，`K/Invariance.lean:547` | 任意两 Coxeter 系统的 Bruhat 区间 order isomorphism 推出 KL 多项式相等；证明选有限模型并调用有限情形。 | 使用 Mathlib `CoxeterSystem`、`OrderIso`①，但结论和有限模型拼接是 KL 主定理④；位置保留稳定导出入口。 |

## 4. Signed-dihedral 已有成果应如何归属

这里至少有三种责任，不能整块迁往一个“通用数学”文件：

1. 一般整数/有限计数：`odd_add_abs` 及两个 natAbs 特例；`eligible_ranks_card`；`total_outgoing_count`；`positiveCount`/`positiveCount_formula` 的签名只含自然数、范围和奇偶。这些以后可按 `Int`、`Finset` 的 Mathlib 组织放入本地扩展，但本轮不移动。
2. 带符号二面体坐标模型：`Before`、`arrowAfter`、`countAfter`、pair helper 与 countAfter 三个客户端。`Before` 先分正/负块，不能当作 ℤ 普通线性序。pair API 的数学责任是“把同秩的两个坐标贡献归一化”。
3. 模型到几何的桥接及应用：`PlaneBasis.afterIndicator_same/next`、`laterCount_same/next/difference`；负责正根、平面群元素和坐标指标之间的对应。其调用方应消费 signed API，而不是重做端点判别。

现 pair 接口精确为：

```lean
theorem arrowAfter_pair {i j : ℤ} (hij : |i| < |j|) (r : ℕ) :
    arrowAfter i (i+j) r + arrowAfter i (i+j) (-r) =
      if i.natAbs < r ∧ Odd (i.natAbs+r) then
        if 0 < j then 1 + (if j.natAbs < r then 1 else 0)
        else (if r < j.natAbs then 1 else 0)
      else 0
```

这也说明分类限制：`r=0` 为零；符合奇偶条件的 `r=|j|` 在正 j 时为 1、负 j 时为 0；`countAfter` 仍含独立 singleton-top summand，客户端的 `c=j` 条件仍是字面等式。它不是一般 finite-sum 交换律。上一轮的 proof shortening 主要来自奇偶规范化；paired API 单独计算含 helper 后增加五个 proof-body 非空行。不能将这轮整理目标包装成既成性能收益。

## 5. 推荐的下一片：线性等价下的核运输

选择理由：三个构造的签名均已完整使用 Mathlib 的模/线性等价，当前却散落在 Bott 的两个领域段之间；抽出后可以独立阅读、导入、测试。两处真实应用分别是 ascent 与 descent 的 word-stalk 核识别。它不引入新数学对象，也不需先拆解几千行分次 sheaf 依赖。

其他两个有界候选暂缓：`ReflectionPlane` 的四个定理本来已经形成只 import Mathlib 的独立文件，本轮只改 namespace 的边际收益小；`ConjugateRange` 与 Mathlib conj 很贴近，但目前只有一个外部消费者，优先级低于两个真实核运输应用。ScaledImages/ModelSum 会碰到跨多个长链模块的对象定义，超出首片范围。

拟建下一轮独立实验 `experiments/kl-kernel-transport`，从本次起点的 signed-ranks 源码派生，保留 pristine 与 signed-ranks 及其验证器原样。待实施分支应另建，例如 `codex/kl-kernel-transport`；本轮尚未创建该实验/分支。

新模块职责与命名：

- `OAI/LinearAlgebra/KernelTransport.lean`：namespace `OAI.LinearEquiv`，提供 `kernelSourceEquiv`、`kernelTargetEquiv`、`kernelMixedEquiv`。参照 Mathlib 的对象 namespace `LinearEquiv`，保留 `OAI` 所有权；不修改依赖 checkout，不假装已经加入 Mathlib。
- `OAI/RepresentationTheory/KazhdanLusztig/KernelTransportCompat.lean`：只 import 新模块，保留三个 `OAI.KLInvariance.*` 旧定义为**显式原类型**的兼容 wrapper。不要使用 `abbrev` 替换现有 def；保持 reducibility/可展开行为，仍须下述检查。
- 原 `BottSamelson.lean` 增加 compat import，删除三个旧实现段；领域客户端暂时保留旧调用与类型表达式。原来只 import Bott 的消费者仍可使用全部旧 API。新一般消费者可只 import 通用模块。
- 第一片直接搬运三个实现体，不同时改写成 Mathlib 组合、不降低 Ring/Field 等假设、不加 simp 属性、不改两处 Bott 证明。这样文件责任迁移和证明重写可以分别评估。
- 通用模块第一片允许 `import Mathlib`，复用已缓存依赖。可能的精简 imports 是 `Mathlib.Algebra.Module.Submodule.Equiv`、`.Ker`、`.RestrictScalars` 与 `Mathlib.Algebra.Module.Equiv.Basic`，但本轮没有 Lean 验证其闭包；不能宣称该最小集合已可编译。不要在同片追求 import 最小化。

新 API 的签名（各类型参数/实例保持与原声明一致；下面列出完整环境，实施时复制原 binder 名称及 universe 参数）：

```lean
-- R : Type ur, [Ring R]
-- M : Type um, N : Type un, P : Type up
-- 各有 [AddCommGroup _]、[Module R _]
def OAI.LinearEquiv.kernelSourceEquiv
    (f : M →ₗ[R] P) (e : M ≃ₗ[R] N) :
    LinearMap.ker f ≃ₗ[R]
      LinearMap.ker (f.comp e.symm.toLinearMap)

def OAI.LinearEquiv.kernelTargetEquiv
    (f : M →ₗ[R] N) (e : N ≃ₗ[R] P) :
    LinearMap.ker f ≃ₗ[R]
      LinearMap.ker (e.toLinearMap.comp f)

-- k : Type uk, [Field k]; A : Type ua, [CommRing A], [Algebra k A]
-- M : Type um, N : Type un, P : Type up:
-- [AddCommGroup _], [Module k _], [Module A _], [IsScalarTower k A _]
-- Q : Type uq, [AddCommGroup Q], [Module k Q]
def OAI.LinearEquiv.kernelMixedEquiv
    (f : M →ₗ[A] P) (e : M ≃ₗ[A] N) (g : P ≃ₗ[k] Q) :
    LinearMap.ker f ≃ₗ[k] LinearMap.ker
      (g.toLinearMap.comp
        ((f.comp e.symm.toLinearMap).restrictScalars k))
```

上面为设计签名摘录，没有提供定义体，不能作为已通过 Lean 的独立文件。源版本元素送到 `e x.val`；靶版本保持 `x.val`；mixed 版本亦送到 `e x.val`，但结果等价是 k 线性的，不能误声称 A 线性。`kernelTargetEquiv` 当前没有真实消费者；此次仅随同一责任收拢，不能算成新增复用收益。

实际消费者及相邻验证点只有这些，不凑五个：

1. `OAI.KLInvariance.TitsSpace.bottHeadKernelEquiv`，`K/BottSamelson.lean:1578`，源运输调用在 `:1587`。
2. `OAI.KLInvariance.TitsSpace.bottHeadRightKernelEquiv`，同文件 `:2045`，mixed 调用在 `:2053`。
3. 后者的求值定理 `bottHeadRightKernelEquiv_eval:2056` 和齐次性定理 `bottHeadRightKernelEquiv_homogeneous:2084` 是 definitional behavior 的真实下游检查点，不是两个额外的直接 API 消费者。

## 6. 类型比较怎样处理移动和改名

现 `experiments/kl-signed-ranks/PublicTypes.lean` 遍历 imported moduleData，只收集模块名以 `OAI.RepresentationTheory.KazhdanLusztig.` 开头的非 private、非 `Name.isInternal` 常量；`validate.py` 要求源文件集恰为旧 34 个、只有 DihedralIntervals 改动，且类型覆盖模块集恰为这 34 个。表达式比较只去 metadata，保留 const 名、universe、binder 名/info 和全部表达式构造，使用 `ExprStructMap` 和两份 DAG 的共同精确结构 interning，不是仅比较 pretty-print 或哈希。

因此现 runner **不适合直接运行新迁移**：它应拒绝新增文件；新 `OAI.LinearAlgebra.*` 模块还会被 prefix 过滤漏掉。不能为过关删除 module coverage、允许旧名丢失、把比较改成仅 definitional equality，或任意 strip namespace。

下一片新建 experiment-owned runner，保留旧 runner 原样，明确修改规则：

1. 参考环境使用已验证的 signed-ranks，而不只是 pristine：3897 个原声明加两个 pair helper，共 3899 个既有公开 API 都需保留。pristine blob 检查继续独立执行。
2. 显式声明参考 34 模块和迁移后 36 模块清单。两份都完整导出；仅新环境增加 generic 与 compat 模块。按完整常量名合并比较，记录每个声明的 owner module。预期 owner 变更仅为三个旧核运输定义从 Bott 到 compat；其余旧声明归属不变。
3. 所有旧完整名字必须仍存在、universe 参数及 type DAG 精确相等。移动文件不会自动改变常量名；兼容 wrapper 必须保持原签名。如果失败，检查 elaboration/隐式参数，而不是放宽比较。
4. 新增公开名字清单精确为 `OAI.LinearEquiv.kernelSourceEquiv`、`OAI.LinearEquiv.kernelTargetEquiv`、`OAI.LinearEquiv.kernelMixedEquiv`，预期总公开数 3902；额外新增/丢失均失败。原 pair helper 必须仍保留。
5. 修改源 allowlist 精确为 Bott 文件；新增源 allowlist 精确为 generic 与 compat 两文件；其余 33 文件逐字节等于 signed-ranks，版本/manifest/Lake 配置亦保持。核对继承的 DihedralIntervals 仍完全等于 signed-ranks，不能退回 pristine 而丢失本轮前成果。
6. 单独导入通用模块和 compat 模块的两个 smoke harness 检查新旧 API 的值/逆映射投影与 wrapper 展开；模块清单确保它们不导入本地 Bott、Tits、sheaf 等领域模块。导入 Mathlib 本身的内容不算本地领域依赖。

未来如真要删除旧名字，必须先列出显式 migration map、所有调用者和兼容期限，并经另行设计决定。此次不删除，不需要对类型表达式做“重命名归一化”。类型比较也不覆盖 simp 属性、实例优先级、definitional 行为或所有证明体，因此这些要靠源码 diff、聚焦检查与 downstream build 补足。

## 7. 实施顺序与可证伪验收

下一实施轮按顺序执行；本轮未执行以下 Lean 阶段：

1. 固定 `7225842…` 参考源快照，创建独立实验/分支；运行 `scripts/verify.py`，逐字节核对参考、配置与允许差异。缓存先以 `lake --no-build build Mathlib` 和参考 `OAI` 的 readiness 检查确认；未就绪则报告成本，不默默开始冷构建。依赖共享，实验 build 只复制/reflink，禁止共享可写 OAI artifacts。
2. 仅作上述三个构造搬运、兼容 wrapper 与 import 改动。运行通用模块/compat 两个轻量 harness，分别验证 source、target、mixed 的值和逆映射，零核/全核示例及非平凡源坐标交换；mixed 另检 k-linear 标量行为。不要用一堆复制实现的测试冒充验证；优先检查消费者依赖的展开行为。
3. 顺序构建新模块、compat、Bott、完整 OAI 到 `Invariance`；运行 signed 边界 harness，保护继承的 pair 结果；导出并严格比较 3899 个旧类型和三个新增名字/owner 迁移清单。
4. 审计新三个 API、三个兼容入口、两个 Bott 核识别和主定理，要求每个请求目标恰有一次输出、闭包均不超出 `propext`、`Quot.sound`、`Classical.choice`。不接受 sorry、额外 axiom、unsafe bypass 或减弱假设。
5. 记录一次 warm build；只有需要讨论速度时才测同环境、同线程、顺序直接 elaboration 的成对时长。单独记录搬运引起的失效重编译成本；不与过去 warm readiness 的约三秒比较来声称加速。保存短报告与本地 commit，不自动 push/PR/merge。

验收能被以下失败明确推翻：

- 通用/compat 独立导入仍需要本地 Bott 或其领域链：责任边界未建立。
- 任一旧公开名/类型丢失或改变，或新增不在清单内的 API：兼容性未满足。
- 两个真实 Bott 消费者或相邻 eval/homogeneous 定理不能原样通过：行为保持未满足。
- 实现同时改了数学假设/证明策略或引入新对象/class：超出这片责任迁移范围。
- pristine 或 signed-ranks 任何已保留源/验证器改变：隔离失败。
- 没有完整 build/axiom/type/identity 输出：只能报告对应阶段未验证，不能称完成。

收益分开衡量：本片预期建立 API 可发现性与独立导入边界；不承诺证明变短。没有更换模块/核表示，不能声称获得新的表示无关性。没有自动化变更，不能声称 tactic 稳定性提升。若未来用 Mathlib 组合重写三个证明体，应另列一片并重新验证消费者的展开行为。

## 8. 本轮实际完成与限制

已完成：检查工作树/指引；保留全部前成果；读取 34 模块的导入/声明索引与上列代表源码及调用点；对照固定 Mathlib 的对象和具体 API；成功执行一次基线身份/依赖检查；给出签名级的小范围迁移和严格验证计划。

未执行：新实验创建、Lean 源码迁移、最小 imports 检验、新 proof/build/axiom/type dump、性能复测、远程状态更新或 publication。本轮没有 denied/pending/uncertain 的外部动作；不存在阻止盘点交付的工具阻碍。设计签名和下一 runner 的规则仍待下一实施轮 Lean/Python 验证。

不将未找到同名 API 等同于证明 Mathlib 缺失；不将上轮编译等同于原数学范围的独立认证；不将目录/namespace 调整等同于减少了实际依赖。
