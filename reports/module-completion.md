# 剩余 105 个 module 迁移与生成名契约调整

**已完成：261/261 modern，0 legacy。验收代码提交为 `01430c8cd9fceaf6bf91e95a82a2087c020c0fed`；完整66阶段验收通过。后续提交仅归档证据/报告，不改维护项目内Lean或检查器。**

本轮从已验收的 `382d29d94aaa8e32bcdeb24633f070d29695dcc3` 延续
`codex/module-next-region`，不创建 PR、不合并 main。`8769a93203b1324ad7c47dde972d278dff86f146`
只交付过声明清单；该清单中的八项公共兼容定义提案已撤回，未作为生产补丁提交。
用户随后明确同意八个生成名退出稳定公共契约。这是有界的源码接口破坏，不能称为完全兼容。

固定 Lean 4.34.1 / `5045d0056413266e57c625dcd7c365b10e377c52`，Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`。继续使用唯一维护项目和已有官方 cache，
没有升级依赖或从源码全编 Mathlib。初始化没有重跑，不能把本轮 warm 成本当作 fresh 初始化成本；token 无遥测，不可得。

## 八项明确退出的名字

完整限定名、旧 Lean 类型及实际 recursor 正文见 [历史声明清单](matcher-compat-declarations.md)。
清单保留作证据，不再代表拟交付的兼容定义。机器登记 `module-all-interface.json` 逐项固定
旧 levels/type hash/kind/owner，不使用 match_N 正则或未来自动豁免。

| 完整名字（均以 `OAI.KLInvariance.` 为前缀） | 旧辅助操作 | 保留的实际接口 |
| --- | --- | --- |
| `CoefficientChange.ext.match_1` | 包装结构的 Prop 消去 | `CoefficientChange.ext`、`casesOn`、`mk`、`val`、`equivVal` |
| `LocalCover.splitEquiv.match_3` | `P × ker g` 的 Prop 消去 | `splitEquiv` 正反向计算；标准 `Prod.casesOn` |
| `MomentGraph.GradedSheaf.extendBottom_upperQuotient.match_1_1` | `∃ w, α d • w = v` 的依赖 Prop 消去 | `extendBottom_upperQuotient`；标准 `Exists.elim`/`rcases` |
| `MomentGraph.GradedSheaf.extendBottom_upperQuotient.match_1_3` | `∃ w, v = α d • w` 的依赖 Prop 消去 | 同上，等式方向由调用处表达 |
| `ReflectionFrobenius.wallCoordinate_injective.match_1_2` | `Fin 2 × ι` 的 Prop 消去 | `wallCoordinate_injective`、`wallCoordinate`；标准积消去 |
| `ReflectionFrobenius.wallMatrix_mulVec.match_1_1` | `Fin 2 × ι` 的 Prop 消去 | `wallMatrix_mulVec`、`wallMatrix`；标准积消去 |
| `ReflectionPairTranslation.Twist.ext.match_1` | Twist 包装结构的 Prop 消去 | `Twist.ext`、`casesOn`、`mk`、`val`、`equivVal` |
| `TitsSpace.exists_common_transverse.match_1_1` | `(E×E) ⊕ (Bool×E×E×E)` 的 Sort 消去 | 公共存在性定理、`rootDifference`、`wallVector`；标准 Sum/Prod 消去 |

第八项确实能计算，不能把它误称为纯证明项。但实际源中的 E/A/v 仅为单个证明向
`exists_avoiding_functional` 提供索引：左支 rootDifference，右支 wallVector。保持局部即可，
没有独立用途需要新增公共归纳类型或八个语义包装。旧生产源码对八名的直接引用为零；外部引用者仍须修改调用。

新增的唯一生成名 `OAI.KLInvariance.LocalCover.splitEquiv.match_6` 与实际旧 match_3 的类型、正文
定义相等，且具有 matcher 元数据。它是编译器编号变化，不作为数学 API 扩张或稳定新操作。
其他生成名仍检查，例如本轮保留的 `TitsSpace.bottDegree.match_1` 通过旧正文比较和普通消费者 rfl。
本轮没有批准或实施“所有生成名均可丢弃”的政策。

## 生产改动和私有边界

105 个生产文件作 module/public import/public section/expose 迁移；数学正文唯一变化是 Structure
中两处 `(quotientLinear α e)` 内联为 `((Ideal.Quotient.mkₐ R (Ideal.span {α e})).toLinearMap)`。
原 private helper 保持 private。没有公开 helper、撤销 expose、改写 stalkMap 证明或添加数学定理。
逐文件输入/输出 SHA256 和精确编辑保存在 `module-all.json`；源检查组合此前所有层，其他正文改动会失败。

撤回的 run_elab 公共补名方案连同完整 patch、计划、两处失败日志保留在证据中。其早期 generic toy 通过
不等于真实八项交付；实际54根编译在 CoefficientChange/Twist 名称解析处失败。撤回后同54根编译全通过。

## 表达式、名称和实际使用的证据

完整导出继续使用原 exporter/compare_types.py 与原历史基线，不刷新基线。
实际旧3947名的处置应逐项核算：3939名保留、8名明确退休、1个生成项新增，实际导出3940条。
完整原始差异单独保留；继承的156模块检查使用明确标记的 prior-contract view，绝不把恢复的历史登记当作当前可访问声明。
每个继承比较均附八项破坏与新增登记，且最终实际3940记录审计是必需步骤。

ForMathlib 完整区域比较为3150→3143：8 missing、1 added、0 owner change，另有
`TitsSpace.coefficientAction_reflection` 一项 type hash 变化（5b6c1815…→9776e80a…）。
实际旧类型在普通现代消费者中可用，并通过定义相等、按旧类型使用当前证明、rw/simp 和公理检查。
这不是命题逻辑不等价的证据，也不产生任何全局 defeq 豁免。

普通导出的隔离诊断保留两种原始视图。沿用旧156 proof-owner范围时有117个表达式差异；
仅把范围更新为当前261模块、保持原150个精确 proof-alias 名单、原 theorem-kind 条件和完整命题表达式后剩7项。
没有增加通配 proof/matcher 规则，也没有任意展开数学定义。115项实际旧类型均另行提取，导出指纹与旧完整基线115/115匹配，
并在普通现代 imports 下逐项通过旧类型使用、kernel、isDefEq 和三公理检查；40个实际旧 helper 的类型/正文在新名字下内核检查。
余下两项视图差异已有上一轮精确证据。ForMathlib 七个、完整十二个普通视图 pair 另以完整旧新记录和实际表达式固定，其他差异拒绝。

保留了 bottWeight.eq_def 的失败控制：把仍保留的公共 matcher 引用替换成新审计名字后默认 isDefEq 失败，具体 Meta 比较路径尚未最小化。
这属于引入额外审计常量后的失败，不能直接归因于生产 API；历史调用应保留其公共名字。保留后115项通过。另外独立比较旧新 matcher 正文并测试普通消费者 rfl，
而不是把失败静默删除或给该 matcher 增加豁免。

Structure 的135个历史名/类型、20个旧 helper 的内核重建，以及 vertex/upper/lower/base-change 的 rfl/rw/simp
都在当前105候选下通过；唯一不可访问者为上述 LocalCover 旧 matcher。原 private quotientLinear 的封装和计算承诺均受定向检查保护。

## 完整验收与重跑

`01430c8cd9fceaf6bf91e95a82a2087c020c0fed` 上的最终 `scripts/check.sh warm`
**66阶段全部通过**（610.310秒）。完整9186-job构建此前已成功，本次首先用 `--no-build`
检查官方Mathlib与全部生产工件就绪，再运行完整接口/公理/回归，最后warm build通过。
261个生产Lean文件与实际完整构建的输入SHA一致；最终审计的378个项目输入也逐字未变。

| 项目 | 结果 |
| --- | --- |
| 全部模块 | 261 modern / 261，总计0 legacy |
| 生产正文 | 仅Structure两处私有计算调用内联；其余105范围正文还原比较一致 |
| 实际完整导出 | 3947→3940；8 missing、1 generated added、3 type pairs、0 owner changes |
| 普通现代完整导出 | 3940条；准确名字/kind/universes/owner/三公理通过；12个固定type pairs |
| 实际旧类型 | 120/120与旧完整指纹匹配；普通现代历史类型使用、kernel、isDefEq通过 |
| 实际旧helper | 53个类型/正文在新审计名字下通过kernel检查 |
| 定向方程 | 10项rw/simp实际用了对应规则；新增OAI属性、OnHom属性和Structure历史属性通过 |
| 公共计算 | 两个包装结构、splitEquiv正反向、Structure及base-change、rootDifference/wallVector、bottDegree/bottWeight、embedLinear、bottHeadPairCoordinates的rfl控制通过 |
| 继承约束 | 原历史/追加声明、stalkMap单项、25模块单项记录、原比较器与源保护、所有既有回归通过 |
| 提交动作 | 仅独立分支；没有创建PR或合并main |

三项完整表示差异逐项固定如下；完整64位hash、levels、kind、owner与实际表达式/见证hash均在
[接口登记](../experiments/kl-for-mathlib/module-all-interface.json) 中。它们不是通配defeq豁免。

| `OAI.KLInvariance.TitsSpace.` 下的名字 | 旧/新完整type hash前缀 | 证据 |
| --- | --- | --- |
| `coefficientAction_reflection` | 5b6c1815… / 9776e80a… | 实际旧类型使用、kernel、rw/simp |
| `bottHeadPairCoordinates.eq_1` | 40ec50e7… / 8f83323b… | 同上，原equation属性及实际toFun rfl |
| `embedLinear.eq_1` | b309f0cf… / 5d2b2d3e… | 同上；旧GraphEmbedding生产者生成，历史Edge owner不变，embed rfl |

隔离的 `ProofLocations-v2.lean` 使用ExprStructEq、共享binder上下文，逐层检查实际旧新类型：
三个目标均未发现非proof部分的结构差异；proof-valued子表达式的类型另经定义相等检查。
这个诊断包括重复出现和审计重命名，计数不是独立改动数量。它不修改导出器，也不参与全局归一化。
最终接受仍依赖固定旧新记录、实际旧表达式、普通消费者、kernel、属性与公理。

证据入口：[manifest](evidence/module-completion/manifest.json)、
[完整66阶段](evidence/module-completion/accepted/stages.json.gz)、
[最终命令成本](evidence/module-completion/research/full-acceptance-v2.json.gz)、
[最终输入身份](evidence/module-completion/research/full-acceptance-v2.inputs.json.gz)、
[源码和版本绑定](evidence/module-completion/research/final-source-and-pins.json.gz)。
完整原始TSV与差异、旧源提取、失败控制及撤回补丁都保留，压缩文件的原始/存储SHA在manifest中。
[普通实际旧类型见证](../experiments/kl-for-mathlib/ModernOrdinaryAllCompat.lean) 和
[计算消费者](../experiments/kl-for-mathlib/ModernAllConsumer.lean) 可直接重跑。

在已初始化、工件就绪的仓库运行：

```sh
source scripts/env.sh
scripts/check.sh static
scripts/check.sh warm
```

新机器先运行 `scripts/setup.sh` 获取固定版本与官方cache，再用 `scripts/check.sh all`
构建和审计唯一维护项目。没有重新初始化或全编Mathlib来代替本轮诊断。

## 成本、失败与限制

以下为独立命令墙钟，存在并行，不能相加当作总经过时间；RSS是最大子进程RSS，不是容器聚合峰值。

| 命令/阶段 | 秒 | 最大子进程RSS KiB | 结果 |
| --- | ---: | ---: | --- |
| 未交付的公共补名候选54根 | 130.739 | 3236488 | CoefficientChange/Twist名称解析失败；方案撤回 |
| 撤回后54根 | 163.701 | 3242796 | 通过 |
| 完整ForMathlib/OAI构建 | 1506.101 | 3322556 | 9186 jobs通过 |
| 首次集成检查 | 150.422 | 7321836 | 新检查缺少Cover.Local import；已修正 |
| 最终完整验收 | 610.310 | 7328312 | 66阶段通过 |

其他实测命令、CPU时间、局部旧源提取及失败成本见research下相应metrics。13次成功的旧类型提取命令墙钟累计275.888秒（存在并行，非总经过时间），其中旧Stalks提取99.335秒。
新单测首次mock覆盖版本查询的失败已保留，修正后针对12个普通pair的字段/名称变异测试通过；
最终全量也重新执行这些回归。OnHom属性输出曾与计时JSON同名，日志保留原值，改用独立输出名后重新提取通过。

完整旧历史环境没有重新构建：冻结旧完整导出用于基线；120项旧表达式另由固定旧生产者源提取，
其指纹逐项匹配基线，再在真实普通现代环境中使用。部分提取使用完整单个生产者文件，尤其Stalks，
不声称是最小复现，也没有启动全历史项目或全Mathlib构建。

初始54根列表由命令内读取，未被recorder作为单独参数枚举执行时hash；生成脚本与列表完整保留。
最终完整构建直接指定ForMathlib/OAI，不依赖该列表，261个生产输入另逐项核实。
初始化未重跑，fresh初始化成本本轮不可得；token无遥测，不可得。

剩余研究限制：把保留的bottDegree matcher换成新审计名字后，默认Meta isDefEq的失败未进一步最小化；
补可归约性标记也未解除该隔离失败。它没有被当作生产API失败或豁免：实际旧名字被保留，其旧正文比较、
普通rfl调用和按原名字的旧类型使用均通过。任意未知外部脚本/旧二进制没有逐个验证；外部若直接引用上述八名，
必须改用标准消去或现有数学接口。本轮因此明确不声称完全源码或二进制兼容。
