# 固定版本 module 边界决策材料（独立 B 线）

起点 `2a7f8dc51dae6b10bc8344890a32ca0ef323b633`，独立分支
`boundary/module-reproducer`。本次只增加研究 fixture、报告与证据；维护项目仍为
`experiments/kl-for-mathlib`。125 modern / 136 legacy 的生产选择不变。
未改 A 线、main、生产数学代码、三公理、3947 记录严格比较或任何 baseline；未提上游 issue/PR。

固定 Lean 4.34.1 `5045d0056413266e57c625dcd7c365b10e377c52`，Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`。安装来源为 `scripts/setup.sh`
校验的官方 release/cache；Mathlib 工作树干净。下述编译器解释来自该安装包的源码，
不是 latest 文档。输入身份、日志、失败和成本见 [证据目录](evidence/module-boundary/)。

## 可执行结论

| 边界 | 最小例与成功/失败控制 | 结论与可信度 |
|---|---|---|
| private quotientLinear → exposed structureSheaf | [四行失败例](../research/module-boundary/PrivateBoundary.lean)；[三个接口控制](../research/module-boundary/private/) | 公开暴露的实现不能解析私有 helper；取消暴露可保持命题 API，但普通 modern consumer 的 `rfl` 失败。内联与公开且暴露 helper 均恢复模型中的 `rfl`。固定版本实测，高可信；Nat 模型只隔离访问规则，不声称测试了生产商模数学。 |
| attachStalkMap 的 `_` + `by simpa` | [五行核心例](../research/module-boundary/InferenceBoundary.lean)；[泛化项目例](../research/module-boundary/AttachGeneric.lean)；[完整诊断副本](../research/module-boundary/AttachBottomExplicit.lean) | 公开证明的目标仍含 metavariable，tactic 被延迟而不能反过来确定源 grading。显式提供 grading 后核心、泛化和完整文件均通过；高可信。 |
| matcher / equation 表示与 owner | [核心方程实验](../research/module-boundary/generated/)；[matcher consumer](../research/module-boundary/matcher/)；[真实方程检查](../research/module-boundary/CheckStalkJson.lean) | 部分是证明闭包表达式差异，部分是实际可访问性差异；不能混称为命题不等价。真实 stalkMap 的定向 defeq 已验证；其余 181 范围未逐项验证。 |

这些是诊断结果，不是生产迁移批准或完整兼容通过。

## 1. private 实现与暴露接口

生产 `Sheaf/Structure.lean` 的 `quotientLinear` 是 private；公开
`structureSheaf` 的 upper/lower 实现引用它。最小失败例的报错明确指出私有声明存在，
但必须 public 才能从该处访问。它不是缺 import，也不应通过公开所有私有名处理。

可选策略及代价：

- 保持 legacy：维持现有实现可见性和历史接口，本次采用的生产状态。
- 保持 helper private、撤销 structureSheaf 暴露：可提供具名等式作为命题 API；模型中
  `structureSheaf_spec` 可用，普通 modern consumer 的 `rfl` 无法展开。下游 `simp`
  可能要改用具名 lemma；自动 equation 的生成/可见性也需重审。这改变既定暴露政策，不能交付为兼容修复。
- 内联 helper 的实现：模型恢复 `rfl` 且不增加公开 helper，但生产体/生成 equation 和
  serializer 表达式可能变化，必须另做完整严格审计；本次没有证明该改写能保持 3947 记录。
- 明确公开并暴露 helper：模型恢复 `rfl`，同时增加可依赖的名字、定义体和审计记录。
  这是有意改变公共 API/私有边界，须用户明确选择，不是自动修复。

不启用 private-in-public escape。module 可见性也不是保密机制。

## 2. AttachBottom：证明目标必须先确定

核心失败形状：

```lean
module
public section
@[expose] def consume (P : Nat → Prop) (_h : ∀ n, P n) : Nat := 0
variable (Q : Nat → Prop) (hQ : ∀ n, Q n)
@[expose] def attachStalkMap : Nat := consume _ (by simpa using hQ)
```

这里 `_` 产生 `?P`；进入公开实现的 `by` 前，目标是 `∀ n, ?P n`。本 pin 的
[BuiltinTerm.lean:174–184](https://github.com/leanprover/lean4/blob/5045d0056413266e57c625dcd7c365b10e377c52/src/Lean/Elab/BuiltinTerm.lean#L174)
明确设置 `delayOnMVars`，理由是 `by` 会切换到 private context，不能让未确定的目标把
私有数据带回 exporting context。
[SyntheticMVars.lean:563–565](https://github.com/leanprover/lean4/blob/5045d0056413266e57c625dcd7c365b10e377c52/src/Lean/Elab/SyntheticMVars.lean#L563)
在目标含 expression metavariable 时不执行该 tactic；最终报告 stuck。这是 elaboration
调度/边界机制，不是 kernel 证明了原定理不成立。

核心控制：原始 `simpa` 失败；仅换 `exact` 仍失败；显式 `consume Q`、直接证明 term、
取消暴露分别通过。局部 `backward.proofsInPublic true` 也通过，作为编译器机制探针；
它改变证明抽象策略且可能重新引入私有引用，本次不建议或交付该选项。

泛化例只需要现代的 `ModuleData.Basic`，不需要 graph、Sheaf 或 AttachBottom。
它保留原模式：`subtype N _ (range_homogeneous _ _ f.map 0 (by simpa using f.graded))`
再 `.comp C.hom`；报错中的未知项就是源 grading。改成
`range_homogeneous M.piece N.piece ...` 后通过。
[AttachComparison](../research/module-boundary/AttachComparison.lean) 在 private 定向控制中
以 `rfl` 验证原实现与显式参数实现相等，并验证新的 `.map` 计算式；公理闭包仍只有原三公理。
尝试把包含未暴露原实现的相等式直接作为公开 `rfl` theorem 失败，日志保留；不能把同模块私有
检查等同于普通 modern consumer 能展开任意未暴露原实现。

完整 `AttachBottomExplicit` 从已有 AttachProbe-basic 诊断源码派生：只显式填入
`(B.sections Set.univ).piece` 与 `(B.attachBoundary τ α hα).piece`，另加定向 `rfl` 检查。
其原始 downstream proofs 也全部编译通过。为避免改变生产依赖，使用严格按 rejected-131
manifest 重建的 **两个** shadow fixture：Sheaf.Basic、GradedSheaf.Defs；其余 Algebra
artifact 仅符号链接到唯一维护项目，不复制项目、不改生产源码/olean。第一次直接导入生产 legacy
Defs 被 module 检查拒绝；第一次 shadow 路径缺少 Algebra artifact 链接也失败，均保留。

这给出可以独立继续验证的候选：显式参数，无须牺牲 exposure 或公开私有 helper。
但尚未在候选迁移区域重做 3947 严格审计、ordinary modern consumer、公理与生成 equation
全套验收，因此不能称为已批准的生产修复；对下游 `rfl` 的定向证据也不是所有 simp/equation
名字和导出记录都不变的证明。无需重跑已知无效的 implementation-import 组合。

## 3. 生成名字、证明表达式、真实类型与可访问性

### 历史证据的准确边界

[rejected-181/full-comparison.json](evidence/module-rollout/rejected-181/full-comparison.json)
是其所选区域 2609 → 2604 条：6 missing、1 added matcher、7 type-expression changes，
`relocated=0`。对应 [public comparison](evidence/module-rollout/rejected-181/public-comparison.json)
2603 → 2603、没有名称增删、10 type changes，`relocated=0`。
名字列表与全部受影响声明直接保留在这些文件中；名称增删不能称为 owner relocation。
本次没有最小化产生那 **精确六缺一增** 的原始 elaboration/缓存环境，也没有逐项证明那 7/10
个类型 defeq，不能把单个成功模型推广到它们。

131 区域的 1336-record pass 与全量 3947 中唯一 stalkMap.eq_1 失败并不冲突：
producer 是 Sheaf.Basic，历史 realizer/owner 是 held legacy GradedSheaf.Properties。
两个全量视图中 owner 一样，变化字段为 type。恢复 Basic 及五个消费者 legacy 后 125 通过，
这是已有完整验收证据，本次没有重新全编或冒称新鲜重跑了该验收。

### 最小方程模型与真实 stalkMap 的定向证据

模型中 `Map` 只有函数与 `map_add` 证明字段；两种写法保持相同函数和字段 binder 语法。
legacy 的完整证明函数变成辅助常量，modern 暴露后是参数 lambda 内引用辅助证明。
结构表达式不同，但两 body 与替换函数头后的 equation type 均 `isDefEq`，且 `rfl`、`simp`
控制通过。producer 导入后尚无 eq_1；调用 `getEqnsFor?` 实现化，随后导入 Realizer 的审计显示
两条 eq_1 都归 Realizer，原函数各归 producer。这是可重跑的 owner 漏检模型。
本 pin 的 [Eqns.lean:345–377](https://github.com/leanprover/lean4/blob/5045d0056413266e57c625dcd7c365b10e377c52/src/Lean/Elab/PreDefinition/Eqns.lean#L345)
通过 `realizeConst` 生成 equation；不能假设 equation 总在定义函数的那个模块中序列化。

`inspect_retained.py` 对历史完整 TSV 逐节点比对：stalkMap.eq_1 的结构差异仅落在构造出的
LinearMap 的两个证明字段分支（旧 applied-proof 与新 lambda），没有把差异折叠成逻辑不等价。
新的真实检查分别从当前原始 legacy Basic 与严格 manifest 的现代 Basic fixture 触发 eq_1：

1. 无损保留 names、universe 参数、binder info、构造器、literal 和全部子表达式；只丢弃 metadata，
   与既有 serializer 对 metadata 的处理一致。用共享 DAG 避免展开证明产生约 31 MB 的重复文本。
2. 两边捕获均通过 codec 的定向 defeq roundtrip；其 proof 值不被替换成新 axiom/sorry。
3. 旧辅助常量与新同名辅助常量的 universe arity 不同；直接复用名字的首次测试失败，
   不能以重命名字符串后盲目认定等价。最终把 **3 个真实旧辅助 theorem 的 type/value**
   在现代 full 环境中用 fresh 名称经 `addDecl` 内核检查，再只对这些名字定向改写旧表达式。
4. 两个实际 equation type 都由 `Meta.check` 检查良构；结构表达式确实不同；`isDefEq` 通过。
   Nat/Bool 不等控制通过；恢复的真实证明闭包不超出 propext / Quot.sound / Classical.choice。

另用未改的生产 `dumpType` serializer 与 `compare_types.load` 对单条 fresh equation 取指纹：
旧 `72387780ac2996e978f19d36e3a222a2befa9a779adc3bed2f09366fed75fcc4`、
新 `6a81270c96e5d49fff7a7d026e7480dbe41225416176431b0f15cf08b5679f84`，
**分别精确匹配历史 rejected-131 两边**；levels/kind 也相同。
指纹检查是 16.90 s 的定向检查，详见 `historical-fingerprint/comparison.json`。

结论仅限这个实际方程在该 full environment 中的定义相等；不是所有表达式的规范化规则，
也不是 ordinary consumer 可以看见所有辅助体的证明。既有 3947 comparator 完全没改，仍会拒绝
历史表达式的变化。`StalkCodec` 是研究传输工具，没有接入任何接受/导出器/baseline 逻辑。

### matcher 不是可忽略的接口

最小 matcher 模型证明：legacy consumer 可 `#check Boundary.ext.match_1_1`；现代 producer
同模块内部也可见，但 ordinary modern consumer 引用失败，`import all` consumer 则通过。
主 theorem 仍可见。故存在真实 **可访问性** 变化，不能因 matcher 为编译器生成而静默删约。
这不是已复现 181 full view 中精确 missing 六名的原因；full 名称计数与 ordinary 可见性需分开。

本 pin [Match/Match.lean:1074–1101](https://github.com/leanprover/lean4/blob/5045d0056413266e57c625dcd7c365b10e377c52/src/Lean/Meta/Match/Match.lean#L1074)
缓存键含 value、compile、isPrivate，并规定 private 可复用 public matcher，反向不可以。
它支持为什么上下文会影响生成/复用名字的机制解释；本次没有追踪精确 181 差异的全部缓存命中，
故不是对那六个名字的完整归因。

## 决策及后续准入

| 方案 | rfl / simp / equation / exporter 影响 | 是否可直接交付 |
|---|---|---|
| 保持 125 生产范围并保留研究例 | 既有承诺与 strict audit 不变 | 本次完成 |
| AttachBottom 显式源/目标 grading | 定向 rfl 与完整诊断文件通过；生成记录、modern/public 全域尚需验证 | 可安全独立继续验证候选；本次不改生产 |
| 依靠扩大 implementation imports | 原证据失败；不解决 delayOnMVars | 不采用 |
| 移除 exposure / 开 proof/private escape | 会改变可归约/可见性与证明抽象契约 | 需用户明确改变政策 |
| 公开 private helper / 新增稳定 equation 包装 | 增加名字与 API；下游可显式依赖，但需审计新增或替换记录 | 需用户明确 API 政策；不是自动兼容补丁 |
| 内联 helper、改 proof binder 语法以匹配旧表达式 | 有望保留部分归约；可能改变生成名/证明闭包与字段序列化 | 只有完整 strict 比较通过才算现政策内修复，当前未验证 |
| 对所有 matcher/证明/类型做全局归一化豁免 | 可能掩盖真实名称/可访问性/类型变化，改变导出器语义 | 不采用；没有这种授权 |

后续应将已知历史 realizer 加入定向检查，再做严格 regional/full 审计。不要用 owner-filtered pass
或 build pass 替代完整 3947 验收；也不要把 `isDefEq` 的诊断成功改写成 strict pass。

## 复跑与成本

从仓库根，使用新的输出名（记录器与 runner 均拒绝覆盖）：

```bash
bash scripts/setup.sh
python3 scripts/recorded_run.py results/boundary-new/core.log \
  python3 research/module-boundary/run_core.py results/boundary-new/core
python3 scripts/recorded_run.py results/boundary-new/project.log \
  python3 research/module-boundary/run_project.py results/boundary-new/project
python3 scripts/recorded_run.py results/boundary-new/retained.log \
  python3 research/module-boundary/inspect_retained.py
python3 scripts/recorded_run.py results/boundary-new/fingerprint.log \
  python3 research/module-boundary/verify_historical_fingerprint.py \
  results/boundary-new/project/shadow results/boundary-new/fingerprint
```

核心 suite 无需 Mathlib。项目 suite 先要求 `lake --no-build build Mathlib` 成功，之后仅构建
GradedSheaf.Defs 的有限依赖；绝不启动全 Mathlib build。shadow 仅产生两个模块 fixture，
不修改、临时变更或恢复任何生产文件，也不写维护项目的现有 artifact。单例可直接使用
runner 的 `*.inputs.json` 中实际 command/cwd/environment；expected_exit=1 是明确的失败控制，
不是把未通过任务计为通过。

首次 fresh setup 313.23 s，官方 cache 8908 个文件恢复，峰值 child RSS 995392 KiB；
首次 ModuleData.Basic 有限构建 36.63 s，Defs 的追加有限构建 20.50 s。
核心 23 个控制的最终 suite 10.53 s；泛化失败 6.76 s、显式通过 4.45 s、private 定向比较 4.52 s；
完整 AttachBottom shadow 通过 10.04 s。最终 bounded replay 共 69.80 s，峰值 child RSS 7624356 KiB；逐项成本另存 runs.json。
这些是当前容器初始化/定向诊断成本，不是迁移速度、全量构建或冷/热对照结论。
项目 Lean 的 Mathlib 导入占用数 GiB；实际单条方程诊断也不应冒称轻量内存测试。

最初 `/usr/bin/time -v` 因该可执行文件缺失而 exit 127，setup 根本未执行；随后使用仓库
Python recorder/measure。core runner 两次因预期诊断文本与 legacy consumer header 设置错误
而失败，随后修正；原始日志均保留。真实方程的 repr 文本方案因 hygiene 名字/metadata 不能
直接作为 Lean 源及 universe 名字混用失败，转为 DAG 方案；codec 开发编译失败也保留。
早期迭代只有 recorder 捕获的 hash、日志和部分输出源；不是每个未提交编辑版本都有完整副本，
不伪造历史源码。最后 replay 的研究输入、生成 fixtures、JSON 与命令都有可重现身份。

measure 的 RSS 是最大 child，不是所有并发进程之和。core 内部 runs.json 的 max_child_rss_kib
是该 Python 进程至当时的 child 高水位；逐项独立 RSS 应看 project suite 每次新建 measure
的记录。没有可靠 token 遥测，token 成本不可得。没有重新全量验证历史 3947 记录，不能宣称
本次 fresh 全库验收通过。生产项目/scripts/provenance 共 358 个起点 tracked 文件逐字节一致的
独立证据见 production-identity.json；具体产品状态与历史接受仍引用原 rollout 报告。
