# 三个 sheaf 模块迁移与单项 equation 兼容验收

**完成：128/261 个产品模块 modern，余下 133 个 legacy；49 阶段完整验收通过。**

从核实的 main `bc7cc147e9742f8f6c77a53785813dbdd6960311` 建立独立分支
`codex/attach-bottom-module`；该起点树等于 imports 验收 head `ed29a2e`。
实际完整执行检查点为 `424bcdf25e746d12573af9a410e8e25ae6018fcf`。
本次未合并 main，未整批合入此前研究分支；只有限定旧证明 DAG 与测试思路被复用。
最终交付只补报告、证据和 README 导航，验收后的 Lean/检查器/规则代码保持不变。

固定 Lean 4.34.1 `5045d0056413266e57c625dcd7c365b10e377c52`、Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`。沿用已就绪官方 cache；没有重新 setup、
升级、全编 Mathlib、lake clean 或修改全局 Lean 配置。Mathlib Git 工作树干净。

## 源码范围与实际正文修改

仅迁移：

- `ForMathlib.Combinatorics.MomentGraph.Sheaf.Basic`
- `ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Defs`
- `ForMathlib.Combinatorics.MomentGraph.GradedSheaf.AttachBottom`

[attach-module.json](../experiments/kl-for-mathlib/attach-module.json) 以起点 Git blob、精确 edits
和 before/after SHA256 约束全部变换。必要 module/public import/public section/expose 之外，
唯一数学实现正文的写法变化是 attachStalkMap 中两个显式 grading 参数：
`(B.sections Set.univ).piece` 与 `(B.attachBoundary τ α hα).piece`。
**原 stalkMap 的 map_add'/map_smul' 证明写法完全保留**，没有沿用上一轮 by-intro 或显式 proof-target 改写。

这不是 import-only。新源保护层的精确逆变换会撤销这两个已记录参数，再进入原有迁移/证明核对；
它不对任意证明或类型做归一化。不可识别的正文或 header 改动仍拒绝。
261 个产品中其它 258 个逐字节不变。原 3902 快照、45 additions、原完整 serializer、原
compare_types.py、旧 proof/source/rollout/import manifests、有限 proof-alias 规则、锁文件与 pins
保持原字节。新增三文件层单列，原 125 范围作为历史层保持不变；剩余 133 legacy 的源保护保留。
维护项目仍只有 `experiments/kl-for-mathlib`。

## 此次明确授权的单项政策

原始结构检测继续执行，原始失败结果完整保留。新增
[stalk-equation-compat.json](../experiments/kl-for-mathlib/stalk-equation-compat.json) 只允许：

| 字段 | 精确绑定 |
|---|---|
| name | `OAI.KLInvariance.MomentGraph.Sheaf.stalkMap.eq_1` |
| levels / kind | `[u, v, w, z]` / theorem，原序列化字符串固定 |
| old type hash | `72387780ac2996e978f19d36e3a222a2befa9a779adc3bed2f09366fed75fcc4` |
| new type hash | `6a81270c96e5d49fff7a7d026e7480dbe41225416176431b0f15cf08b5679f84` |
| 当前历史 realizer owner | `ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Properties` |
| 版本 / 输入 | 固定编译器、Mathlib、旧完整 type/proof DAG SHA256、普通消费者源码 SHA256 |

[attach_module.py](../experiments/kl-for-mathlib/attach_module.py) 在任何 missing/added、第二项变化、
其它名字/字段/level/kind/hash、错误 owner 时拒绝。当前完整记录比较额外拒绝所有 owner 迁移。
其严格期望取自 main 起点 A 线完整 3947 export，并与该 Git 对象的压缩文件逐字节核对；
没有刷新 baseline。旧 reference 3902 的历史模块重定位仍按原架构规则处理，当前 3947 的 owner 则零变化。

只有精确这一对差异匹配，才实时运行普通现代 Lean witness；失败即验收失败，不使用旧成功标记。
输出分别保留 `raw.passed=false`、原始 changed 记录、明确的 accepted_representation_changes 单项与
最终 `passed=true`。其它声明的比较逻辑没有改变；这不是一般 defeq 豁免或未来自动接受机制。
旧两个改写候选的不同 hash 不在此政策中。

## 普通现代消费者与真实旧类型

[StalkEquationCompat.lean](../experiments/kl-for-mathlib/StalkEquationCompat.lean) 使用普通
`module; import ...AttachBottom; import Lean`，无 import all、无 legacy aggregate：

1. 从固定的 [旧 DAG](../experiments/kl-for-mathlib/stalk-equation-old.json) 恢复真实旧类型与三个 helper 的
   type/value。数据源为原始候选研究提交 `67bcbc5` 的 old JSON，原 Basic 源 blob 与当前起点相同。
   保存所有 Name、universe、binder info、表达式结构和证明值，只忽略原 serializer 同样忽略的 metadata。
2. 旧 helper 与现代同名 helper 的 universe arity 不同，因此用 fresh 名称安装 **真实旧 theorem**，
   每个 type/value 经 addDecl 内核检查；不新增 axiom/sorry、不假设旧证明、不借用共同 full 环境。
3. 在普通现代环境取得实际 equation，核对其精确用户名，检查旧/新类型良构且确实结构不同，
   实时验证定义相等，并由内核检查实际命名新 equation 可以直接证明完整历史类型。
   Nat/Bool 不等控制通过；旧 helper 与历史类型使用的公理闭包均不超过原三公理。
4. 用普通源代码 `#check Sheaf.stalkMap.eq_1`，直接 rfl，以及
   `rw [Sheaf.stalkMap.eq_1]; rfl`、`simp only [Sheaf.stalkMap.eq_1]; rfl` 验证实际使用。
   rw/simp 的末尾 rfl 用于结构投影归约，未声称它们单独自动关闭目标。
5. 单独从起点 Git blob 编译一个旧 Basic fixture 测属性，再与普通现代 equation 对照：
   两边 `defeq=false`、`backward_defeq=true`。没有开启 backward 选项或更改属性。
   相同 rfl/rw/simp 源控制在旧 legacy consumer 中也通过，见 old-api-controls。

普通 private import 下，Lean 会按 consumer scope 实现化一个 `_private.StalkEquationCompat...eq_1`；
解析器中的准确用户名字保持 `Sheaf.stalkMap.eq_1`。测试按官方 getEqnsFor? 返回实际 backing name，
再核对 privateToUserName?，没有假定 backing name 必是全局名，也不把此本地 realization 当作 producer owner 迁移。
完整导出的历史 realizer 仍是 Properties，其实际编译与记录均已验证。

[ModernAttachConsumer.lean](../experiments/kl-for-mathlib/ModernAttachConsumer.lean) 另外核对
attachStalkMap/extendBottom/attachAssignment 实际为可见 defnInfo，验证 map 的 subtype val/坐标、
新旧顶点、边 projection/comp 与 assignment 的 rfl，并检查延拓/生成等 theorem 名字。
[ModernAttachTypes](../experiments/kl-for-mathlib/ModernAttachTypes.lean) 使用继承的有限 alias 与
original-kind 规则，严格核对三个 producer 的全部原有 93 条记录及公理闭包。

## 完整结果

[完整证据](evidence/attach-module/) 包含实际输入身份、失败、49 阶段日志、完整 TSV 与独立 JSON 结果。
比较采用继承 serializer 的规范化完整记录；原始 TSV 保留，不宣称文本字节相同。

| 检查 | 结果 |
|---|---|
| source/proof transport、覆盖与依赖边界 | 全部通过；只修改三个产品，原证明写法保留 |
| 完整 ForMathlib / OAI 构建 | 真实构建通过，9186 jobs；Properties 和所有应用/兼容入口包括在内 |
| 当前完整 3947 记录 | 无 missing/added/owner 变化；恰好一个已绑定 type diff，其余字段/记录相同 |
| 原 3902 + additions 45 | 原始 diff 单项保留并单独接受；45 严格比较通过 |
| 既有现代视图 | 原 11 与 rollout 1196 记录通过 |
| 新现代视图 | 93 条记录、original-kind 与三公理上界通过 |
| 计算/导入/入口回归 | 旧名、`.val`、逆映射、rfl、边界及应用检查全部通过 |
| 公理 | 16 root 与 81 pilot 命名闭包及各现代闭包仍限 propext / Quot.sound / Classical.choice |
| 对抗回归 | 继承比较器 31、partition 14、proof evolution 30、module 7、rollout 7 与新增 4 组均通过 |
| 最后 warm build | 7.76 s，通过，无源重编 |

全量执行时所有 1386 个捕获文件在运行结束后仍匹配预执行 hash，检查点为 `424bcdf`。
报告和 README 导航在验收后补充；没有修改 Lean、规则、检查器行为、manifest 或 pin。
没有为了最后交付重复完整构建。

## 实际成本、失败与限制

| 操作 | wall 秒 | 说明 |
|---|---:|---|
| 三模块局部 build + Mathlib no-build readiness | 63.23 | 重用固定 cache |
| 普通现代最终局部 witness / consumer / 93 类型检查 | 22.63 | 无 import all |
| 旧属性 fixture | 19.61 | 单个旧 Basic，不是另一个项目或全历史重编 |
| 旧 rfl/rw/simp 源控制 | 6.73 | 复用该 fixture |
| 静态源保护 | 10.79 | 通过 |
| 相关回归最终局部运行 | 11.69 | 48 项相关检查 |
| 完整 library-build 阶段 | 3015.88 | 实际所有下游构建 |
| 完整 migrated-types 导出 | 23.02 | fresh |
| 原 3902/45 比较含 live witness | 13.35 | raw 单项保留 |
| 当前 3947 比较含 live witness | 14.66 | owner 零变化 |
| 完整 49 阶段总 wall | 3302.39 | 全部通过 |

完整运行峰值 child RSS 为 7332692 KiB（约 6.99 GiB），不是并发进程总内存。
沿用 env.sh 线程配置、四 CPU quota 与原串行编译 gate；Lake job 时间含排队/锁等待，不可相加。
UpperSections 的 Lake job 记录约 1088 s，是主要成本点；没有据此推断模块迁移速度或内存改善。
未测新鲜初始化或受控冷/热对照。没有可靠 token 遥测。

失败都保留：最初消费者在局部 build 未结束时启动，Basic artifact 尚不可用；此失败不作 API 结论。
随后的探针曾错误假定 consumer equation 的 backing name 为全局名；#check 可解析，实际是本地私有 realization。
一次 withExporting 探针因普通 import 不对外 re-export 而找不到该函数，测试改为普通私有 proof scope，
未改变生产 imports 来绕过问题。rw/simp 初稿未写最后投影 rfl，留下目标；最终用明确归约控制修正。
旧负向回归曾因错误消息前缀变化失败；恢复消息兼容后通过，拒绝条件未削弱。

本次只接收这条 equation 的表示变化。其余 matcher/类型边界与 Structure 的 private helper
没有被豁免，剩余 133 个 legacy 模块未迁移。源码/API 检查不承诺旧 olean 二进制缓存互换，
也不由这些结果推出普通 public 文档可见性或任意未测试 tactic 自动化不变。
未新开上游 issue/PR，未合并 main。

## 复跑

从仓库根，保持官方 cache 与固定 pins。为 recorder 使用新 label：

```bash
source scripts/env.sh
python3 scripts/recorded_run.py results/attach-recheck/full.log bash scripts/check.sh
# 所有产物已就绪时可避免重复源构建：
python3 scripts/recorded_run.py results/attach-recheck/warm.log bash scripts/check.sh warm
```

最小消费者可在维护项目内直接运行 `lake env lean StalkEquationCompat.lean`、
`lake env lean ModernAttachConsumer.lean`。`proof_evolution.py --compare` 与
`attach_module.py --compare-full` 对完整导出执行比较；实际单项接受每次都会调用 live 普通 witness。
不要手动把 raw 的 passed 改为 true 或刷新 reference snapshot。
