# AttachBottom 显式 grading 修复试验：严格兼容拒绝

起点为核实并 fetch 的 imports 验收提交
`ed29a2ef4639ea0eeabb4db8a08755bee430279d`，独立分支
`boundary/attach-bottom-explicit`。未合入 boundary/module-reproducer 整批研究材料；只参考
`67bcbc5129c16337e7ffd9573826b2c56e358ec4` 的固定版本结论与两个模块 header 变换。
main 合并不影响此起点；本次未操作 main 或 A 线分支。

**结论：本轮没有可交付的生产修复。** AttachBottom 的推断失败可用两个显式参数解决，
真实普通现代消费者及 93 条现代类型/公理检查通过；但最小依赖中的 Sheaf.Basic 仍使历史
`stalkMap.eq_1` 的严格类型表达式不一致。两种不改数学接口的局部证明写法均未解决。
未撤销 expose、未使用 import all 消费者、未豁免表达式或 matcher、未改三公理和比较器。
最后生产树已恢复为起点，仅保留研究/证据/报告。

## 实际范围与正文变更

必要最小 local 依赖链是：
`Sheaf.Basic → GradedSheaf.Defs → GradedSheaf.AttachBottom`。
其它依赖已 modern。只在唯一维护项目 `experiments/kl-for-mathlib` 原地受控修改这三个文件，
没有第二个项目、全 Mathlib build、setup 重复初始化或 pin 更新。

完整文件、before/after SHA256、精确 diff 与拒绝状态见
[trial-plan.json](../research/attach-explicit/trial-plan.json) 和
[final-candidate.patch](evidence/attach-bottom-explicit/final-candidate.patch)。这是真实正文试验，
**不是 import-only**；没有把它注册成已接受的 source/proof exception。
原 source/proof manifests、导出器、有限 alias 规则、baseline、完整检查器均未改变。

- 三文件 module/public import/public section 与必要 data/instance expose 变换；保留公开实现。
- AttachBottom.attachStalkMap：把 `range_homogeneous _ _` 中两个 grading 依次填为
  `(B.sections Set.univ).piece` 和 `(B.attachBoundary τ α hα).piece`。其余证明正文不改。
- Basic.stalkMap，候选 1：把 `map_add' b c := by ...`、`map_smul' r b := by ...`
  改为 `map_add' := by intro b c; ...`、`map_smul' := by intro r b; ...`，原 tactic 主体保留。
  目的为在公开暴露边界内抽象整个证明函数，尝试恢复旧 equation 中 proof-field 形状。
- Basic.stalkMap，候选 2：进一步显式写出两个证明目标的 `∀`、`@Eq` 和完整 dependent Pi
  codomain，并给其中 lambda 的 Outgoing 参数显式类型。保留相同函数、数学等式和归约意图；
  这是另一种正文/证明表达式改写，仍不视为已接受。

尝试显式 universe 表达式与省略 lambda 参数类型的中间版本曾编译失败；日志保留。
最终候选取消该额外 universe 参数并补上参数类型，可编译，仍不符合严格表达式。
不存在“所有局部写法都不可能”的证明；结论只是这两种有针对性的候选未能在现标准通过，
继续锁定编译器内部 proof/universe 表达式需要新的局部设计，不能自动放宽标准。

## 验证结果分列

| 项目 | 实测结果 | 限制 |
|---|---|---|
| 环境/依赖 | 固定 Lean4.34.1/5045d005，Mathlib/d13f23b；`lake --no-build build Mathlib` 成功 | 重用现有官方 cache，不重新 setup、不全编 Mathlib |
| 起点有限目标 | AttachBottom 及现有依赖编译通过，20.41 s | 不是 fresh 全库验收 |
| 候选 1 编译 | 三个实际生产模块重编通过，23.64 s | 不代表类型兼容 |
| 普通现代消费者 | 仅普通 import AttachBottom 与 Lean，成功，5.23 s；最终候选再检查 4.45 s | 无 import all；不是 isolated shadow fixture |
| 普通现代类型/公理 | 三模块原有 93 条记录严格比较通过；原始 kind 检查及各自公理闭包均不超过三公理，5.24 s | 未替代全量 3947 检查 |
| 定向 implementation 类型 | 两候选均 228 对 228，无 missing/added；均有同一条 stalkMap.eq_1 type diff（探针 owner 标注见下文） | 该必需条件失败，候选拒绝 |
| 恢复后有限目标/静态源保护 | 重建 23.24 s、静态 13.17 s，均通过；359 文件逐字节恢复 | 恢复检查通过也不是候选接受 |
| 候选完整全库 build/export/公理/回归 | **未运行** | 便宜的已知必要条件已失败；不花全库重编成本重证同一拒绝，不宣称 full pass |

[ModernAttachConsumer.lean](../research/attach-explicit/ModernAttachConsumer.lean) 验证：

- attachStalkMap、extendBottom、attachAssignment 在普通 modern env 中实际为 defnInfo，体确实暴露；
- attachStalkMap.map 到 `C.hom.map` 的 subtype val 及其坐标值均 `rfl`；
- 新底点和原顶点的 vertex、下边的 projection/comp 定义、底点 assignment 均 `rfl`；
- lift_global、extendBottom_generated、extendBottom_edgeFlabby 名字可访问。

`ModernTrialTypes.lean` 复用现有 modern serializer/有限 alias/原始 kind/axiom 逻辑，
只将 owner/expected 集合限定为本次三个实际 producer 的原有 93 条声明。
期望从 A 线验收的完整 3947 export 取出，不建立新 baseline、不接入全局接受逻辑。
它作为真正普通 module 编译；无全实现 imports 消费者兜底。

`RegionTypes.lean` 是 legacy implementation 诊断 root，用未改的生产完整 serializer
导入实际 AttachBottom。为防止再漏掉历史 realizer，显式触发 stalkMap 的 eq_1，并把其类型
单独列入导出；该诊断记录的 owner 人工标注为历史 Properties，**不是本次真实 realization
owner 测量**。真正的历史 producer/owner 仍分别是 Basic / GradedSheaf.Properties。
本次 exporter 的单条人工 owner 标注只供对齐类型检查；没有用它论证 owner 未变化。

严格期望取自起点 A 线验收的全量导出，按已导入 local owner 集合选取全部记录，再明确加入
历史 eq_1；**不是仅对两边名称交集比较**。修正后的 compare_region.py 同时拒绝 missing、added、
levels、type、kind，并记录 owner 变化；它不改 `compare_types.py`。

同一条历史 equation 的 type fingerprints：

| 版本 | SHA256 |
|---|---|
| 已验收历史 | `72387780ac2996e978f19d36e3a222a2befa9a779adc3bed2f09366fed75fcc4` |
| 候选 1（by intro） | `6fdf49c42922cd6ebe895ed4dfc4bdf168eebd747e8fdc16fb3b9ff1da796afc` |
| 候选 2（显式 proof targets） | `4ae24f5b1dd87cda67cfee6eb747c5dabf2ac82bc409cd999b56d0961644a4c7` |

这仍是严格表达式失败，不是命题逻辑不等价的结论；此前对原现代表示的 isDefEq 结论
也不能接受这两个新候选或改变完整比较政策。差异包括证明字段中 codomain 展开、universe
表达式与 cast proof 表达式；详细 DAG 路径保留在 strict-final-v1/v2.json.out。
本次没有尝试剩余 136 模块总体迁移，也没有触及 Structure/private helper。

## 失败、执行身份与成本限制

所有 recorder identities、候选来源及最终文件、日志、TSV、比较结果保留在
[evidence/attach-bottom-explicit](evidence/attach-bottom-explicit/)。输入记录在执行前捕获；
候选 source snapshot/patch 另标注归档位置，未冒称每次手工编辑都有完整旧版本。

起点 exporter 首次在 `discard <| ← getEqnsFor?` 的 harness 写法处失败；虽输出过 TSV，
**未作为 fresh baseline 成功证据**。后来修复 harness，并用已绑定 A 线完整导出作为严格期望。
比较脚本收紧 owner 集合时曾因变量遮蔽失败；修复后用 recorder 再跑两种固定输出，均正确 exit 1。
失败日志不删除、不改变为成功。直接工具编排的语法错误未启动 shell，不能计为 Lean 尝试。

`typed-v2-build` 尚未结束时编辑了源并启动下一版本，故该次预执行 hash 不能证明编译器
实际读取了同一版本；**不把这次成功计为 source-bound 验证或独立时间对照**。
后续 source 保持不变，最终类型运行先通过 Lake no-build readiness，再 fresh elaboration 诊断 root；
随后普通现代类型/公理与 consumer 也独立通过。重叠 build 时间不可相加或解释为隔离测量。

wall/CPU/RSS 见各 JSON；RSS 是最大 child 而非进程内存总和，Lean 项目导入约数 GiB。
没有 token 遥测。没有新鲜初始化成本；没有声称完整全库接受或性能改善。

## 下一步边界

可确认两个显式 grading 参数解决公开证明目标推断，普通现代 API 也保持了所测计算承诺。
但要交付必须先找到保持历史 stalkMap.eq_1 完整类型表达式的局部方案，再执行完整 3947
导出/公理及适用全库回归。当前停止在这一兼容性拒绝；不是权限拒绝，也没有 pending 写操作。
没有将任何 policy 改动提交供默认接受。
