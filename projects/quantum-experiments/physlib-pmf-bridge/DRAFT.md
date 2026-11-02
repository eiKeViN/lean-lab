# UNVERIFIED_DRAFT：离线源码草稿接续

2026-10-31，**四份 Lean 文件均未编译/解析/公理检查**；没有接受证明或运行收益。
网络403保留在`preparation.json`和`results/prepare01/`，本次没有网络请求或Lean调用。
这些草稿是待修订的真实导入客户端，不是可作为依赖的库，也不是旧版Lean回放。

## 文件和明确未完成项

|文件|拟交付的接口/消费者|显式占位义务|
|---|---|---|
|[Bridge](UNVERIFIED_DRAFT/PMFBridgeDraft/Bridge.lean)|toPMF/ofPMF、两点值、两往返、equiv/injectivity、PMF.bind实数有限和观察|B01、B02、B03|
|[Native](UNVERIFIED_DRAFT/PMFBridgeDraft/Native.lean)|原生共享bind、点值、结合律及DMChannel串接/comp_assoc|N01、N02|
|[ViaPMF](UNVERIFIED_DRAFT/PMFBridgeDraft/ViaPMF.lean)|桥输送bind/bind_bind，并公开同一个实数点值合同和通道任务|无新占位，但依赖Bridge全部三个未完成义务|
|[Compare](UNVERIFIED_DRAFT/PMFBridgeDraft/Compare.lean)|两route的分布/通道输出相等|无新占位，但依赖两路线的未完成证明|

五个` sorry `证明项均显眼标识。它们不属于已完成统计；无新占位的文件也不代表已验证。
`draft-status.json`登记每个占位的位置及四源码字节，后续不可把本快照回填成接受运行。

- **B01**：非负实有限和归一化搬到`ENNReal.ofReal`的有限和。
- **B02**：从`PMF.tsum_coe`、有限载体及`apply_ne_top`得到toReal有限和归一。
- **B03**：`PMF.bind_apply`转为实数有限和；需有限tsum、toReal的sum/product接口。
- **N01**：原生bind归一化：非负证明已给候选，交换有限双和并复用每个输入的normalized。
- **N02**：原生bind结合律：展开点值、分配、交换有限双和及乘法结合。

保存的固定来源中没有上述有限和转换/交换helper的声明源码，故不猜它们的精确参数，
用未完成义务明确暴露，而不是编造已核实API或添加给调用者的新假设。恢复时优先查原生helper后填 proof。
草稿其余tactic、rfl、隐式参数、coercion和导出可见性仍可能失败，也都未通过Lean核验。

## 已读API依据及设计公平性

源码依据仍是研究检查点`98a6b804a911bac97327df961628e65fbf98155f`的11份原样快照与sources.json。
本次重新核读以下声明或使用点，没有访问网络：

- Physlib `ProbDistribution`、`mk'`、`normalized`、`ext`及`Prob.zero_le_coe`：真实有限前端。
- Physlib Channel：真实`DMChannel.symb_dist`；不复用注释中的`Channel.comp`。
- PMF Constructions：`ofFintype`和`ofFintype_apply`，且公开导入Monad。
- PMF Basic：`ext`、`tsum_coe`、`apply_ne_top`。
- PMF Monad：`bind`、`bind_apply`、`bind_bind`。
- Physlib Prob固定源码使用`ENNReal.toReal_nonneg`、`toReal_ofReal hx`和`ofReal_toReal hx`。
  后两项依据是已有调用点而非本次直接读取声明体；实际elaboration仍待检查。

Native仅显式导入真实Channel，未调用桥/PMF；ViaPMF不借用Native的归一化或结合律。两边共享的是上游真实前端和相同任务，
各自可有充分共享helper。comp的输入类型I不要求Fintype，可观测的有限和仅要求中间/输出载体有限，
不额外索取Nonempty、MeasurableSpace或可积性。Compare拟检验输出一致，防止任务被换掉。
不新增全局coercion，不把桥缺失义务变成用户输入，不从源码行数或占位数推断维护收益。
目前仅能说B路线有显式复用PMF.bind_bind的候选证明，不能说它降低了总责任。

## 匹配环境恢复后的确切入口

先按README解决已停止的网络准备动作；使用隔离Lean4.35.0及锁定Physlib/mathlib真实依赖，
真实构建上游Prob/Distribution/Channel闭包。不能指向旧4.34.1对象或只含摘录的目录。
将本目录下`UNVERIFIED_DRAFT`作为实验source root，独立对象目录加入LEAN_PATH；
依次对以下确切文件执行匹配`lean -o <独立对象路径> <文件>`，完整保存命令、源快照、版本、输出和exit：

1. `UNVERIFIED_DRAFT/PMFBridgeDraft/Bridge.lean`
2. `UNVERIFIED_DRAFT/PMFBridgeDraft/Native.lean`
3. `UNVERIFIED_DRAFT/PMFBridgeDraft/ViaPMF.lean`
4. `UNVERIFIED_DRAFT/PMFBridgeDraft/Compare.lean`

第一轮可仅诊断当前草稿，修复错误但保留原快照/失败；即使exit0，存在占位也必须标NOT_ACCEPTED。
接受前须消除全部五占位及任何新admission，重新编译、公理审计确认无sorryAx，核对完整公开类型和同任务消费者。
分别记录导入闭包构建、桥/往返、实数点值、消费者及公理审计，不将其代称独立kernel/全依赖认证。
本次不扩测度、方差或POVM分支；准备到此即止，不等待或轮询网络。

后续委托补记（2026-10-31）：用户另行选定[概率理论链](PROBABILITY-CHAIN.md)。该接续增加两份独立草稿，
不改变上述四文件/五占位快照或当时的工作范围；新来源和状态单独登记。
