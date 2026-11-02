# 有限任务前端，桥接证明后端（2026-11-02）

本阶段已通过实际 Lean 验证：47 个新增声明（含定义、观察桥、客户端与契约），并复查原有 63 个声明。公开入口为 `import FiniteProbability`。这是隔离实验中的新接口层，旧六文件、原生对照、冻结失败与成本研究均保留，没有迁移 Alioth。此源码及下述证据随本次 main 发布。

## 接口分层

| 模块 | 责任 | 调用者需要什么 |
| --- | --- | --- |
| `FiniteProbability.Core` | 真正的有限 `ProbDistribution` 乘积、与实际 `DMChannel.on_fin` 的连接、`law_product_eq_pi`、`coordinates_independent` | 表示层支持任意 `Fintype (ι → O)`；测度出口显式要求可测空间及可测单点 |
| `FiniteProbability.Moments` | 用 Fubini、边缘积分、乘积测度方差等理论证明有限矩性质 | 测度实例与二阶矩证书在证明内部提供 |
| `FiniteProbability.Scores` | 任务友好的 `productMean`、`productVariance`、`productCovariance` API | 仅有限索引、有限输出、分布族和实值评分；交叉矩要求不同坐标 |
| `FiniteProbability.Channel` | 实际 Physlib 固定输入信道的均值、混合矩、方差、协方差、加权方差 | `C`、固定输入 `is`、评分；不要求调用者编码成一般概率对象 |
| `FiniteProbability.Clients` | 三类领域任务的短客户端 | 只有领域数据和真正必要的领域假设 |
| `FiniteProbability.Contracts` | 与既有原生接口、既有方差/协方差契约对齐 | 仅验收导入原生证明；公开入口不导入该模块 |

**同一个有限前端可以有不同证明后端。** `productMean` 与既有原生定义逐定义相等，五个乘积均值/矩接口的参数顺序、结果形状和有限类型前提保持一致；`mean_center` 也一致。`Contracts.lean` 实际编译检查这组对应关系，而不是仅靠文字比较。

`Core` / `Moments` 的函数空间 `Fintype` 参数是 Physlib 表示层细节：其分布类型依赖枚举实例，不能随意把 `Fin n` 的实例换成另一个定义上不同的实例。`Scores` 在内部合成该实例，旧式有限求和公开签名不新增这一参数，也不新增 `DecidableEq`、可测、可积、`MemLp` 或非空前提。

## 已实现的公开任务接口

- 均值与混合矩：`productMean_prod`、`productMean_coordinate`、`productMean_pair`、`productMean_sum`、`productMean_sum_coordinate`、`mean_center`。
- 加性二阶矩：`productVariance_sum`、`productCovariance_sum`。
- 加权不确定性：`variance_scale`、`weighted_variance`；结果已经提取平方权重，便于继续做有限和不等式。
- 固定输入信道：`mean_on_fin`（导出原先只存在于局部证明的连接）、`mean_score_on_fin`、`cross_moment_on_fin`、`variance_on_fin`、`covariance_on_fin`、`weighted_variance_on_fin`。
- 需要一般概率接口时仍可显式使用 `law_product_eq_pi` 和 `coordinates_independent`，不把所有下游限制在有限求和语言。

此处均值、方差、协方差沿用 `QuantumExperiments.PMFComparison.Finite` 的既有定义，不加强 Physlib 的通用 expectation API。

## 三类客户端与证据范围

1. **固定输入的错误/告警计数均值**：`Clients.expected_flag_count`。给定 Bool 标记函数，预期标记总数等于各坐标边缘标记均值之和。客户端直接调用 `mean_score_on_fin`，没有测度转换。
2. **评分之间的关联**：`Clients.two_sensor_cross_moment` 用 `Bool` 索引实际验证并不局限于 `Fin n`；`Clients.diagnostic_covariance` 计算同一信道输出上两组总评分的协方差。不同坐标交叉项由乘积结构处理，同坐标协方差保留，未错误假设两个诊断独立。
3. **加权估计量的方差预算**：`Clients.weighted_uncertainty_budget`。若每项方差不超过 `v i`，则加权和方差不超过 `∑ i, w i ^ 2 * v i`。客户端用 `rw [weighted_variance]` 后直接接有限和不等式，检验结果可重写性与后续组合；无同分布、无偏、权重非零等额外条件。

方差/协方差原任务已有实际实验消费者；以上具体领域形态是本阶段提出并编译的客户端，不是发现了上游真实调用或生产采用。它们证明这些接口可用，不能据此声称一般最优、净维护收益或跨版本稳定性。

## 证明后端与保留的直接代数

- 乘积矩：`MeasureTheory.integral_fintype_prod_eq_prod`。
- 坐标均值：`MeasureTheory.integral_comp_eval`。
- 方差可加：`ProbabilityTheory.variance_sum_pi`，有限性推出的 `score_memLp_two` 在内部调用。
- 方差缩放：`ProbabilityTheory.variance_const_mul`。
- 坐标独立性：`ProbabilityTheory.iIndepFun_pi`。
- 协方差：复用方差可加与既有桥侧极化公式。

乘积分布归一化、有限均值线性性与中心化保留直接有限代数；异坐标混合矩用通用乘积矩做简单特例化。没有为宣传“全部桥接”而增加不必要的转换。`Dependencies.lean` 导出实际 elaborated 本地依赖和直接上游调用，验收脚本检查新路线没有回退调用原生有限矩/方差/协方差证明。

历史 `TransportCovariance` 的极化与观察引理仍被复用，没有复制整套桥接。旧模块不改名不删除，以保留历史成本与失败证据。新模块是推荐的实验公开入口，并非对上游 Physlib 的正式 API 变更。

## 实际验收与复现

在外层 `pmf-environment` 运行：

```bash
source env.sh
python3 Frontend/verify.py
```

`verify.py` 会核验：

- Lean 4.35.0；mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`；Physlib `c5a908ba7a1ee474063626bdf0470af006f9812e`，且依赖源码无已跟踪改动。
- 原冻结源及六份桥证明的 SHA；既有 `Verified`、`Comparison`、`CostStudy20261102`、`history` 由随仓库提供的 `preserved-source-sha256.json` 核对保留代码；导航与日期化发布补记允许更新。
- 整体 `lake build PMFBridgeDraft PMFComparison FiniteProbability FiniteProbability.Clients FiniteProbability.Contracts`，逐个新增源码重新 elaboration。
- 47 个新增声明的类型与公理闭包、旧 63 个声明的公理闭包；仅允许 `propext`、`Classical.choice`、`Quot.sound`，没有 `sorryAx` 或新公理。
- 实际证明依赖来源；全部命令、退出码及源码 SHA 写入日期化日志。

初次本地验收目录：`evidence/accepted-20261102T022029Z/`，`report.json` 为机器可读结果，所有命令退出码为 0。首次迭代失败亦保留：`core-01` 至 `core-04` 是函数空间枚举实例及有限和归一化转换；`moments-01` 是函数值和与逐点和的表达式匹配；`scores-01` 是加权函数需要显式特例化。后续成功日志保留，没有把失败重标为通过。旧的 module-system import 风格警告继续存在，未因此修改固定上游或旧证据。

范围边界：有限、同一种输出类型 `O`、实值评分；信道输入固定。没有异质坐标类型、无限空间推广或相关随机输入下无条件独立的结论。本轮没有新计时、升级或长期维护实验；不重用历史计时作为新接口的性能结果。

发布复验与浅克隆支持：`verify.py` 使用随仓库提供的源码SHA清单，不要求本地历史Git对象。原验收目录保留，新发布验收由 `evidence/latest.txt` 指向；不将本次验收描述为新性能计时。

本次发布布局的复验：`evidence/accepted-20261102T023701Z/`，47新增及63历史声明检查通过。公开保全清单含31个既有代码/证据文件；根导航、量子索引和原报告的日期化补记已同步更新。
