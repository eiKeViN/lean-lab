# lean-lab 量子实验区

返回 [lean-lab 多项目入口](../../README.md)。本区 Lean 4.35.0 与旧 KL 项目的 4.34.1 环境独立。

当前唯一活动 Lake 工作区是 **`pmf-environment/`**。全部活动 Lean 源码均已纳入 lean-lab 本地 Git，不以临时目录或 ZIP 作为唯一来源。

| 位置 | 用途 |
|---|---|
| `pmf-environment/lakefile.toml`、`lean-toolchain`、`lake-manifest.json` | 固定环境和三个 Lake 库入口 |
| `pmf-environment/Verified/PMFBridgeDraft/` | 六份已验证桥接源码；保留命名以维持原声明身份 |
| `pmf-environment/Comparison/PMFComparison/` | 强有限求和基线、共同观测定义、桥适配、协方差变更、同题接口 |
| `pmf-environment/Comparison/README.md` | 保留历史比较；最新口径见下方修正账本 |
| `pmf-environment/CostStudy20261102/` | 声明级成本拆分、受控计时及公开原始证据 |
| `pmf-environment/Frontend/` | 任务友好有限API、桥接证明、真实信道特例及三个领域客户端 |
| `physlib-pmf-bridge/UNVERIFIED_DRAFT/` | 旧原稿，只作为冻结历史，不能当活动库入口 |
| `physlib-pmf-bridge/` 其他文件 | 原计划和恢复历史，保留原文 |
| `pmf-environment/downloads/restore/original/` | 原始保全包内容与历史参考，保持本地原件 |
| `pmf-environment/logs/` | 可恢复验证记录；Git 忽略 |

首次使用请先在 `pmf-environment` 执行 `bash setup.sh`。之后运行 `bash check.sh` 会复用已有固定工具链，整体构建三个活动库及客户端、检查新模块、审计47新增及63历史声明，不追加性能计时。原始六文件的专门验证入口仍为 `pmf-environment/verify-proofs.py`。

固定 Lean 4.35.0，mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`，Physlib `c5a908ba7a1ee474063626bdf0470af006f9812e`。不修改仓库原有 KL 实验或其他研究项目。

发布目标：`eiKeViN/lean-lab` 的 `main`，路径保持为 `projects/quantum-experiments`。原实验分支与旧本地验收提交继续保留；公开复现使用随仓库发布的源码 SHA 基线，不依赖未发布提交对象或私人保全包。未迁入或修改 Alioth。

2026-11-02 发布补充：[有限方差声明级成本与受控编译时间](pmf-environment/CostStudy20261102/README.md)。
此补充保留原源码与报告，细分基础/消费者成本，并采用独立产物目录计时；原始数据随 `CostStudy20261102/evidence` 公开；不把历史计时当作新前端计时。

### 有限任务前端

[接口与验证报告](pmf-environment/Frontend/README.md) · [短客户端](pmf-environment/Frontend/FiniteProbability/Clients.lean)。在匹配 4.35.0 环境下验证，采用有限友好前端与桥接证明后端；支持任意有限索引，真实信道是特例；三个领域客户端已经编译，但不是生产采用证据，不表示整个仓库工具链已升级。

## 按证明角色阅读

下表的新前端命名空间前缀为 `QuantumExperiments.FiniteProbability`，旧原生对照为 `QuantumExperiments.PMFComparison.Finite`。推荐先看 `Scores` 的公开签名，再按需要读 `Moments` 后端；不要把旧目录名 `Verified/PMFBridgeDraft/Native.lean`（旧组合律对照）误当本次原生有限矩接口。

| 角色 | 文件入口与关键声明 | 关系 |
|---|---|---|
| 通用表示桥 | [Bridge.lean](pmf-environment/Verified/PMFBridgeDraft/Bridge.lean)：`PMFBridgeDraft.Bridge.toPMF`、`ofPMF` | 真实 Physlib 分布与 mathlib PMF；新前端继续复用 |
| 测度表示与观察API | [ChannelProduct.lean](pmf-environment/Verified/PMFBridgeDraft/ChannelProduct.lean)：`law`、`law_singleton`；[ChannelStatistics.lean](pmf-environment/Verified/PMFBridgeDraft/ChannelStatistics.lean)：`integral_real`、`score_memLp_two`；[Transport.lean](pmf-environment/Comparison/PMFComparison/Transport.lean)：`integral_eq_mean`、`variance_eq_finite` | 旧已验证观察层仍供新后端使用；旧文件也保留原信道方差证明 |
| 通用乘积连接与信道特例连接 | [Core.lean](pmf-environment/Frontend/FiniteProbability/Core.lean)：`product`、`law_product_eq_pi`、`coordinates_independent`、`on_fin_eq_product` | 新版任意有限索引；旧 `ChannelProduct.law_on_fin_eq_pi` 是固定 `Fin n` 信道版本，保留作历史与已有接口 |
| 有限友好的桥后端接口 | [Scores.lean](pmf-environment/Frontend/FiniteProbability/Scores.lean)：`productMean_*`、`productVariance_sum`、`productCovariance_sum`、`weighted_variance` | 推荐公开有限求和前端，隐藏表示与分析证书 |
| 内部通过桥复用理论 | [Moments.lean](pmf-environment/Frontend/FiniteProbability/Moments.lean)：`mean_product_prod`、`mean_product_coordinate`、`variance_sum`、`covariance_sum` | 实际调用 mathlib Fubini、边缘积分、方差理论；简明有限代数保留直接证明 |
| 信道下游与短客户端 | [Channel.lean](pmf-environment/Frontend/FiniteProbability/Channel.lean)：`mean_score_on_fin`、`cross_moment_on_fin`、`variance_on_fin`、`covariance_on_fin`；[Clients.lean](pmf-environment/Frontend/FiniteProbability/Clients.lean) | 通用理论特例化到真实固定输入信道；客户端展示计数均值、混合矩/诊断关联、加权方差预算 |
| 直接有限和原生接口及原消费者 | [Finite.lean](pmf-environment/Comparison/PMFComparison/Finite.lean)：`productMean_*`、`variance_on_fin`；[FiniteCovariance.lean](pmf-environment/Comparison/PMFComparison/FiniteCovariance.lean)：`covariance_on_fin` | 原生有限矩证明与方差/协方差消费者，未被删除或改成桥接实现 |
| 两路线同题契约 | [原 Contracts.lean](pmf-environment/Comparison/PMFComparison/Contracts.lean)：`VarianceClaim`、`CovarianceClaim`；[新 Contracts.lean](pmf-environment/Frontend/FiniteProbability/Contracts.lean)：`productMean_agrees`、`same_*` | 原对照及新前端对齐的实际编译检查；新契约只用于验收，不由公共入口导入原生证明 |

共同有限 `mean`、`variance`、`covariance` 定义在 [Comparison/Moments.lean](pmf-environment/Comparison/PMFComparison/Moments.lean)。新前端沿用这些定义，证明后端的改变不迫使调用者更换结果语言。新客户端是本地提出并编译的应用形态，不声称存在上游生产调用。
