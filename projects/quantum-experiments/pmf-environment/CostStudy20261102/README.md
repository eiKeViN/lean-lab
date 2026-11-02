# 2026-11-02：有限方差的声明级成本与受控编译时间

> 发布补记：本研究及新有限前端随本次 lean-lab main 发布。原始成功计时与失败日志已保存在 [evidence](evidence/README.md)，无需私人包或本机 logs 目录即可读取。以下“仅本地提交”描述保留为原研究阶段状态；本次发布不重跑或改写这些计时。


这份补充修正此前文件级账本容易产生的解释：**185 行不是全部可免费复用的基础，其中已经包含当前方差目标；85 行也不是全部消费者专属证明，其中有大量共享矩引理。** 原报告、代码与旧计时不改。下述比较不预设某条路线胜出。

在同一口径下，当前必要本地声明总量为原生 **78 行**、桥侧 **76 行**，共同定义另4行。若双方相应基础已存在、但都尚未预付聚合方差核心，增量是 **31 对26行**；这支持“该明确起点下桥侧略短”，不支持24对85的节省说法。若原生更丰富的矩库连中心平方和核心也已具备，其增量则是17行，结论随起点改变。

## 数学对象与口径

对象仍是实际 Physlib `DMChannel.on_fin`、固定 `is : Fin n → I`、任意实评分 `g`，终点是同一个有限中心方差等式。没有添加 `Fintype I`、`Nonempty O` 或外部可测前提，也没有改变原生强基线。原 `Contracts.VarianceClaim` 的两路线接口保留；测量副本又分别通过完全相同表达式的合同检查。

本次按**声明正文的非空非注释行**计数，包含签名、属性和证明，排除 imports、namespace、section变量与end。不能与原报告含这些结构行的185/85/24直接加减。逐声明来源、正文SHA、类别与数字由 `generate.py` 提取，见 `accounting.json`。代码行只表示当前实现体积，不是作者工时、最短证明、抽象质量或维护时间。

### 共同成本

`Finite.mean` 2行、`Finite.variance` 2行，共4行。共同上游 Physlib/mathlib 理论以及同题验收工具不偏计给任一路线。协方差不是本轮目标，不计入该共同定义切片。

### 原生路线：78行／9声明

| 职责 | 声明（统一前缀 `QuantumExperiments.PMFComparison.Finite`） | 行数 |
|---|---|---:|
| 通用乘积加权观察 | `productMean` | 4 |
| 中心化均值 | `mean_center` | 4 |
| 乘积求和因子化 | `productMean_prod` | 8 |
| 单坐标观察 | `productMean_coordinate` | 5 |
| 异坐标二阶矩 | `productMean_pair` | 16 |
| 求和线性 | `productMean_sum` | 5 |
| 坐标均值求和 | `productMean_sum_coordinate` | 5 |
| 聚合二阶矩核心 | `productMean_centered_sum_sq` | 14 |
| 真实信道方差连接 | `variance_on_fin` | 17 |

前七项合计47行，是可复用基础。`productMean_centered_sum_sq` 也可复用到任意有限索引，但它实际承担展开平方与消除交叉项的核心工作；主增量场景把这14行与最后17行一起计费，不仅因其叫helper就免费。

### 桥路线：76行／16声明

以下 `Bridge`、`ChannelProduct`、`ChannelStatistics` 位于 `QuantumExperiments.PMFBridgeDraft`，`Transport` 位于 `QuantumExperiments.PMFComparison`。

| 职责 | 声明 | 行数 |
|---|---|---:|
| 通用表示桥 | `Bridge.toPMF`、`toPMF_apply`、`toPMF_toReal` | 4+2+4 |
| 通用测度表示 | `ChannelProduct.law`、`law_probability`、`law_singleton` | 2+4+5 |
| 信道领域连接 | `ChannelProduct.on_fin_real_apply`、`law_on_fin_eq_pi` | 2+10 |
| 通用积分观察 | `ChannelStatistics.integral_real` | 4 |
| 有限二阶矩证书 | `ChannelStatistics.score_memLp_two` | 6 |
| 通用有限终点观察 | `Transport.integral_eq_mean`、`variance_eq_finite` | 2+5 |
| 消费者记号 | `ChannelStatistics.totalScore` | 1 |
| 当前方差目标 | `ChannelStatistics.variance_totalScore_of_memLp` | 11 |
| 自动给证书的目标包装 | `ChannelStatistics.variance_totalScore` | 6 |
| 当前有限终点连接 | `Transport.variance_on_fin` | 8 |

前三个通用表示/观察组及领域/矩基础合计50行，消费者合计26行。`variance_totalScore_of_memLp` 的对象和结论就是当前信道方差任务；它不能因为先前写好就归为“免费通用桥”。`variance_eq_finite` 则适用于任意有限分布与评分，可以合理放入通用观察基础，但从共同上游开始时仍需计费。

`law_on_fin_eq_pi` 是可复用于多个消费者的信道领域基础；场景二假设它已具备，是一个明确的业务/库起点，而不是所有项目天然已有的事实。

### 不应进入本目标必要成本的资产

- Bridge：`ofPMF`、`ofPMF_apply`、`ofPMF_toPMF`、`toPMF_ofPMF`、`equiv`、`toPMF_injective`、`pmf_bind_toReal`。
- ViaPMF：`bind`、`toPMF_bind`、`bind_apply`、`bind_assoc`、`comp`、`comp_apply`、`comp_assoc` 全部。
- `ChannelProduct.coordinates_iIndepFun` 有独立价值，但本地方差链直接调用上游 `variance_sum_pi`，不调用这条本地独立性定理。
- 协方差扩展、旧原生bind和路线相等检查不是当前方差首次证明。

这些代码仍保留；这里只是从当前必要依赖切片中剔除，不否定它们的成本或用途。

## 起点敏感性

| 假设起点 | 原生需新增 | 桥侧需新增 | 解释 |
|---|---:|---:|---|
| 共同上游已有，所有必要本地声明从零计入 | 78行/9声明 | 76行/16声明 | 加上共同4行后是82对80；总体体积接近 |
| 各自基础已存在，聚合方差核心尚未预付 | 31行/2声明 | 26行/4声明 | 预存基础分别47/50行；本次计时采用此切分 |
| 更丰富原生矩库已含中心平方和核心 | 17行/1声明 | 26行/4声明 | 边界敏感性，未另作计时；不是双方同等基础必然存在 |

因此，用户“复用之后可能省”的直觉可以在明确起点下成立，但先前185行里已有的方差目标不能一并扣除。主增量账只差5行，不能由此推出明显开发或维护优势。未来哪个基础已经存在，应由真实应用决定。

## 编译时间：受控本地 `.olean` 构建

### 设计和隔离

测量固定在同一容器、Lean4.35.0及既有两个依赖SHA，串行运行，无本任务其他并行编译。未绑定CPU核心、未隔离宿主其他负载；三次样本不用于显著性或普遍速度判断。

为避免原文件拆分不对称，生成五个测量模块：

- `Common`：两路线所需上游import的并集，以及共同mean/variance；预先编译一次，耗时1.842秒，双方共用。
- `NativeBase`：47行基础；`NativeConsumer`：中心平方和核心＋真实信道方差，共31行。
- `BridgeBase`：50行基础；`BridgeConsumer`：totalScore、两个方差目标和有限终点连接，共26行。

声明名、前提和证明步骤保留，正文直接从公开源码提取。27个相关声明在原版、拆分版和编辑版中，公开Lean表达式经仅规范化binder名称、universe参数拼写、metadata后完全相同；不是只比较打印文字或数学摘要。目标公理闭包只含 `propext`、`Classical.choice`、`Quot.sound`。共同import并集可能影响simp/instance搜索的证明项，所以只主张声明语义一致，不声称所有证明项逐字相同。

所有输出都新建于 `logs/cost-20261102/`，没有删旧证据、共享缓存或生产产物。缓存基础对象仅复制到本轮自有输出目录；原项目 `.lake/build/lib/lean` 从测量副本的搜索路径中移除，上游依赖只读。

调用是直接 `lean <module>.lean -o <isolated>.olean`，包含进程启动、导入、elaboration及olean写出；不是Lake调度或C/可执行文件链接测量。标准化共同import负载有意排除了原始布局的导入差异，不能将本表当成原始文件布局的完整构建wall time。上游和OS页缓存是热的；“冷”仅指指定路线自有产物不存在。不包含下载、安装或完整mathlib源码构建。

### 三种状态

1. **路线自有产物冷**：共同上游/Common已缓存；新目录只有Common，依次构建Base→Consumer。总时长是两次串行编译之和，也就是本设计的关键路径。
2. **基础已缓存，消费者产物冷**：已有Base复制入隔离目录，Consumer尚不存在，仅编译Consumer。
3. **消费者修改后的受控增量**：先有基础和原消费者对象，对最后的 `variance_on_fin` 证明体作同类型重构，包装为 `exact (by …原证明…)`；输入源码SHA改变，只重建Consumer，输出文件实际更新且基础SHA不变。编辑后的27类型和公理重新检查通过。这是实际源码修改与重建，但只是受控证明体重构，不是新数学结论、跨版本升级、长期维护样本或Lake自动失效传播测试。

三轮交错顺序记录在脚本与原始日志中；第二轮反转路线和场景顺序。构建前检查和基础预备在计时样本之外另记。

### 原始值与汇总（秒）

| 状态 | 路线 | 三次原始值 | 中位数 | 范围 |
|---|---|---|---:|---|
| 路线产物冷 | 原生 | 4.068, 4.216, 4.030 | 4.068 | 4.030–4.216 |
| 路线产物冷 | 桥 | 3.903, 4.195, 3.885 | 3.903 | 3.885–4.195 |
| 基础缓存/消费者冷 | 原生 | 2.242, 2.163, 2.039 | 2.163 | 2.039–2.242 |
| 基础缓存/消费者冷 | 桥 | 1.922, 1.920, 1.850 | 1.920 | 1.850–1.922 |
| 证明体修改/重建 | 原生 | 2.305, 2.087, 2.063 | 2.087 | 2.063–2.305 |
| 证明体修改/重建 | 桥 | 2.138, 1.938, 1.957 | 1.957 | 1.938–2.138 |

路线冷样本的模块分解：原生Base为2.013/2.203/1.958秒、Consumer为2.055/2.014/2.071秒；桥Base为1.926/2.122/1.834秒、Consumer为1.977/2.073/2.051秒。原始值保留更高精度及子进程CPU时间。

18个计时区间累计48.920秒；commands.json中记录的编译/审计进程（含预备、合同与类型/公理导出）wall time累计69.684秒。这不是作者工时，也不是包含Python全部调度开销的端到端总时长。

本次受控条件下桥侧三个中位数均略低；首次路线构建和编辑重建的范围有重叠。不能由三次小样本宣布统计显著性或长期优势。也不能拿这里的Consumer样本去替代旧报告的原布局叶文件计时；两种口径单独保留。

## 复现、证据与未测项

从 `pmf-environment` 运行：

```bash
source env.sh
python3 CostStudy20261102/generate.py
python3 CostStudy20261102/run.py
```

需要已有固定上游缓存及原活动库对象，用于原版类型比对；从公开仓库按其setup说明准备后先 `lake build PMFBridgeDraft PMFComparison` 即可。脚本只生成/使用本轮自有产物，不执行清缓存操作。测量副本保留原声明名称，因此只通过独立输出脚本编译，不加入主Lake库或与原模块同时import。

成功记录：`logs/cost-20261102/run-20261102T014237719601Z/`。`report.json` 含类型一致断言、27项公理、环境、完整命令、源/产物SHA及原始计时；`cases.json` 与逐命令日志保留各状态、关键路径、编辑前后产物信息。报告SHA-256为 `c512cc9ae275f68611c0d64ace62fafbc998192ed121bd2414513c0f5fef054a`。

初次测量框架尝试因Lean同名顶层模块目录的搜索路径选择找不到Common而失败（`run-20261102T014147105311Z`）；后来改为将本轮基础对象复制到各自完整的隔离模块目录，不改数学证明、不清共享目录。失败记录保留，不纳入成功样本。

没有运行全依赖全冷安装/源码构建、原始不对称模块布局的冷构建、Lake自动重建行为、核心绑定性能试验、独立全依赖kernel重放或新数学消费者。原源码、原报告、原失败和旧计时保留。本轮仅本地提交，不推送任何远端或修改Alioth；完成本次核算后停止。
