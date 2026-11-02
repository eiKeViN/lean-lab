# Physlib ↔ PMF 桥与通道串接

2026-10-31，用户明确授权的本地隔离实验。当前状态：**环境准备被网络代理拒绝，实验NOT_RUN**。
已按后续委托保存[UNVERIFIED_DRAFT离线草稿](DRAFT.md)：真实imports、双向桥及原生/PMF通道对照，
有五个显式未完成证明项，全部源码未编译，不能作为验证结果。恢复顺序和精确文件见该页。
用户随后另选的[固定输入概率理论链](PROBABILITY-CHAIN.md)现增加两份未编译草稿：真实on_fin→乘积测度→独立性→实评分方差。
原五项未完成及403记录不改；新文件无显式占位也不表示接受或解除原Bridge的传递依赖。

## 2026-11-01：匹配环境恢复结果

按用户“先解决匹配版本环境”的新请求，只对原官方发布API作了一次同操作恢复尝试。
仍在代理CONNECT阶段返回`Tunnel connection failed: 403 Forbidden`，没有收到GitHub API响应，
没有下载asset或启动安装；本轮随后停止，未重试、换通道/执行器、改代理或创建凭据。
这不是平台自动审批拒绝或Lean失败，具体代理规则/是否暂态仍未知；不能靠再次确认安装授权解决。
完整错误、旧工具链的实际版本输出和命令回执在本地`results/prepare02/`，
固定pin、哈希、检查范围及恢复条件见[本次环境回执](environment-recovery-2026-11-01.json)。
现有二进制实际为Lean4.34.1，缓存mathlib为d13f23b；两者明确不符合本题目标。
匹配4.35.0版本查询、56a00585/Physlib依赖准备及最小import均NOT_RUN，不作环境验收通过。
需要当前环境网络/代理管理方允许原请求的`CONNECT api.github.com:443`，或提供已有的可核验匹配环境位置，
再据新的相关信息决定恢复；不盲目重复本次失败。原prepare01、六源码和旧缓存均不改，未push。

## 固定目标及已有证据

- Physlib：`c5a908ba7a1ee474063626bdf0470af006f9812e`。
- 配套 mathlib：`56a005855ea17e0b0958f73ec801ae140b0a1679`，Lean `v4.35.0`。
- 原始[实现前计划](https://github.com/eiKeViN/lean-library-quality-research/blob/98a6b804a911bac97327df961628e65fbf98155f/research/api-families/physlib-pmf-bridge/PLAN.md)、
  [源文件及环境记录](https://github.com/eiKeViN/lean-library-quality-research/tree/98a6b804a911bac97327df961628e65fbf98155f/experiments/physlib-pmf-bridge)
  保留在研究仓库，没有回填旧检查点或声称当时已获环境准备授权。
- 本地源证据目前仍位于`/workspace/lean-library-quality-research/experiments/physlib-pmf-bridge/upstream/`；
  它们只是原样选取的源码，不是完整依赖checkout，不能作为重写stand-in冒充真实集成。

实验目标不变：真实ProbDistribution双向桥、两观察式/两往返；原生有限sum/helper与PMF.bind路线
在相同DMChannel串接任务中比较，含实数有限和点值式及结合律。原生方案允许充分共享helper。
区分一次性桥责任、下游新增责任及无净收益；不以末行短证明当维护收益。
独立性/乘积测度仅为核心完成后有价值才选择的升级，不是本次必做。

## 本次准备动作与阻塞

1. 已读仓库规则，确认无重复Lean/lake构建，起始工作树干净。现成工具链仍只有已知4.34.1缓存。
2. 磁盘检查：32GB分区约23GB可用；没有开始大文件下载。
3. 官方发布元数据GET：`https://api.github.com/repos/leanprover/lean4/releases/tags/v4.35.0`。
   Python urllib在建立代理隧道时返回`Tunnel connection failed: 403 Forbidden`，exit1。
   原始错误保存在本地`results/prepare01/release-metadata.stderr`，命令及哈希见`preparation.json`。
4. 该动作已停止，没有重试、代理改设、镜像、不同访问路径或凭据动作。
   尚无release asset digest/下载结果，故未下载、解压、运行4.35.0、拉取依赖或获取官方缓存。

这是**网络准备阻塞**，不是Lean证明失败或自动审批拒绝。桥/消费者编译、公理、kernel、完整构建及runtime
均NOT_RUN；不能推出该桥不可行或已经简化证明。现有KL项目、旧缓存、量子正式接口和上游均未修改。

## 恢复入口

先由负责人解决对上述官方URL的网络访问或提供现有匹配环境位置，再决定恢复同一准备动作。
在没有新相关信息前不重复被拒访问，不另选路径。准备时使用独立`.cache/quantum/`版本目录，
核对官方asset digest、锁定Physlib/mathlib及其manifest依赖；只获取所需缓存，避免全库源码构建。
随后真实构建Prob/Distribution/Channel导入闭包，再按冻结计划实现桥和两个消费者路线，逐次保存源码快照、
完整stdout/stderr、退出码、命令/版本、对象来源及公理输出。不能将本次prepare01回填为接受实验。

当前仅本地分支/提交；无远端发布、PR或merge。原始日志本地保存且Git忽略，不能声称它们已被Git备份。
