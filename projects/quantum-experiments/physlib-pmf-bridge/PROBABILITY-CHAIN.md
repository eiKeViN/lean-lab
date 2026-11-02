# 固定输入的无记忆信道：乘积测度、独立性与加性评分方差

2026-10-31，用户另行选择的离线接续。**UNVERIFIED_DRAFT，未编译、未解析、未做公理检查。**
原946402f四文件/5个未完成项和此前403记录全部保留；本轮不是环境已恢复或验证成功。

## 两份必要草稿与责任边界

- [ChannelProduct.lean](UNVERIFIED_DRAFT/PMFBridgeDraft/ChannelProduct.lean)：
  `law d := (Bridge.toPMF d).toMeasure`；直接读取真实`DMChannel.on_fin`的点值，证明候选乘积测度等式，
  再调用`iIndepFun_pi`得到坐标独立。没有另造乘积分布来冒充原consumer。
- [ChannelStatistics.lean](UNVERIFIED_DRAFT/PMFBridgeDraft/ChannelStatistics.lean)：
  实数有限和积分观察；有限像的显式界`∑ o, ‖g o‖`提供`MemLp 2`；用`variance_sum_pi`得到加性评分方差公式。
  保留显式`MemLp`入口和从有限载体自行构造证书的入口，没有把目标独立性/方差公式当作输入或结构字段。

三层责任分别是：

1. **原PMF桥**：原`Bridge.toPMF`归一化B01仍未完成；本轮不重写原桥。
   新源码调用正向桥和它的点值，而不使用逆桥/结合律。设计上的调用链不需要B02/B03/N01/N02，
   但这些旧项仍存在，实际公理依赖须恢复后检查，不能从源码推断已经无sorryAx。
2. **本轮领域连接**：在有限O、给定可测空间且单点可测时，
   `law (C.on_fin I O is) = Measure.pi (fun k : Fin n => law (C.symb_dist (is k)))`。
   每个坐标的概率测度及sigma-finiteness由原生PMF实例导出，不是用户新增假设。
   同一有限载体的单点确定测度；单点等式归结为真实on_fin点值与非负有限乘积的ofReal公式。
3. **现有概率理论**：坐标独立直接用`iIndepFun_pi`；评分二阶可积性就地构造后用`variance_sum_pi`。
   这里新增可测/实值分析环境只服务测度消费者，不加强Physlib已有一般`expect_val`或`Mixable`。

## 精确范围与数学推演

输入串`is : Fin n → I`始终是**固定参数**。不要求I有限；O有限并具单点可测的可测结构，
这已足够使O上的任意实值评分可测。可选择离散可测结构，但本草稿不全局更换实例。
坐标分布可各不相同，不声称同分布。评分`g : Fin n → O → ℝ`任意，目标为

`Var[fun os => ∑ k, g k (os k); law (C.on_fin I O is)]`
`= ∑ k, Var[g k; law (C.symb_dist (is k))]`。

数学上，有限质量逐点相等给出测度相等；有限域上实函数可测且有有限界，因此二阶可积，
可以应用固定源码中的乘积独立性及方差定理。此推演支持路线和输入范围，**不是Lean接受证据**。
n=0不需默认输出元素；界采用非负范数和，也不要求额外Nonempty O。具体typeclass合成仍待编译。

**不可删去固定输入范围：**若两位随机输入都是同一个公平比特B，经过恒等确定性无记忆信道，
输出也都是B。于是`Var(Y₁+Y₂)=Var(2B)=1`，而`Var(Y₁)+Var(Y₂)=1/2`。
无记忆只规定给定输入下的乘积规则，不保证混合相关输入后仍无条件独立。此为数学控制，未另做Lean实验；
本轮不建立条件概率/随机输入理论。

## 固定源码核对与未核事项

本次只通过正常授权的GitHub只读connector读取mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`的
九份文本，未重试被停的官方Lean发布API、工具链下载或切换下载路径。完整文本和Apache许可证
保存在本地`results/source-review01/`，被Git忽略；`probability-chain-status.json`记录固定URL、
本地路径/哈希及声明位置。这些本地副本没有远端备份，hash本身不代表历史执行认证。

关键源码：

- `Measure/Dirac/Basic.lean:60`：`Measure.ext_of_singleton`，countable载体，需本节单点可测环境。
- `Constructions/Pi.lean:299–313`：`pi_singleton`需要坐标sigmafinite，概率乘积实例可导出；
  PMF `Basic.lean:332`的概率实例来自此前固定来源。
- `Basic/ENNReal/BigOperators.lean:63–66`：`ofReal_prod_of_nonneg`。
- `Probability/Independence/Basic.lean:889–906`：`iIndepFun_pi`的每坐标概率测度及观测AEMeasurable输入。
- `Probability/Moments/Variance.lean:449–462`：`variance_sum_pi`的每坐标`MemLp 2`输入；上游自己处理交叉项。
- `LpSeminorm/Basic.lean:631–633`：`MemLp.of_bound`；`MeasurableSpace/Basic.lean:293`：有限载体的函数可测。
- `PMF/Integrals.lean:27–49`：有限和积分接口的实Banach环境；本地仅用ℝ，不改一般Physlib期望。

尚未核查4.35.0的实际导出类型/实例合成，尤其是函数空间单点可测、PMF概率→sigmafinite、
真实`C.on_fin I O is`的显式参数/elaboration、rfl与simp匹配。`Finset.single_le_sum`依据固定源码
`single_le_prod`的`to_additive`生成规则，非本次读取编译后导出类型；`Finset.sum_apply`有固定Variance调用点。
这些调用均为待编译候选，不靠静态文本宣布成功。最初试读错误Pi路径返回404，已保存；随后按真实import找到
`Constructions/Pi.lean`，这是源路径纠正，不是工具链代理403的恢复或绕过。

## 原生有限和对照与当前能作的判断

原生前端已有归一化；直接证明评分方差可先做有限期望线性，再展开平方。
需以乘积权重的有限求和因子化证明不同坐标的混合二阶矩等于均值乘积，使协方差交叉项消失。
原生方案允许共享这些helper；本轮没有故意写一套重复概率库来制造差距。

桥路线的候选收益是复用已成体系的乘积测度、独立性和方差理论；实际新增责任是桥、
乘积测度识别、可测性/二阶可积性以及实数观察式。复用上游定理不使这些责任消失。
本轮没有匹配编译对照、工时/维护测量，不能据证明末行或源码长度声称净收益或独占能力。

## 恢复顺序与收束

先遵循原[环境停止记录](README.md#本次准备动作与阻塞)，不自行重试网络。
匹配环境恢复后保留原快照和失败，先诊断原Bridge及其B01，再按[DRAFT恢复入口](DRAFT.md#匹配环境恢复后的确切入口)的
独立source-root/对象路径方法，编译本次确切`ChannelProduct.lean`、`ChannelStatistics.lean`。
记录命令、pin、stdout/stderr、退出码、源码快照及公理；即便exit0也不得把传递的sorryAx当作接受。
接受须实际完成所用证明、核对签名和原生对象/实例，区别模块编译与独立kernel/完整依赖认证。

本轮新增两文件没有显式占位，但仍依赖原不完整Bridge，全部为UNVERIFIED_DRAFT。
当前六源码均无接受运行，原五项未完成保持；无push/merge/部署/正式库修改。到此结束，不轮询网络或扩其它分支。
