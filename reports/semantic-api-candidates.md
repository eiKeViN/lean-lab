# Semantic API 实验：候选与环境检查点

状态：候选与实现范围已确定，完整验收正在运行；本提交只归档进度，不是代码验收结论。

- 起点：已合并 main `178ccf2a9fa1f0bff04d6b029db1361f881fef33`。
- 分支：`experiment/semantic-api-20261024`，不创建 PR、不合并、不修改 main。
- 已读根 AGENTS.md、项目说明及 module-completion/module-interface-decisions 等既有研究。
- 工作区 .agents 为空，仓库没有附加技能文件。
- 初始环境没有 Lean、项目 .lake 或依赖缓存；标准 setup 已成功安装精确 Lean 4.34.1 / 5045d005，
  并取回 Mathlib d13f23b7 的官方缓存，没有全编 Mathlib。
- 唯一维护项目仍为 experiments/kl-for-mathlib；没有另建维护项目。

| 候选 | 真正下游 | 本轮 API 与边界设计 |
| --- | --- | --- |
| LocalCover.splitEquiv | 局部最小覆盖、graded splitting、kernel 自由性 | 三个坐标/逆向公式；保留已有公开 rfl 契约，另做隐藏对照 |
| CoefficientChange.map | graded changeHom、mapEquiv、配对与 changeTop_split | val_map、map_id_apply；小客户端隐藏验证通过，但 GradedSheaf.Duality 仍有多处直接归约依赖，交付保留透明 |
| Sheaf.quotientPullback | tensor/pi 自然性与 structureBaseChangeIso | 逐点取值公式；尝试隐藏，显式比较 producer 衔接成本 |
| Sheaf.baseChangeQuotient | structure sheaf 边模 base change | 复用已有纯张量公式，不添重复规则；尝试隐藏 |

目前共六条新增定理、七个生产/客户端文件。已有 ext/val/equivVal 复用，不加 casesOn 包装。
两个 quotient 定义保留隐藏候选；split/map 与 wrapper/module 实例保持透明。
六项新声明和七文件精确源码将分别受有界门禁约束，不全局放宽冻结源码或新增声明检查。

当前命令为 `lake build ForMathlib OAI`，正在编译 OAI/KL/BottSamelson/UpperSections.lean。
环境无阻塞；该文件既有验收 job 曾记录948秒（含排队）。完成后继续普通 modern import、
真实 producer/client 隔离隐藏对照、完整类型/公理及项目门禁。尚无最终通过声明。

最终实现、详细前后比较与实测证据将归入本分支的 `reports/semantic-api-experiment.md`。
