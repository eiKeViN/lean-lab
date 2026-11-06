# 恢复交接

2026-11-06。用户已明确允许开始 Lean 实验和验证；上一轮禁止编译的暂停对本次实验已解除。当前范围是 `experiments/measurement-api`，分支 `experiment/measurement-api-20261106`，基于 lean-lab 主分支 e4c76a7。原工作目录 `/workspace/lean-lab` 的 work/f43b964 保留，其他实验未修改。

先读 README.md、MeasurementAPI/*.lean、Contracts/*.lean。已完成 Physlib POVM 搬运/粗粒化/二元观察、复用旧桥的 PMF 推前、归一化 Kraus 族的概率视图；完整 HypothesisTesting 文件前后版本编译通过。其 Ref81Lem5 的签名与公理集合一致。过程反例证明两个归一化 Kraus 族同 POVM/同概率但总信道及在指定态上的输出不同。

固定 Lean 4.35.0、mathlib 56a0058、Physlib c5a908b。`scripts/setup.sh` 已实际运行成功；它用自己的 Lake 配置和官方目标缓存。旧 PMF 桥仅通过本目录的模块可见性适配接入，未修改原桥。`scripts/check.sh --record` 保存实际验收；普通 check 不改写冻结证据。

验收检查 26 个 API 声明、20 个命名契约、两个完整消费者、源码身份前后核对和实际打印公理。仅标准的 propext/Classical.choice/Quot.sound。82 个 Physlib 文件的身份覆盖与 55 个实际依赖模块的编译覆盖分开报告。完整日志、下载、依赖和编译产物均忽略；必要诊断及哈希在 evidence/。

保持已核实的远端目标 eiKeViN/lean-lab；只发布此实验分支，不合并、联系上游或部署 CI/bot/服务。QIT instrument 草案不是本轮已验证成果。继续扩展前先结合实际客户选择范围，不把静态草案或旧验收记录当作本轮编译证据。
