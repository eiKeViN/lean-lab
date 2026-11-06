# 独立评审及整改

初步原型经过一次不继承原讨论的独立评审。评审者先检查代码差异与调用点，再读说明，并独立运行 Lean 探针及前后隔离验证。总体判断是数学与运算实例成立，下游便利度有实际依据；建议集中在通用生成元接口和搬运规律。

| 评审或后续设计问题 | 本轮处理 | 可核查证据 |
| --- | --- | --- |
| 组合满射性只存在于矩阵 presentation | 为所有有限 presentation 提供系数线性映射、加法/负元/单生成元公式和满射；矩阵满射定理成为特化 | `BinaryBridge.lean`；workflow 的非矩阵构造、重复生成元关系及关系空间维数 |
| 系数映射展开后仍应能自动化简加法 | 将组合的加法公式加入 `simp`，检查线性映射与乘法组合两种写法的 `by simp` | `PublicTypes.lean` |
| 搬运与重编号缺少恒等、复合、逆变换规律 | 在 Pauli、码、稳定子、presentation 层统一提供；用命名等价集中处理依赖载体对齐 | `Transport.lean`、`Reindex.lean`；workflow 的连续重编号与撤销 |
| `C.prod` 与 `P.prod` 的默认返回层级不同 | 统一为 typed stabilizer，提供显式 `C.prodPauli` | `Interface.lean`、`PublicTypes.lean`、workflow 的乘积交换 |
| `toUnitary (ofMem …)` 裸 `simp` 无法还原 | 补充命名 `[simp]` 入口 | workflow 中相应 `by simp` 示例 |
| 否定实例测试可能把超时当作“无实例” | 删除 `fail_if_success` 通过性探针；独立记录有界搜索结果 | `scripts/profile_instances.py` 和 `evidence/instance-outcomes.json` |
| 是否真正支持一条完整使用链 | 以共同固定态构造 presentation，分析系数核，重排生成元与 qubits，再复用码距 | `Examples/PresentationWorkflow.lean` |

边界与验证范围：初步评审的结论只对应当时原型；整改后的构建、类型、源码身份与对照记录在验收文件中。该记录不替代全仓库或跨版本性能测试。负向搜索的资源限制结果不证明搜索空间已穷尽。兼容性与非计算性说明集中在 README 末尾。
