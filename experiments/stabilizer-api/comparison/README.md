# 原始接口与当前接口的独立编译对照

旧版为 Lean-QEC `8d115519b471b71a21fbdddf5341d8203b841cc9`，新版为本实验固定 overlay。两侧使用相同 Lean 与 Mathlib 依赖。

| 任务 | 旧侧 | 新侧 |
| --- | --- | --- |
| 构造码 | 额外传入交换性字段 | 从排除 `−I` 推出交换性 |
| 环境成员交换 | 安装 `C.h_comm`，再调用通用成员引理 | `C.mul_comm` |
| 有限乘积 | 用户局部配置交换群结构 | `C.Stabilizer` 自动提供 |
| 生成元与 codespace/normalizer | 分别传 `g` 与 `hgen`，转换闭包/谓词 | `P.mem_space_iff`、`P.mem_normalizer_iff` |
| 矩阵二元像 | 已有一行证明 | presentation 入口同样一行 |
| 二元恢复 | 选择存在性见证并证明规格、往返 | `C.ofBinary`、`simp` |
| 二元线性维数 | 用户先组装群等价、模结构与线性等价 | `C.binaryLinearEquiv.finrank_eq` |
| 搬运码与码距 | 用户补充相应基础设施 | 公开的 map/reindex 及组合规律 |

- [Before.lean](before/Before.lean)：常见旧侧写法。
- [BeforeLinear.lean](before/BeforeLinear.lean)：用户组装线性桥的完整示范。
- [UserReindex.lean](before/UserReindex.lean)、[BeforeTransport.lean](before/BeforeTransport.lean)：旧侧用户为同等任务补的重编号与码距理论。
- [After.lean](after/After.lean)：对应新侧调用。
- [verify.py](verify.py)：核查固定旧源码字节和当前 overlay，分别编译两侧。

完整集成检查会运行这组对照，也可在准备好环境后直接运行 `python3 comparison/verify.py environment`。

比较口径与验证边界：旧侧是基于原 API 新写的可编译示范，复用了已有闭包、二元像与单射性结果。辅助代码和局部配置按建立一次后复用理解；不把演示行数当作最短实现下界。`g + hgen` 与 `P` 承担相同数学信息。原始矩阵公式只要求交换性，presentation 公式面向合法码；原定理仍保留。完整 workflow 的新增通用系数映射与变换组合规律由主验收检查，不把旧侧额外代码伪装成原有上游声明。非计算性、公理依赖、定向构建范围见主 README 末尾。
