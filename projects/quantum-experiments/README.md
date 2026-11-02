# lean-lab 量子实验区

当前唯一活动 Lake 工作区是 **`pmf-environment/`**。全部活动 Lean 源码均已纳入 lean-lab 本地 Git，不以临时目录或 ZIP 作为唯一来源。

| 位置 | 用途 |
|---|---|
| `pmf-environment/lakefile.toml`、`lean-toolchain`、`lake-manifest.json` | 固定环境和两个 Lake 库入口 |
| `pmf-environment/Verified/PMFBridgeDraft/` | 六份已验证桥接源码；保留命名以维持原声明身份 |
| `pmf-environment/Comparison/PMFComparison/` | 强有限求和基线、共同观测定义、桥适配、协方差变更、同题接口 |
| `pmf-environment/Comparison/README.md` | 有界公平比较结果、实际成本与限制 |
| `physlib-pmf-bridge/UNVERIFIED_DRAFT/` | 旧原稿，只作为冻结历史，不能当活动库入口 |
| `physlib-pmf-bridge/` 其他文件 | 原计划和恢复历史，保留原文 |
| `pmf-environment/downloads/restore/original/` | 原始保全包内容与历史参考，保持本地原件 |
| `pmf-environment/logs/` | 可恢复验证记录；Git 忽略 |

首次使用请先在 `pmf-environment` 执行 `bash setup.sh`。之后运行 `bash check.sh` 会复用已有固定工具链，整体构建两个活动库、检查新模块、审计全部63声明并做两轮有限增量计时。原始六文件的专门验证入口仍为 `pmf-environment/verify-proofs.py`。

固定 Lean 4.35.0，mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`，Physlib `c5a908ba7a1ee474063626bdf0470af006f9812e`。不修改仓库原有 KL 实验或其他研究项目。

发布目标：`eiKeViN/lean-lab` 的 `main`，路径保持为 `projects/quantum-experiments`。原实验分支与旧本地验收提交继续保留；公开复现使用随仓库发布的源码 SHA 基线，不依赖未发布提交对象或私人保全包。未迁入或修改 Alioth。
