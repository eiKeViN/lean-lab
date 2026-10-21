# 单一维护项目收敛（2026-10-21）

起点是已发布并核实的 `85b3d1a4fa9c4f08beb718d8925d2d0ec9c50060`，
仍使用 `codex/kl-semantic-architecture` 分支。不合并 main，不改变权限或
保存的云环境设置。此次没有修改数学内容、类型、Lean 检查示例或抽取新接口。

## 删除与保留

删除四个工作目录：

- `experiments/kl`
- `experiments/kl-signed-ranks`
- `experiments/kl-kernel-transport`
- `experiments/kl-architecture`

唯一维护目标仍为 `experiments/kl-for-mathlib`，路径没有变化。其 230 个 Lean
产品模块、168 个候选模块、23 个项目数学模块与一个 kernel 包装保持原样；
36 个兼容 import 入口继续保留。没有创建另一份实验或基线工作副本。

所有历史提交、原始 34-blob upstream manifest、许可证、challenge/comparator
参考文本和已提交的构建/类型/公理证据保留。以前报告按历史记录保留；当前
命令从 root README 获取，历史源码路径用固定 Git 提交解析。

整个当前项目的 **239 个 `.lean` 文件（含行为/导入/公理检查）与 85b3d1a
逐字节相同**，文件集合也相同。独立 blob 清单见
`reports/evidence/consolidation-lean-identity.json`。工作树删除不改写 Git 历史，
也不声称 Git 对象存储体积缩小。

## 基线没有随旧目录消失

`provenance/baselines.json` 固定了四种历史树：

| 用途 | Git 提交与历史前缀 |
| --- | --- |
| pristine 原始源文件 | `7ddc53ba8a09ed902fefff86e67a87217518c1d4:experiments/kl` |
| 525 个迁移单元的直接来源 | `7ddc53ba8a09ed902fefff86e67a87217518c1d4:experiments/kl-kernel-transport` |
| 已审阅的比较/覆盖政策 | `2b5287954bd3c16015d9aab10dc3331d61065926:experiments/kl-architecture` |
| 本轮前已发布的项目与 lockfile | `85b3d1a4fa9c4f08beb718d8925d2d0ec9c50060:experiments/kl-for-mathlib` |

新 `scripts/baseline.py` 读取 Git 对象并核对 blob SHA，不恢复旧 checkout，
不执行旧 lakefile。原 34 个源 blob 继续与独立 upstream manifest 比较；
迁移单元、名字注记、完整覆盖算法和固定声明数继续受检查。source_check
只替换读取来源的 I/O，静态检查按历史源码精确构造并验证这个机械适配。

另外保留已经通过独立导出比较的完整参考 DAG：
`provenance/kl-reference-types.tsv.gz`。原数据 16922969 字节，压缩后 2998718
字节；压缩/解压后 SHA-256、长度、导出器哈希和捕获依据都绑定在 JSON 中。
每次检查重新验证完整性、解析完整 footer/记录并比较全部 3902 个类型。
这不是仅相信一条旧 passed 标记，也不是将新数据与自己比较。

原 `--refresh-reference` 所依赖的历史 Lean 工作项目已退休。当前基线检查
是**重放固定、已验证的导出证据**，不声称重新 elaboration 了历史证明。
当前库仍单独进行 artifact/build 就绪、实际导入、类型导出、行为和公理检查。
`--verify-baseline` 提供不运行 Lean 的基线/来源检查；不静默冒充旧选项。

普通检查不访问网络来补历史；缺失对象会明确失败。setup 才会在 shallow clone
缺少固定提交时获取它们，不改分支或重建实验。源码 ZIP 如果不带 `.git`，
不能单独完成这一来源核验；请使用 Git clone 或完整 Git bundle。获授权的
未来 baseline/API 变更需要显式更新政策和证据，而不是删检查或新建实验。

## 单一入口与缓存

```bash
bash scripts/setup.sh
bash scripts/check.sh          # 完整检查
bash scripts/check.sh warm     # 要求所有 artifact 已就绪，完整复验
bash scripts/check.sh static   # 不运行 Lean 的结构与基线检查
bash scripts/check.sh smoke
```

直接项目入口保持 `bash experiments/kl-for-mathlib/check.sh`。旧 `kl`/`build`
命令名作为完整检查的别名，`audit` 作为 warm 完整检查的别名；不再指向已删
目录。root/project README、AGENTS、provenance 和历史报告索引同步更新。

物理依赖目录从旧 `kl/.lake/packages` 移到当前项目的 `.lake/packages`，
不再是指向旧项目的符号链接。当前 manifest 与已发布 baseline 的完整字节
比较，所有已安装依赖的 Git rev 和脏改动检查继续执行。旧项目的构建缓存
移除，当前工作产物、Lean 安装和 Mathlib 下载缓存保留。

移动后实际执行 cache-only 预检：Mathlib 8923 jobs、本库 9155 jobs 均显示
all targets up-to-date。setup 复用已有 Lean 4.34.1 与 Lake 5.0.0-src+5045d00，
Mathlib 为 `d13f23b723b8a846827a245b89c10fc7d3f11612`，跳过网络 cache 访问。
没有重编长 stalk/pairing，也没有 Mathlib 全源码构建。

## 验证结果与范围

实际执行 `bash scripts/setup.sh`、`bash scripts/check.sh smoke consolidation-smoke`
和 `bash scripts/check.sh warm`，均完成。smoke 的真实退出码为 0，耗时 1.263 秒。
完整 warm 验收的 20 个阶段全部退出 0：

| 检查 | 结果 |
| --- | --- |
| 原始 34 blobs、工具链、lockfile 和可用依赖 rev | 通过 |
| 固定导出 archive 校验、解压、完整解析、baseline snapshot 对照 | 3902 项通过 |
| 525 个单元的一一分配、34 文件 35871 非注释行覆盖 | 通过 |
| 构建/cache-only 就绪与 warm build | 通过，未发生长源码重建 |
| 候选、通用对象和领域独立导入 | 全部通过；ForMathlib→项目反向依赖仍为 0 |
| kernel、兼容与 signed boundary 行为 | 全部通过 |
| 公理闭包 | 精确覆盖原 16 个命名目标；主定理仍恰为 propext、Classical.choice、Quot.sound |
| 当前公开类型导出与对照 | 3902→3902，无缺失、新增或规范化类型变化 |
| 比较器反例测试 | 原 31 项通过，政策未改 |
| 离线清理/失败路径测试 | 新 18 项，普通 Python 与 PYTHONOPTIMIZE=1 均通过 |

18 项测试覆盖 Git 历史缺失/路径越界、源 blob/缺项、工具链与非 Mathlib
依赖 pin 错误、旧依赖符号链接、参考 archive 损坏/错误内容 hash/计数，
以及空/缺失/重复/替换公理目标、额外公理和 cache 失败传播。公理检查由
原先只核对数量，进一步要求恰好原 16 个不同名字；没有减少目标或测试。

本轮不是 cold build 性能比较，也没有重新安装全部依赖。源码身份、历史证据
重放、当前编译缓存、类型和公理是不同证据；不据此独立认证原始数学范围。
以下是实际阶段 wall time，完整命令、CPU/RSS 和退出码保存到 evidence：

| 阶段 | Wall 秒 | 退出码 |
| --- | ---: | ---: |
| `baseline-identity` | 0.474 | 0 |
| `baseline-export` | 0.133 | 0 |
| `baseline-snapshot-check` | 2.532 | 0 |
| `source-transport` | 0.584 | 0 |
| `source-coverage` | 0.439 | 0 |
| `classification-and-boundaries` | 0.046 | 0 |
| `lean-version` | 0.743 | 0 |
| `mathlib-ready` | 3.328 | 0 |
| `oai-ready` | 4.501 | 0 |
| `ForMathlibChecks` | 5.288 | 0 |
| `ImportChecks` | 4.138 | 0 |
| `DomainImportChecks` | 4.067 | 0 |
| `KernelChecks` | 4.871 | 0 |
| `CompatChecks` | 4.606 | 0 |
| `BoundaryChecks` | 5.283 | 0 |
| `Audit` | 3.996 | 0 |
| `migrated-types` | 11.560 | 0 |
| `type-comparison` | 2.618 | 0 |
| `comparator-tests` | 0.083 | 0 |
| `warm-build` | 4.436 | 0 |

`reports/evidence/consolidation-*` 保存本轮记录；之前已发布的 evidence 未被覆盖。
没有新增 CI workflow 或保护规则，也不将本地结果称为 GitHub CI 通过。
新分支 head 与远端检查状态以本轮最终发布回读为准。所有操作仅限 lean-lab。

本轮未重复空缓存安装，也没有实际触发 shallow clone 缺失历史时的网络 fetch
分支（本地固定对象已齐备）；验证的是已保存环境中的迁移与暖启动路径。
这些未执行路径不记为通过或新的历史证明重编译。
