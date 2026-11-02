# PMF 桥接与有限求和实验

固定 Lean **4.35.0**，mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`，Physlib `c5a908ba7a1ee474063626bdf0470af006f9812e`。

这里是 `projects/quantum-experiments` 的唯一活动 Lake 工作区：

- `Verified/`：已修复并验证的六份 PMF 桥接、真实信道乘积测度、独立性与方差证明。
- `Comparison/`：强原生有限求和基线、同题有限中心矩接口及双评分协方差消费者扩展。
- [比较报告](Comparison/README.md)：实际证明/适配成本及限制；没有观察到当前纯有限任务上桥接的净优势。
- [原验证说明](Verified/VALIDATION.md)：原五处空缺修复及原36声明验收。
- [发布与历史记录](history/README.md)：公开源码基线、必要失败记录、差异和发布验证。
- `../physlib-pmf-bridge/`：冻结历史原稿与计划；其中 `UNVERIFIED_DRAFT` 不作为活动构建入口。

## 从干净克隆复现

在本目录执行：

```bash
bash setup.sh
source env.sh
python3 compare-check.py
```

`setup.sh` 下载官方 Lean 发行包并核对 SHA-256，以本地固定 manifest 获取依赖和所需 mathlib 二进制缓存，再运行环境 smoke check。工具链、下载和缓存只写入本目录的 Git 忽略子目录。需要允许访问 GitHub 官方发行包、依赖仓库及官方缓存；不需要私人文件或额外凭证。

`compare-check.py` 构建两个库、逐文件检查新增六模块、核查全部63显式声明的公理闭包和源码基线，并进行两轮有限叶文件增量计时。也可在上级目录运行 `bash check.sh`。只检查原六份修订稿可运行 `python3 verify-proofs.py`。

两个 Lake 入口为 `lake build PMFBridgeDraft PMFComparison`。脚本复用现有缓存，不更新 pins；不触及仓库根 `experiments/kl-for-mathlib`，因此不调用专用于该旧项目的根 `scripts/setup.sh`/`scripts/check.sh`。

## 验证范围与保全

发布源码身份由 `history/source-baselines.json` 记录的14个冻结历史文件和6个已验收桥源码 SHA-256 核查。此前本机验证还核查过完整私人保全包与30个恢复文件，原件继续保留在本地历史分支/下载区；公开复现不依赖它们、私有 Library ID 或未发布 Git 对象。

日志输出在 `logs/`，不常规纳入 Git。按本次发布要求，必要失败摘录、差异和有限发布验收快照保存在 `history/`，不含缓存、工具链二进制或凭证。历史报告中的旧绝对路径与本地提交标签是当时证据，公开复现请使用上述命令。

已证明的是固定输入、有限输出的具体命题，不能推广为相关随机输入下的无条件独立；消费者扩展也不等同于长期维护或跨版本升级数据。没有执行独立的全依赖内核重放。
