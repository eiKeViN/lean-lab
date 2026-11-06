# 重放证明与核对首轮身份

以下命令在 `experiments/measurement-api` 中运行。先完成项目通常的固定环境设置和库检查：

```bash
bash scripts/setup.sh
bash scripts/check.sh
```

这不会重新派发求解者。重放一份已经保存的证明、在新库上回归以及重新做一次上下文独立试验，是三种不同工作。

## 当前版本

```bash
# 只检查档案内源文件、输出和最终提交的哈希；不调用 Lean。
python3 Usability/recheck.py --allow-library-drift --verify-archives-only
python3 Usability/recheck.py --round round2 --verify-archives-only

# 使用当前库，重放首轮六人各自首个成功源和最终源，并打印全部类型/公理。
# 明确允许相对首轮冻结库的变化；输出类型标为 later_library_regression。
python3 Usability/recheck.py --allow-library-drift

# 使用 round2 冻结库，重放同题迭代版本的首个成功源和最终源。
python3 Usability/recheck.py --round round2
```

默认报告和完整输出只写入忽略目录 `results/usability-parent/round1` 或 `round2`；不会改写存档结果。仅维护者有意刷新紧凑证据时使用 `--record`。当前库与 `freeze-round2.json` 相同；首轮库不同，所以不带 `--allow-library-drift` 的首轮命令应拒绝运行。这一拒绝不是证明失败。

重放器直接读取 Git 中的 `Usability/records/*.json` 或 `records/round2/*.json`。这些档案内嵌每次原始源和完整输出，包含失败及旧记录器误拒绝；`source_snapshot`/`log` 字段保留当时路径，仅用作追溯，并不要求那些忽略目录仍然存在。重放器校验档案哈希，取首次普通编译退出 0 的源，再分别重放它和最终提交；这是一次新的 Lean 调用。仅校验哈希的命令不能替代它。

## 严格重放冻结首轮

首轮库为 `f642cf3`，协议提交 `321c723` 尚无答案，`afd4ef8` 已含全部答案与档案而库仍相同。用 `afd4ef8` 的单独 checkout 可同时取得首轮冻结配置与结果。下面使用当前重放器读取其档案，从而不依赖旧版重放器当时使用的忽略日志；不会改动该 checkout 的库或记录器。

```bash
MEASUREMENT_STUDY_ROOT="$PWD"
git worktree add --detach /workspace/lean-lab-measurement-r1-replay afd4ef8
cd /workspace/lean-lab-measurement-r1-replay/experiments/measurement-api
bash scripts/setup.sh
bash scripts/check.sh
python3 "$MEASUREMENT_STUDY_ROOT/Usability/recheck.py" --root "$PWD"
cd "$MEASUREMENT_STUDY_ROOT"
```

目录名可以替换成一个尚不存在的可写路径。严格重放检查所有冻结库/配置文件及题目哈希，不允许漂移。旧 checkout 的 `scripts/check.sh` 验收的是它自己的 28 声明版本。重放器实现属于当前测试工具，并会记录自身 SHA；不将它误写成学生当时使用的记录器版本。上述额外 checkout 从零下载/构建的整套命令在本轮未再次执行；首轮 44 声明在冻结库上的实际复核已保存于 [parent-review.json](parent-review.json)，当前库上的实际回归见 [regression-review.json](regression-review.json)。

## 单个题目与过程证据

- 原题：`problems/E1.md` 至 `E4.md`；每题 SHA 与 `freeze.json` 对应。
- 最终证明与事实记录：`Submissions/`；每份档案记录最终 Lean 源 SHA。
- 派发资源、隔离方式、帮助：`assignments.json`、`PROTOCOL.md`；同题后续为 `round2-assignment.json`。
- 每次源/错误/退出码/选项/进程耗时：`records/`。首轮 22 次调用，后续 2 次；父代理与维护者调用分开记录。
- 规范覆盖：`RUBRIC.md`；编译/类型/公理通过后仍需按该标准读陈述，避免把弱化目标计为完成。
- 首轮记录器的准确旧实现：协议提交 `321c723` 的 `Usability/attempt.py`；当前记录器已修正公理名格式，默认会因首轮库哈希不同而拒绝把新调用记为首轮。

如需再次派发独立求解者，应建立新的题目/库冻结身份和记录目录，且不能将已看过这些答案的上下文当作干净参与者。原始生成过程和搜索选择不由已保存的最终证明重建；档案使结果与公开失败可核查，不保证再次生成相同代码。
