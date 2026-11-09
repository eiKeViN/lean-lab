# E3New 事实记录

## 完成范围

已完成练习 E3 的全部要求，解答位于 `Usability/Submissions/E3New.lean`。

- `E3New.merged`：对任意有限结果集和任意函数 `f : X → Y` 构造合并后的 POVM，使用允许的 `POVM.coarsegrain`。
- `E3New.merged_effects`：合并后的效果恰为相应纤维上原效果之和。
- `E3New.merged_probability`：合并后的实数 Born 概率恰为相应纤维上原概率之和。
- `E3New.pushforward_sum_abs_le`：任意两个有限概率分布经确定性推前后的实数绝对差之和不增加。
- `E3New.measurement_sum_abs_le`：题目要求的两个密度矩阵测量概率之间的不等式。

没有添加满射、满秩、可交换或其他数学假设。没有使用 `sorry` 或自定义公理。

## 查阅的资源与公开操作

首先只读取了 `Usability/LEARNER.md` 与 `Usability/problems/E3.md`。
随后列出了允许库的源码文件，并读取了：

- `MeasurementAPI.lean`
- `MeasurementAPI/POVM.lean`
- `MeasurementAPI/Probability.lean`
- `MeasurementAPI/Observations.lean`
- `vendor/physlib/QuantumInfo/Measurements/POVM.lean`
- mathlib 的 `Mathlib/Algebra/Order/BigOperators/Group/Finset.lean` 中 `Finset.abs_sum_le_sum_abs` 的声明

在允许的 mathlib 目录检索了 `abs_sum_le_sum_abs`、`sum_fiberwise_eq_sum_filter` 与 `sum_sub_distrib`。
证明使用扩展库提供的测量合并与经典推前接口，再用有限和三角不等式和按纤维求和恒等式完成收缩结论。

只修改了分配的解答和本记录文件；所有 Lean 调用都通过指定记录器进行。未修改库、依赖、配置或证明预算。

## 尝试记录

全部记录位于 `results/usability/E3New/`。

1. `Attempt001`：`python3 Usability/attempt.py --case E3New`，首次完整解答编译通过；Lean exit 0，4.206 秒。
2. `Attempt002`：对上述五个声明执行 audit。Lean exit 0，但记录器报告 `audit_rejected`；输出的公理列表为 `[propext, choice, Quot.sound]`。查阅了本次尝试自己的 JSON 记录。
3. 将文件级 `open Classical BigOperators` 移入 `namespace E3New`，避免该作用域影响记录器在文件末尾打印公理名称。没有改变任何定义、定理或证明的数学内容。
4. `Attempt003`：再次对全部五个声明执行 audit，结果 `verified`；Lean exit 0，7.118 秒。所有声明的公理列表均为 `[propext, Classical.choice, Quot.sound]`。

最终检查命令为：

```text
python3 Usability/attempt.py --case E3New --audit --decl E3New.merged --decl E3New.merged_effects --decl E3New.merged_probability --decl E3New.pushforward_sum_abs_le --decl E3New.measurement_sum_abs_le
```

## 障碍与帮助

未遇到尚未解决的数学或接口障碍。唯一额外处理的是上述 audit 对公理短名的识别问题，已通过缩小命名空间打开作用域解决。

没有请求其他代理、联网或读取个人/房间历史；没有获得外部解题帮助。仅向父代理通报过编译完成及 audit 名称显示问题。
