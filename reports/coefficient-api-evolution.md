# Coefficient transport API：实现演化实验（第二轮）

状态：所选实际客户端和隔离实现扰动已通过；完整构建/接口/公理门禁仍在运行，尚非最终验收。
从 `31f05da2d4ff1d80f2ceed3f8e1f3ac86fcb933b` 建立
`experiment/coefficient-api-evolution-20261024`。唯一维护项目不变，不修改main、不建PR、不合并。
第一轮六条数学API及其历史记录保留。本轮只恢复quotientPullback的expose，不统一文件格式，
撤销仅为隐藏它增加的四个局部R/S衔接证明和两个私有历史定义审计上下文，恢复原严格普通审计。

## 数学API与真实消费者

| 层 | 本轮声明 | 真实用途与正规形 |
| --- | --- | --- |
| CoefficientChange | `val_zero`, `val_smul` | upperQuotient及配对正交性，把wrapper的零/新标量作用转为原向量的零/e.symm标量；去掉无用scalar-tower假设 |
| CoefficientChange | `val_mapEquiv` | 用底层原等价描述输运等价；重写既有pairingEquiv_apply，成为实现扰动的唯一API证明修补点 |
| ModuleData | `val_changeHom` | 底层map→graded hom的求值桥，供sheaf lower/upper自然性调用 |
| GradedSheaf | `coefficientChange_lower_val`, `coefficientChange_upper_val` | 保持真实边映射，改造Hom.coefficientChange两个交换图及upperQuotient |
| GradedSheaf | `coefficientChange_compatibleOn_iff` | 兼容性等价；用于flabby/generated与截面等价的构造，不逐个客户端展开record |
| GradedSheaf | `coefficientChangeSections_symm_val_apply` | 逆向截面输运逐点求值；配对homogeneous与左右正交性使用 |
| PerfectPairing | `coefficientChange_apply` | 把新配对表示成原配对与系数等价e；实际Uniqueness对称配对输运调用 |

共9条新定理，修改6个生产文件（包含恢复Structure）。复用第一轮val_map、map_id_apply、
pairingEquiv_apply、既有wrapper.ext及标准LinearEquiv规则；没有新实例、ext规则、公开casesOn包装
或新模块层级。`compatibleOn_iff`和配对输运公式保持显式调用；其余求值/零/标量规则使用simp，
右侧朝原对象的值正规化，没有相反方向的折叠规则。未给完整定义增加simp属性。

原客户端中的隐式定义归约、congrArg直接当作目标证明、`change e (p.pairing _ _)=0`，改成
命名求值规则与等式输运。某些显式衔接更长，收益是隔离表示依赖，不宣称所有证明行数减少。
保留wrapper.val/mk及模块载体的计算接口，不声称建立完全抽象的系数变化库。

## 隔离实现变化：实际旧新对照

上游仅改 `CoefficientChange.mapEquiv`：原来显式给正向map和逆函数；改为输运逆映射
`map e f.symm.toLinearMap`，用已有map_injective/map_surjective证明双射，通过
`LinearEquiv.ofBijective`构造后取symm。目标类型和标量约定不变，仍expose；当前正式实现不替换。
这是常见的“从双射构造等价”选择，前向函数此时通过所选逆函数求值，旧rfl不再足够。
不是加零、改binder名或移除expose来制造差异。

对API层仅把val_mapEquiv的rfl证明改成：由apply_symm_apply获得逆映射方程，经val_map与
symm_apply_eq恢复原前向求值公式。其余API声明/证明保持原文，已有pairingEquiv_apply无需再改。
这证明对所有f和m的底层向量语义相同，未改变数学契约，不仅是几个具体数值测试。

| 步骤 | 结果 |
| --- | --- |
| 只改实现，不修API证明 | val_mapEquiv原rfl证明失败（保留负对照） |
| 改实现并重证上述一条API | 实际Coeff.Dual生产者通过 |
| 冻结当前graded coefficient Basic文件 | 整文件byte hash不变，重新elaboration通过 |
| 冻结当前GradedSheaf.Duality文件 | 整文件byte hash不变，重新elaboration通过 |
| 冻结当前GradedSheaf.Uniqueness文件 | 整文件byte hash不变，重新elaboration通过 |
| 普通ApiEvolutionChecks | 组合规律、所有指定expose控制和17项公理闭包通过 |
| 31f的旧Duality / 旧Uniqueness | 两份实际旧文件均因pairing的定义归约依赖而失败，不是缺工件 |
| 恢复 | 正式源码、冻结客户端和所记录的正常Lake工件hash均未变 |

脚本`api_evolution_trial.py`用当前Lake normal import的setup，只替换选定模块的scratch工件路径；
不给选定producer提供olean.private。没有另一份维护项目，也没有用import all进行数学证明。
生产源码只临时替换并在finally恢复，代码/命令/退出码/冻结hash/两份patch均留存。

收益证据局限于这种等价构造变化，直接影响配对链；lower/upper/compatibility等API有实际消费者，
但不能据此断言本扰动逐一压力测试了它们。未来若变更carrier、wrapper.val或sections类型，仍可能
需要其他API/契约评估。Classical逆函数的运行性能不在本实验比较范围，未将该变体作为生产优化。

## 门禁、复现与成本

`api-evolution-source.json`按31f绑定6文件的精确新旧字节；第一轮source/type/gen记录不刷新。
只有核对第二轮完整新增记录后才给旧比较器提供去除第二轮新增的历史视图；完整当前原始导出
另与31f逐条比较，不按名字前缀忽略新增，也不把全部生成名当稳定API。

```sh
source scripts/env.sh
bash scripts/check.sh static
bash scripts/check.sh all
cd experiments/kl-for-mathlib
# 不与构建并行
python3 api_evolution_trial.py
```

已测实现试验32.863秒，最大子进程RSS 3178724 KiB；首次试验因尚未显式导入/编译Structure而
未通过额外expose控制，该失败与修正后的真正旧新对照分开记录，不作为语义失败。
完整成本与验收结果待最终归档。固定Lean4.34.1/5045d005与Mathlib d13f23b7不变；复用官方cache，
没有再次bootstrap或全编Mathlib。token无遥测，不可得。不把缓存构建成本当API速度收益。
