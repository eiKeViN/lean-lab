# Coefficient transport API：实现演化实验（第二轮）

状态：完成。完整9186-job构建及72阶段项目验收全部通过。
已验收代码检查点：`44cf72ba98ac0869dbb0f912f5bc3150b6668892`；后续提交仅增加报告和证据。
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

共9条新定理，修改6个生产文件（包含恢复Structure），相对31f新增138行、删除72行。复用第一轮val_map、map_id_apply，
以及既有pairingEquiv_apply、wrapper.ext及标准LinearEquiv规则；没有新实例、ext规则、公开casesOn包装
或新模块层级。`compatibleOn_iff`和配对输运公式保持显式调用；其余求值/零/标量规则使用simp，
右侧朝原对象的值正规化，没有相反方向的折叠规则。未给完整定义增加simp属性。

原客户端中的隐式定义归约、congrArg直接当作目标证明、`change e (p.pairing _ _)=0`，改成
命名求值规则与等式输运。某些显式衔接更长，收益是隔离表示依赖，不宣称所有证明行数减少。
保留wrapper.val/mk及模块载体的计算接口，不声称建立完全抽象的系数变化库。

例如，旧 `SymmetricPerfectPairing.coefficientChange` 的对称性证明直接使用
`congrArg e (p.symmetric _ _)`；新证明先通过两次
`PerfectPairing.coefficientChange_apply` 暴露同一对原截面，再以该等式连接。
旧 `coefficientChange_flabby` 手工逐边 `congrArg val` / `CoefficientChange.ext`；
新版本通过 `coefficientChange_compatibleOn_iff` 双向输运兼容性，延拓的数学步骤不变。
完整前后代码由基点31f与本分支的6文件精确补丁记录，而非另造示例消费者。

命名和规则参照固定mathlib的 `Mathlib/Algebra/Module/Equiv/Defs.lean`
（函数求值、`apply_symm_apply`、`symm_apply_eq`、已有ext）及项目wrapper现有 `val_map`。
沿用 [module interface decisions](module-interface-decisions.md) 对数学接口与生成helper的区分，
未给已退休的八个match名称添兼容包装。新规则未尝试全局改变simp透明性或实例搜索；
ModuleCat载体别名使若干隐式重写不匹配，因此使用显式定理实参和等式传递。

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
变体只验收选定数学链，未承诺所有历史生成eq_1/内部helper也兼容这种实现变化；
完整项目与历史兼容门禁针对正式实现执行。

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
`ordinary-checks.log`也记录了该错误；该次外层shell继续执行静态检查，wrapper的退出0
不作为Lean成功证据。最终普通检查与修正后的隔离trial均独立检查Lean退出码。
完整构建1154.041秒，最大子进程RSS 3368416 KiB；
首次接口导入/导出分别4.986/10.220秒，最大RSS 7426920/7780920 KiB。
原始完整接口3947→3956，恰有9条新数学定理，无新生成声明，
旧声明无missing/changed/relocated。原始严格比较器因存在任何新增而显示passed=false，
本轮有限API记录核对器另要求精确9条新增后才接受。
完整门禁462.566秒，最大子进程RSS 7779880 KiB；最后热构建3.685秒。
72阶段均退出0，覆盖普通ApiEvolutionChecks/SemanticApiChecks、17项新链公理闭包、
原始ModernStructureCompat、完整/普通接口比较、各轮精确source/type策略及全部适用回归。
没有sorry、新公理或数学类型契约变化。保留的六条第一轮API与全部旧声明均通过精确比较。
这是已有缓存环境的阶段成本，包含串行锁等待；未测冷启动成本或API性能收益。固定Lean4.34.1/5045d005与Mathlib d13f23b7不变；复用官方cache，
没有再次bootstrap或全编Mathlib。token无遥测，不可得。不把缓存构建成本当API速度收益。

## 可复核证据

- [72阶段命令、退出码与成本](evidence/coefficient-api-evolution/accepted/stages.json.gz)
- [完整构建成本](evidence/coefficient-api-evolution/experiment/full-build.json) 与
  [最终验收成本](evidence/coefficient-api-evolution/experiment/acceptance.json)
- [原始接口差异](evidence/coefficient-api-evolution/experiment/raw-interface-diff.json)；
  [精确9条记录核对](evidence/coefficient-api-evolution/accepted/api-evolution-full-records.log)
- [隔离试验逐步命令/结果](evidence/coefficient-api-evolution/experiment/implementation-trial/metrics.json)，
  [冻结整文件哈希](evidence/coefficient-api-evolution/experiment/implementation-trial/frozen-downstream.json)，
  [恢复检查](evidence/coefficient-api-evolution/experiment/implementation-trial/restoration.json)，
  [公理日志核对](evidence/coefficient-api-evolution/experiment/implementation-trial/axiom-closure-check.json)
- [实现补丁](evidence/coefficient-api-evolution/experiment/implementation-trial/definition-only.patch) 与
  [唯一API证明修补](evidence/coefficient-api-evolution/experiment/implementation-trial/api-proof.patch)
- [402项输入身份与版本](evidence/coefficient-api-evolution/accepted-inputs.json)；
  [148份证据的原始/压缩SHA256清单](evidence/coefficient-api-evolution/manifest.json)

证据清单区分实验调试与最终accepted阶段；accepted只归档本次stages中的日志和本次接口导出，
不重用工作目录遗留的旧审计文件。第一轮报告/证据未修改。远端main仍为178ccf2，
第一轮分支仍为31f05da；本轮仅推送独立实验分支，没有PR或合并。
