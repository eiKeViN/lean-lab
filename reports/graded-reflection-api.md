# Graded / reflection API experiment（第四轮）

状态：分阶段进行，尚未全库验收。
基点a797fbc1300142c56c18ebfaa0ae84b357bc4b3d，分支
experiment/graded-reflection-api-20261024。不修改main、不建PR、不合并，保留先前三轮。

本轮选五个相邻操作族：

| 家族 | 生产者 / 实际消费者 | 状态 |
| --- | --- | --- |
| 分次同态组合与截面映射 | GradedSheaf.Summand中的Hom.comp/sectionMap → SplitIn.sections_split | 局部通过 |
| range自然性与幂等固定点 | ModuleData.Range → Hom.imageInclusion/Projection/Split、imageSection_fixed | 局部通过 |
| splitting/projector/image | SplitIn.projection_comp_inclusion、projector点值 → 现有projector幂等性、截面分裂 | 局部通过 |
| twisted lattice成员与核坐标 | ReflectionPair.Twist → TensorKernel的右核、左右满射与单射 | 待实现 |
| 反射张量的一般自然性 | TensorKernel/TensorDescent → 既有tensorFirst/Second_map、tensor_difference、KernelCoordinates | 待实现 |

现有shift与costalk已经有较多接口，暂不重复铺设。保留expose和原定义的数学/计算契约。
普通prod/subtype、LinearMap/LinearEquiv接口继续作为计算接口，不隐藏所有record。

第一阶段补11条定理，实际改造两个生产文件。复用已有Hom.eq_of_maps、sectionMap_apply、
SplitIn.vertex_split/edge_split及mathlib函数/线性映射外延，不新造ext别名。
局部目标GradedSheaf.Summand编译成功。调试有一次遗漏section的end及隐式参数匹配失败，
随后用完整定理实参修正；失败日志保留。全库门禁尚未运行。

计划隔离两种等价构造：经quotient构造range上诱导映射；把lattice的存在见证carrier改为兼容性关系。
固定改造后的整份真实下游，比较旧源码，记录API层修补、无区分力对照和恢复。
不将变体作为生产性能优化，不为通过门禁放宽全局策略。

成本、完整覆盖与源码索引在完成后补齐。token无遥测，不估造。
