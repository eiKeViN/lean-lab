# Graded / reflection API experiment（第四轮）

状态：完成。完整构建、两种冻结客户端试验及78阶段全量检查全部通过。
执行代码与输入绑定：`31c6f7ca02b1b30d20c978a467517c9c0c362def`。
数学源码与已独立复核的`857aceb5f6095b8a204cc64fcc0c32c01836e2a2`一致；
接口登记与`803d94528e6ebb0601ae3e206ec9b039eb972b8b`一致，后续提交仅报告/证据。
基点`a797fbc1300142c56c18ebfaa0ae84b357bc4b3d`，分支
`experiment/graded-reflection-api-20261024`。main及先前三轮分支保留，不建PR、不合并。
[发现索引](../experiments/kl-for-mathlib/API-GUIDE.md)列出完整命名、语义及来源。

| 操作族 | 新API / 复用 | 实际生产下游 |
| --- | --- | --- |
| 分次同态与截面函子性 | comp的vertex/edge求值、sectionMap保持comp/id；复用sectionMap_apply、eq_of_maps | SplitIn.projection_comp_inclusion、sections_split |
| range自然性与幂等固定点 | rangeMap_projection交换方块、rangeMap_val、projection/inclusion求值、range_fixed | Hom.imageInclusion/Projection、imageSplit、imageSection_fixed |
| splitting/projector/image | projection_comp_inclusion；projector_apply_vertex/edge，复用原vertex_split/edge_split | 原projector_vertex/edge及截面分裂，保持全部旧名称与类型 |
| twisted lattice成员与核坐标 | val_add/val_smul、mem_lattice_iff、left/right_apply、两侧kernelMap坐标 | lattice_saturated、左右满射与核的满射/单射证明 |
| 反射张量自然性 | twistMap_val、tensorFirst_natural/Second_natural（任意A-linear map） | 原tensorFirst_map/Second_map改为特化调用；tensor_difference、KernelCoordinates.twistMap_injective |

这五组相邻且共享接口，不是五个完全独立领域；其中张量族是已有Endo自然性的补齐。
shift和costalk现有接口较多，本轮不重复铺开。跨对象张量规律的普通检查通过，
当前生产使用仍通过原Endo兼容入口，不宣称已有新的跨对象生产应用。
共22条新数学定理，六个生产文件增加196行、删除50行；无新生产定义、instance或ext属性。
全部原定义保留expose，没有批量格式迁移。

## 真实证明变化

旧imageProjection两个交换图直接依赖rangeMap的restriction实现；新的公共交换方块是：

```lean
    (rangeMap e f g h).map ((rangeProjection e).map m) =
      (rangeProjection f).map (g.map m)
```

实际lower证明为`(ModuleData.rangeMap_projection (h.vertex _) (h.edge e) (B.lower e) (h.lower e) v).symm`，
upper对称。一般rangeMap_val改为由此方块和projection求值推导，而不继续依赖rfl。

原样结构字段摘录，外层上下文省略：

旧版：
```lean
  lower e v := Subtype.ext (h.lower e v)
```
新版：
```lean
  lower e v := (ModuleData.rangeMap_projection (h.vertex _) (h.edge e) (B.lower e) (h.lower e) v).symm
```
旧imageSplit/imageSection_fixed拆range成员见证；新证明复用range_fixed和求值API。
旧sections_split逐点计算；新证明改用sectionMap_comp、projection_comp_inclusion、sectionMap_id。
原projector幂等性经projector求值和已有split规律得到。

旧lattice客户端把成员证明直接拆为共同lift见证；新代码先经mem_lattice_iff。
左右kernelMap的构造也经该接口提供成员证明，投影和坐标的实际数学约定不变。
张量差值加法步骤改用Twist.val_add；新val_smul明确新标量经τ作用，避免与系数变化的逆方向混淆。

求值及identity使用simp，朝原向量与原操作归一化；交换方块、sectionMap_comp、
retraction、range_fixed、成员iff和一般张量自然性保持显式调用，避免自动展开所有结构。
复用mathlib的quotKerEquivRange/liftQ、现有Hom.eq_of_maps和标准ext，不增加自动化框架。

## 两种冻结试验

正式实现不采用变体。两者都保留expose，正常module import，不给选定producer提供olean.private。

| 扰动 | 上游实现与API修补 | 冻结真实客户端 / 旧对照 |
| --- | --- | --- |
| quotient-range | rangeMap改为经ker(e) quotient，用第一同构定理与liftQ诱导；局部求值证明同时保证graded字段。只重证公共rangeMap_projection，其余API不改 | 整份Summand、AdjointSheaf均通过；a797旧Summand失败。AdjointSheaf本轮未改，旧版也通过，不算区分收益 |
| relational-lattice | 用Submodule.copy把存在共同lift的carrier改为lower/upper兼容性关系；复用原闭合性证明。只重证公共mem_lattice_iff | 整份TensorKernel、TensorDescent、KernelCoordinates均通过；a797旧TensorKernel失败，后两旧版也通过，不算区分收益 |

第一种不是加零或换binder：从restriction改为quotient诱导，API方块直接表达两者相同的数学操作。
第二种是image见证与fiber-product关系两种自然表述；copy保留线性闭合性证据，
不声称重新构造了完整范畴pullback。两条API分别对所有输入/所有lattice向量给出原语义。
每次均冻结整文件SHA、重新elaboration；最后确认临时源码恢复、冻结客户端字节未变，
所记录的正常.olean*工件也未变。
试验只覆盖所列链，未全库重编译变体或承诺所有生成eq_1/helper兼容；正式实现另做全库验收。

直接压力收益落在range交换方块和lattice成员边界。截面、projector、一般张量自然性有真实调用，
没有单独改变其自身实现，不能把整文件通过当成每条API均已压力测试。
计算载体、标准product/subtype与已有val接口仍公开；不宣称完全抽象化或生产性能优化。

## 验证与成本

六文件精确源码登记在api-reflection-source.json，原三轮source/type/gen数据不刷新。
本轮完整导出先独立与a797逐条比较，再给旧检查提供精确去新增的历史视图；没有通配豁免。
full-build前的局部目标和普通导入已通过，36项公理闭包只含原允许基础公理。
隔离试验共113.120秒，最大子进程RSS 3317324 KiB。
调试保留section结束位置、ModuleCat隐式参数失败；隔离构造初稿的private可见性和implicit重写失败
也单独归档，不当作有效负对照。最终改为局部构造与显式等式输运，没有开展无关编译器研究。

```sh
source scripts/env.sh
bash scripts/check.sh all
cd experiments/kl-for-mathlib
# 与任何构建互斥；临时源码在finally中恢复
python3 graded_reflection_trial.py
```

完整构建1134.338秒，最大子进程RSS 3373500 KiB；增量构建实际重编译49个模块。
接口3967→3989，精确新增22条数学定理，无生成新增、旧声明删除、类型或归属变化。
首次全量检查在第73阶段rollout-tests失败，前72阶段通过，耗时473.639秒。
该旧测试直接比较当前源码与早期迁移的字节，漏掉本轮已登记增量的逆向视图。
修复只在这一条历史比较前调用api_reflection.prior_source；原迁移规则、plan和基准均未改变，
当前产品仍必须等于本轮六文件精确overlay，任意未登记变动仍被拒绝。
修复后含剩余源码/比较器测试的91项Python回归全部通过。数学源码、接口记录与扰动脚本不变。
修复后的完整检查链78阶段全部通过，耗时487.369秒，最大子进程RSS 7779600 KiB，
最后缓存热检查3.492秒。沿用已完成的生产构建，没有再次编译生产模块。
普通现代import、36项公理闭包、完整/普通接口、各轮精确源码/类型与全部适用回归通过；
无sorry、新增公理或既有数学类型契约变化，无未解决阻塞。
复用固定Lean4.34.1/5045d005与Mathlib d13f23b7的已初始化缓存，未全编Mathlib或更新pins。
记录阶段墙钟与RSS，包含编译锁等待；不估造冷构建或性能收益。token无遥测，不估造。


## 固定证据

- [78阶段命令、退出码和成本](evidence/graded-reflection-api/accepted/stages.json.gz)，
  [最终检查成本](evidence/graded-reflection-api/experiment/acceptance.json)
- [完整构建成本](evidence/graded-reflection-api/experiment/full-build.json)，
  [49模块重编译记录](evidence/graded-reflection-api/experiment/build-coverage.json)
- [完整接口原始差异](evidence/graded-reflection-api/experiment/raw-interface-diff.json)，
  [精确22条记录核对](evidence/graded-reflection-api/accepted/api-reflection-full-records.log)
- [quotient-range旧新对照](evidence/graded-reflection-api/experiment/trials/quotient-range/comparison.json)，
  [relational-lattice旧新对照](evidence/graded-reflection-api/experiment/trials/relational-lattice/comparison.json)
- [首次失败检查链](evidence/graded-reflection-api/experiment/acceptance-before-rollout-view-fix/stages.json.gz)，
  [测试适配后的91项回归](evidence/graded-reflection-api/experiment/rollout-view-fix.log)
- [414项输入哈希与版本](evidence/graded-reflection-api/accepted-inputs.json)，
  [266份证据的原始/压缩SHA256](evidence/graded-reflection-api/manifest.json)

原始严格比较器因任何新增而显示passed=false；本轮核对器要求精确22条新增完全匹配才接受。
accepted只收本次成功检查的日志/导出；实现初稿失败及首次全量失败在experiment中分开保留。
已核对证据哈希、报告/索引链接、输入工作树与Git提交字节，以及两组冻结客户端的输入身份。
最终提交相对执行代码仅增报告/证据。main仍为178ccf2，前三轮分支保留，未创建PR或合并。
