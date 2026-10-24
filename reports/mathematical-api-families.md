# 数学 API 操作族实验（第三轮）

状态：完成。完整9186-job构建、两种六文件冻结试验、75阶段项目验收全部通过。
验收代码与输入绑定：`7cc09db394c8ba68a744808ed89710024b1750b3`；
数学源码仍与已独立复核的`2d8a70eac578ec65047e50caa653bad4cf6d5755`逐字节一致。
后续提交仅归档报告/证据。
基点 `bdbca7ff639bc32f94a85647c88cb16d9e80b294`，分支
`experiment/mathematical-api-families-20261024`。第一阶段检查点`15ccdc5`已推送。
保留前两轮完整结果，main不变，不建PR、不合并。

[本轮与上轮的原样源码摘录](mathematical-api-gallery.md)列出固定SHA、行号与真实消费者。

## 选择与数学边界

本轮覆盖四组操作模式，不以定理数量、expose数量或行数下降衡量；也不宣称覆盖四个独立数学领域。
盘点发现大部分基础API已经存在，因此复用原有兼容性、自然性和像判据，不重复包装casesOn。
七个生产模块中的四类表示依赖分别是：逐点输运、子模成员的实现、product/pi的依赖类型转换、
子图与ambient顶点集合之间的兼容性对应。

| 操作族 | 新声明 | 实际消费者及变化 |
| --- | --- | --- |
| 同构输运 | `Iso.assignments_apply`, `assignments_symm_apply`, `sections_val_apply`, `boundary_apply` | Iso既有compatible_iff、stalkMap/boundaryMap、upwardKernel_iff与Structure中Iso.flabby/generated。flabby显式使用assignment等价的逆，再经点值公式，而不change到某个record函数体 |
| 局部核 | `mem_upwardKernel_iff`, `upwardKernel_univ` | Iso.upwardKernel_iff、Pullback两个核包含、Models的prod/pi_upwardKernel_iff。局部约束先通过成员API取得；对所有边的约束等于完整stalkMap的线性核，供prod/pi_kernel_iff复用 |
| product/pi | `prod_stalkMap_apply`, `pi_stalkMap_apply`, `prod_compatible_iff` | prod_generated/flabby与prod/pi_kernel_iff，Models的prod/pi_upwardKernel_iff。依赖顶点相等所需的cases移入两条stalk分量API的证明，客户端按分量组合，不重复处理casts |
| restriction/延拓 | `restrict_extendAssignment`, `restrict_compatible_iff` | extend_compatible由兼容性等价、restriction∘零延拓=id推得；restrict_flabby_live继续复用extend_compatible。兼容性等价精确对应子图集合Ω和其ambient像，不要求ambient任意assignment由零延拓产生 |

共11条新增数学定理，七个生产文件相对bdb增加124行、删除67行，无新生产定义、instance或ext属性。不是为所有定义补求值引理：
局部成员判据、核恒等式、product兼容性和restriction兼容性是实际消费者需要的逻辑接口。
保留所有原定义的expose、数学类型和计算载体；未批量统一文件格式。

复用既有 `Iso.compatible_iff/map_sections/stalkMap/boundaryMap`、`pi_compatible`、
`prod/pi_kernel_iff`、Models的prod/pi像判据、`extendAssignment_mem`，以及mathlib的
LinearEquiv逆函数、Submodule.mem_iInf/LinearMap.mem_ker、Prod.ext、funext。
固定mathlib的 `Mathlib/LinearAlgebra/Pi.lean` 与
`Mathlib/Algebra/Module/Submodule/Lattice.lean` 提供交核/分量接口，
`Mathlib/Algebra/Module/Equiv/Defs.lean` 提供输运等价的规则。
没有另造范畴框架或全库自动化。

## 前后证明与自动化

旧Structure.flabby把目标change成vertex等式，依赖assignments的具体正向函数；
新证明经assignments_apply、assignments_symm_apply再用已有LinearEquiv.apply_symm_apply。
旧Models局部核证明直接把成员假设当作`∀ e∈F, ...`应用，并为product/pi反复cases边的source等式；
新证明先通过mem_upwardKernel_iff取得约束，再经stalk分量API组合。
旧Pullback同样把hv直接当函数；新证明显式调用成员判据，保留原图映射几何论证。

旧extend_compatible逐边从两个image成员构造子图边，处理Subtype相等和lower/upper cast。
该论证现在只在restrict_compatible_iff的证明出现一次，实际extend_compatible缩为：

```lean
  apply (B.restrict_compatible_iff K Ω (B.extendAssignment K f)).mp
  rw [B.restrict_extendAssignment K f]
  exact hf
```

这是一侧retraction；没有错误地声称任意ambient assignment都等于其限制的零延拓。
新API不是完全抽象的sheaf表示：vertex/edge、wrapper值和标准product/pi载体仍是计算契约。
不宣称所有证明都变短。特别是显式成员转换使Pullback略长，但把carrier表示依赖局限在API。

七条simp规则：四条Iso点值、两条prod/pi stalk分量、一条restrict∘extend消去；
均降低输运/组合层数，右侧归一到原对象，没有反向折叠规则。
其余四条逻辑/子模等式保持显式调用，避免全局展开每个成员条件。
无需新ext属性：已有Prod.ext、Subtype.ext、函数外延足够。没有全局透明性或实例搜索调整。

## 两种实现扰动：整文件冻结与旧对照

仅隔离改写生产者Sheaf.Iso，正式实现不替换。两种变体都保留expose。

1. **逆向双射构造assignments**：原piCongrRight正向构造改为先取逐点逆向线性映射，
   用LinearEquiv.ofBijective构造后取symm。前向值改由所选逆函数得到。
   只重证assignments_apply：由back.apply_symm_apply得到逐点逆向等式，再经symm_apply_eq。
   assignments_symm_apply、section和boundary等其余API证明未改。
2. **upwardKernel的交核表示**：原carrier约束record改为
   `⨅ e : Outgoing x, ⨅ (_ : e ∈ F), ker ((proj e).comp (B.stalkMap x))`。
   只重证mem_upwardKernel_iff，用标准mem_iInf、mem_ker、comp/proj求值。
   upwardKernel_univ及所有输运、product/pi证明未改。

两条API分别对所有assignment/顶点、所有局部边集/向量给出原数学语义，因此不是几个数值测试，
也不是加零、改binder名或隐藏body来凑差异。交核是数学上自然的另一种子模构造。

每种变体都重新elaboration六个**整文件冻结**的新客户端：Pi、Products、Models、Pullback、
Structure、Restriction。每次均保存SHA256、源码补丁、命令/退出码、正常工件恢复哈希。
使用正常module import与Lake setup的scratch artifact替换；不给选定producer提供olean.private，
没有另一个维护项目或import all证明。普通ApiFamiliesChecks也通过，25项公理闭包核对通过。

| 对照 | 逆向双射 | 交核表示 |
| --- | --- | --- |
| 只改实现，不修API | 原assignments_apply的rfl失败 | 原mem_upwardKernel_iff的rfl失败 |
| 只修上述一条API证明 | producer通过 | producer通过 |
| 六份冻结新客户端 | 全部通过 | 全部通过 |
| bdb旧Structure | 失败，依赖assignment定义归约 | 通过 |
| bdb旧Models、Pullback | 均通过 | 均失败，依赖carrier直接当函数 |
| bdb旧Pi、Products、Restriction | 均通过 | 均通过 |
| 正式源码/冻结字节/正常Lake工件 | 全部未变 | 全部未变 |

因此维护收益的压力证据分别落在Structure和Models/Pullback；**不把旧新都通过的文件包装成成功区分**。
product/pi的分量规律支持局部核客户端；restriction虽有真实、明显更概念化的客户端，
本轮两个扰动没有直接压力测试其自身实现。也未穷尽所有实现变化、计算性能或carrier类型变化。
Classical逆函数变体不作为生产性能优化。变体不承诺所有历史生成eq_1/helper也兼容；
完整历史门禁针对正式实现执行，未把全部生成名升级为稳定API。

## 阶段、门禁与复现

阶段一先推送同构输运API和真实客户端；其后扩展其余三组，保持顺序构建。
局部目标Models/Pullback/Restriction/Structure与普通导入均通过。
一次Pullback调试编译失败于ModuleCat载体别名在implicit透明性下的rw匹配；
改用显式定理实参的mp/mpr解决，没有更改全局选项。失败日志单独保留。

`api-families-source.json`绑定相对bdb的七文件精确字节补丁；前两轮source/type/gen记录不刷新。
api_families逐条登记本轮新增声明，另对完整当前接口与bdb逐项比较；
只在精确核对后给旧比较器提供去掉本轮新增的历史视图。
前一轮单元测试以显式mock隔离其原记录边界，新一轮另检查源码/声明mutants。
完整接口/源保护不按前缀忽略声明，不放宽全局门禁。

首次整轮验收到第74阶段proof-evolution-tests失败（前73阶段通过），耗时464.458秒。
原因是该旧回归先把当前源码逆转为module迁移前的输入，再让proof_evolution检查旧守卫；
新源码层此前只识别bdb/31f/178的现代输入。所需交集恰为Models与Pullback两个文件。
修复仅在api_families.HISTORICAL_INPUTS登记Git 382d29d的两个精确字节SHA，并再次核对Git字节；
不泛化为任意旧header。当前产品仍必须等于七文件overlay，旧字节不能作为overlay输入。
新增回归验证旧输入可读、增添一个换行即拒绝、不能作为当前overlay起点；
修复后新旧两组33项单元测试通过。数学源码、API类型、两类扰动及六文件冻结均不改变。
失败整轮日志留存；修复后完整重跑75阶段全部通过，未重编译未变生产模块。

```sh
source scripts/env.sh
bash scripts/check.sh static
bash scripts/check.sh all
cd experiments/kl-for-mathlib
# 与任何构建互斥运行；试验sources在finally中恢复
python3 api_families_trial.py
```

完整构建334.920秒，最大子进程RSS 3315808 KiB。
使用增量依赖缓存，日志记录69个模块重编译；未重新编译UpperSections或Stalks，
不是对所有9186项从零重编译；详见build-coverage.json。
完整接口3956→3967，恰有11条新数学定理，无新生成声明，旧声明无missing/changed/relocated。
原始比较器因任何新增而显示passed=false；本轮核对器只有精确11条新增均符合登记才接受。
最终完整门禁476.306秒，最大子进程RSS 7780184 KiB，最后热构建3.380秒。
75阶段均退出0，覆盖普通导入、25项本轮公理闭包（含全部11条新API和实际消费者）、
前两轮API、完整/普通接口比较、各轮源码/类型精确保护与全部适用回归。
无sorry、新增公理、既有数学类型契约改变或未解决阻塞。
输入绑定408项源码/脚本/配置哈希，前两轮报告及证据完全不变。
阶段一18.327秒；阶段二失败23.806秒，修正后的阶段三20.613秒；
普通导入检查3.616秒，静态检查10.035秒。
两种试验共110.584秒，最大子进程RSS 3175720 KiB；各步骤耗时另记。
复用已初始化缓存，不估造冷构建或API性能收益；阶段墙钟含串行编译锁等待。
固定Lean4.34.1/5045d005与Mathlib d13f23b7不变，没有全编Mathlib。
token无遥测，不估造。没有PR或合并授权，也未进行此类动作。

## 已归档的实现对照

- [逆向双射旧新对照](evidence/mathematical-api-families/experiment/trials/inverse-bijection/comparison.json)
- [交核旧新对照](evidence/mathematical-api-families/experiment/trials/kernel-intersection/comparison.json)
- [试验总成本](evidence/mathematical-api-families/experiment/trials.json)

每个trial子目录同时保存实际变体源码、唯一API修补patch、完整客户端SHA、逐步命令/退出码、
旧/新错误日志及恢复检查。

## 最终验收证据

- [75阶段命令与退出码](evidence/mathematical-api-families/accepted/stages.json.gz)，
  [验收总成本](evidence/mathematical-api-families/experiment/acceptance.json)
- [完整构建成本](evidence/mathematical-api-families/experiment/full-build.json)，
  [实际重编译范围](evidence/mathematical-api-families/experiment/build-coverage.json)
- [原始完整接口差异](evidence/mathematical-api-families/experiment/raw-interface-diff.json)，
  [精确11条记录核对](evidence/mathematical-api-families/accepted/api-families-full-records.log)
- [首次失败整轮](evidence/mathematical-api-families/experiment/acceptance-before-historical-view-fix/stages.json.gz)，
  [历史视图修复的33项回归](evidence/mathematical-api-families/experiment/historical-view-fix-verified.log)
- [408项固定输入身份及版本](evidence/mathematical-api-families/accepted-inputs.json)，
  [264份证据的原始/压缩SHA256](evidence/mathematical-api-families/manifest.json)

accepted目录仅收本次成功stages的日志和相应接口导出；失败与局部调试放在experiment目录。
所有链接、证据原始/压缩哈希、输入工作树字节及Git提交中的字节均已核对。
最终提交相对验收代码仅有报告/证据，没有生产、验证脚本或门禁数据规则修改。
main仍为178ccf2；前两轮分支保留在31f05da与bdbca7f。未创建PR、未合并。
