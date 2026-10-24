# 第六轮：已有数学 API 的合理补齐

基线 `78cdaf405dbf1dcf07eed5490469b7a8704c93f0`，独立分支
`experiment/api-saturation-20261024`。环境已从该远端基线恢复，初始工作区干净。
唯一维护的 Lean 项目仍是 `experiments/kl-for-mathlib`。旧分支保留，不创建 PR、不合并、不强推。
状态：完成。完整构建、逆向实现试验及 **84/84 阶段验收全部通过**，含 121 项 Python 回归。
执行代码与 426 项输入绑定：`70b7bcc161be904259cc9e54194ed0577c4c61c2`；
数学源码与已推送检查点 `be92e1e30df2beeee92d4d721fcb71f9822d1255` 相同。
后续提交仅报告/证据。

本轮选取四组相邻的**已有家族补齐**，不是四个新领域；新增 13 条数学定理，
仅改两个生产文件，没有新结构、实例或模块迁移，全部定义保留 expose。
[发现索引](../experiments/kl-for-mathlib/API-GUIDE.md)给出入口。

## 选择依据与锁定 mathlib 对照

对照固定 checkout `d13f23b723b8a846827a245b89c10fc7d3f11612`，不使用网上最新版。
下面的路径均相对于该 checkout 的 `Mathlib/`。

| 候选与决定 | mathlib 原型 | 本项目的理由与边界 |
| --- | --- | --- |
| 采纳：同态结合/单位 | `Algebra/Module/LinearMap/Defs.lean`：`LinearMap.comp_assoc`, `id_comp`, `comp_id` | 分次 sheaf Hom 已有 comp/id 和外延判据，缺少整体等式；corner/primitive 证明重复逐点计算。结合律不设 simp，单位消去设 simp。 |
| 采纳：点态双射的双侧逆 | `Algebra/Module/Equiv/Defs.lean`：`LinearEquiv.comp_symm`, `symm_comp` | 复用已有 `ModuleData.Hom.inverse_map/map_inverse`。同态层的 cancellation 是自然契约；本轮普通导入检查组合不同对象并取 sections，但没有新的生产调用。 |
| 采纳：range 恒等/组合与 inclusion 方块 | `Algebra/Module/Submodule/LinearMap.lean`：`restrict_comp`, `subtype_comp_restrict`；`LinearAlgebra/Quotient/Basic.lean`：`mapQ_id`, `mapQ_comp` | 已有 `rangeMap_projection/val` 给求值，缺少可复合的整体规律。不要求 e/f/q 幂等，也不限定 endomorphism g/h。属于未来复用的 saturation，没有声称新的生产跨对象应用。 |
| 采纳：image 因子分解 | `Algebra/Module/Submodule/Range.lean`：`subtype_comp_rangeRestrict`；`LinearAlgebra/Projection.lean`：`projectionOnto_comp_subtype` | inclusion∘projection=h 是原始数学操作，直接用于 image sections 满射、splitting 往返与 primitive_image；不再由客户端 rfl 得到它。 |
| 采纳：image-section map 的值 | `Algebra/Module/Submodule/LinearMap.lean`：`codRestrict_apply`；既有本项目 `imageSectionEquiv_val` | 原有等价求值无法给等价构造前的 bijectivity 证明使用。新中间边界使该证明和旧等价 API 都不依赖 codRestrict 实现。 |
| 采纳：corner 压缩的乘法与 sandwich | `LinearAlgebra/Projection.lean` 的 projection/subtype retraction；`LinearMap.comp_assoc` | `downEnd_comp` 表明乘法须插入 ambient projector，实际用于 downEnd_idempotent；`liftEnd_downEnd` 给两侧 projector 的整体公式，实际用于 lift_down。原 compress_liftEnd 已提供 retraction，不添同义规则。 |
| 不采纳：更多 zero/add/smul 排列 | 同一 LinearMap 家族有相应代数结构 | 零复合可独立补，但未发现值得优先处理的生产重复；add/smul 还需建立 sheaf Hom 的 Add/Module 结构，会扩大任务。此次不为补全表格引入它们。 |
| 不采纳：所有逆的排列/复合逆包装 | `LinearEquiv` 有更完整的逆运算族 | 双侧消去已足以推导需要的等式；当前无真实新消费者，不再机械列排列。 |
| 不采纳：新的 ext、category 或 functor 实例 | mathlib 提供完整分类式框架 | 已有 `Hom.eq_of_maps`、`ModuleData.Hom.eq_of_map_eq`、标准 ext 足够；此次不为三条函子规律引入框架。 |
| 不采纳：再次铺开 support/tensor/系数求值 | 前五轮已覆盖所检查的计算接口 | 未发现值得优先引入的新生产语义边界；不重复前五轮试验或宣称一般 tensor 已有新跨对象用途。 |

## 实际生产代码

旧 `Hom.imageSectionMap_bijective` 的满射证明通过两层 `Subtype.ext; rfl` 完成。
现在先使用 `imageSectionMap_val`，再经第四轮 `sectionMap_comp` 与本轮 image 分解：

```lean
  · rintro ⟨s,m,rfl⟩
    refine ⟨h.imageProjection.sectionMap Ω m,?_⟩
    apply Subtype.ext
    rw [h.imageSectionMap_val]
    change ((h.imageInclusion.sectionMap Ω).comp (h.imageProjection.sectionMap Ω)) m = _
    rw [← Hom.sectionMap_comp, h.imageInclusion_comp_imageProjection]
```

旧 `Hom.primitive_image` 的 `s.projector=p` 由逐点 rfl 得出；现在使用
`p.imageSplit_projector hv he`。`imageTo_toImage_vertex/edge` 使用 image 分解和旧
projector 求值/split 规律，不展开 range 投影实现；反向 `toImage_imageTo_*` 复用
`range_fixed` 替代成员见证拆解，但仍用 `change` 连接公开坐标，此处表示依赖尚未完全消除。

旧 `SplitIn.lift_down` 为每次使用临时证明一个逐点 sandwich 等式；现在是：

```lean
 theorem SplitIn.lift_down (s : SplitIn B C) (f : Hom C C)
    (hf : f.comp s.projector=f) (hf' : s.projector.comp f=f) :
    s.liftEnd (s.downEnd f)=f := by
  rw [s.liftEnd_downEnd, hf, hf']
```

`liftEnd_downEnd` 通过整体结合律证明；primitive 的两组单位证明复用单位规则，
且复用第五轮 `liftEnd_id`。不是所有证明都变短；明确的转换有时多于 rfl。
本轮收益是提取可组合规律，仍保留 vertex/edge、subtype 和底层向量作为公开计算契约。
7 条新 simp 规则消去单位、双侧逆、range 恒等、image-split projector 和 section 值；其余 6 条规律显式使用。
沿用 `Hom.eq_of_maps`、`ModuleData.Hom.eq_of_map_eq`、`LinearMap.ext`、`Subtype.ext` 和 funext，
不增加 ext 属性或实例。

## 实现变化与冻结对照

结果：逆向构造先把 section-map range 上的 image projection 证明为双射，再取其逆，
代替原先 inclusion 的 codRestrict 构造。仅重证 `Hom.imageSectionMap_val`：由逆恒等式及
image 因子分解恢复相同的 inclusion 值，对所有输入成立；其后从
`Hom.imageSectionMap_bijective` 起至文件结尾的整段生产源码保持字节相同，并重新 elaboration 通过。
冻结对象是这个 SHA256 绑定的尾段；producer 定义和一条 API 证明为试验修改。

另两份整文件冻结的 `Models`、`AdjointSheaf` 和普通导入/19 项公理闭包均通过。
旧模块使用同一逆向实现并补入同样的两条 API 边界，保留旧证明正文；它在 bijectivity 的
`congrFun` 类型衔接、满射证明的 `rfl` 和旧 `imageSectionEquiv_val` 的 `rfl` 三处失败。
日志没有缺失工件或可见性错误。两个外部旧文件均通过（它们本轮未改），不算区分收益。
直接压力证据落在同一 producer 内的真实 image-section 客户端，不延伸为所有四族的稳定性承诺。

初稿先遇到 ring/map 推断问题，补类型后又显露缺少 bijectivity 证明；正式试验改为显式局部
等价及其逆恒等式。失败原型日志与成功恢复记录保留；一次路径错误重复启动了未修正原型，
没有新增语义信息，不作 API 收益，早先那一次的独立时间未保存。API 修补的证明比原 rfl 长，
本轮不宣称行数或运行性能节省。

脚本 `api_saturation_trial.py` 使用正常 module setup 的 scratch
工件，不提供选定 producer 的 `.olean.private`；与构建互斥，在 finally 恢复正式源码与工件。
变体从 range 上的投影先构造双射，再取逆，代替从 image inclusion 正向构造 section-range map。
这两种由同一分裂诱导的等价，正向计算路径不同；变体不进入生产实现。
所有正式源码、冻结客户端字节及所记录正常 `.olean*` 工件均在 finally 中恢复且哈希相同。
变体只检查所列尾段、两份文件和普通入口，未在变体下全库重编译或复验全部历史生成名称；
正式版本另行通过完整 84 阶段验收。

## 验收与成本

当前完整构建通过，原始接口 4001→4014：恰好 13 条数学定理新增，零生成新增，
无旧声明缺失、类型或归属变化。84/84 阶段验收全部通过；19 项本轮/消费者公理闭包
仅使用 `propext`、`Classical.choice`、`Quot.sound`。所有适用历史兼容与回归检查通过，
没有放宽旧公开契约。历史检查比较当前结果与不可变记录，不是重编退休的历史项目。
原始比较器因新增返回 `passed=false`；精确核对器要求这 13 条完整记录与登记完全一致，
且旧记录零变化，才接受本轮增量。
首次原始导出为 4020 条：13 条数学定理之外，还多出 `ModuleData.rangeMap.congr_simp`
及 `SplitIn.downEnd.eq_1`、`imageTo.eq_1`、`liftEnd.eq_1`、`projector.eq_1`、`toImage.eq_1`。
精确检查拒绝这六条未登记的生成声明；没有扩大豁免。它们来自新证明中 `simp` 展开定义与
依赖参数的自动 congruence 生成，随后改用显式等式传递、有限的 `change` 和 `Hom.comp_assoc`，
避免把这些实现辅助名称带入正式接口。首份完整导出、差异和失败日志保留。
另一次从仓库根目录启动增量构建的命令在工具链选择前立即退出，未产生编译结果；
改回项目内的既有串行环境执行。该启动失败不计入 API 收益。

新 source/type 层只登记本轮两个文件与精确声明，不刷新前五轮记录、不作前缀豁免。
历史输入仅允许明确 Git 提交和哈希；当前完整产品仍要求等于新 overlay。
本轮逆向视图只允许两个生产文件的已登记精确增量和三个已列明历史源码哈希；
回归拒绝额外字节、缺失或变化的声明记录。原各轮基准与记录不刷新。
数学源码差异为两个文件 +152/−32 行（净 +120）；这是文本规模，不是复杂度或质量指标。

保存环境最初缺失 `.lake` 与 Lean 工具链缓存，按 `scripts/setup.sh` 恢复固定版本和官方缓存，
没有更新 pins、重跑前五轮试验或全编 mathlib。复现：

```sh
source scripts/env.sh
scripts/check.sh all
cd experiments/kl-for-mathlib
python3 api_saturation_trial.py  # 不与构建并行
```


| 实测操作 | 墙钟秒 | 范围 |
| --- | ---: | --- |
| 恢复后首次完整构建 | 2202.355 | 9186 目标；初稿随后消除六条生成辅助声明；最大子进程 RSS 3372272 KiB |
| 最终完整增量构建 | 331.959 | 9186 目标；当前数学源码；最大子进程 RSS 3329396 KiB |
| 最终全量验收 | 685.888 | 84 阶段；121 项回归；最大子进程 RSS 7781988 KiB |
| 最终预检完整接口导出 | 20.471 | 导入工件与序列化两条命令 |
| 成功冻结实现试验 | 145.018 | 8 次 Lean 调用；最大子进程 RSS 3316716 KiB |
| 两份保留的失败原型 | 51.510 | 不计同型重复启动的未保存时间；不是 API 收益 |

最终热构建 7.260 秒。setup 和全部局部命令没有单独完整计时；这些行不是总会话成本，
也不能与旧环境直接作性能比较。token 遥测不可用，不估算 token 或性能收益。

固定证据：

- [执行输入绑定](evidence/api-saturation/accepted-inputs.json)、[核对摘要](evidence/api-saturation/verification.json)、[最终完整性核对](evidence/api-saturation/final-integrity.json)、
  [84 阶段完整命令/退出码](evidence/api-saturation/accepted/stages.json)、[全量验收指标](evidence/api-saturation/experiment/full-checks.json)。
- [最终构建指标](evidence/api-saturation/experiment/final-build.json)、[完整构建日志](evidence/api-saturation/experiment/final-build.log)、
  [原始接口差异](evidence/api-saturation/experiment/raw-interface-diff.json)、[精确登记核对](evidence/api-saturation/accepted/api-saturation-full-records.log)。
- [试验对照](evidence/api-saturation/experiment/trial/comparison.json)、[一条 API 修补](evidence/api-saturation/experiment/trial/api-proof.patch)、
  [冻结 producer 尾段](evidence/api-saturation/experiment/trial/frozen-producer-client-tail.json)、[旧证明语义失败](evidence/api-saturation/experiment/trial/old-module-clients.log)、
  [恢复哈希](evidence/api-saturation/experiment/trial/restoration.json)。
- [未接受的六条生成声明](evidence/api-saturation/experiment/first-export-generated/raw-interface-diff.json)、
  [锁定 mathlib 参照与哈希](evidence/api-saturation/experiment/mathlib-patterns.json)、
  [main 及前五轮分支远端记录](evidence/api-saturation/experiment/remote-refs-before-final.log)、[归档清单](evidence/api-saturation/manifest.json)。

已核对代码输入与执行提交、全部归档哈希/压缩往返、报告链接及正常工件恢复记录。
main 仍为 `178ccf2`，前五轮分支保留；没有 PR、合并、强推或未解决验收阻塞。


## 后续停止边界

建议本轮完成后停止按排列继续补接口，等待新证明给出下一批组合需求。
目前逆规律与三个 range 整体规律已经属于面向未来的补齐；其余逆排列可由两侧消去推导，
更多加法/标量规律又会涉及尚未建立的 Hom 代数结构。此次已经找到的实际重复集中于
image/corner 的组合，这支持有界完成当前家族，而不支持再凑一轮等量声明。
下一次优先依据新生产证明和明确的结构设计重新评估。
