# 第六轮：已有数学 API 的合理补齐

基线 `78cdaf405dbf1dcf07eed5490469b7a8704c93f0`，独立分支
`experiment/api-saturation-20261024`。环境已从该远端基线恢复，初始工作区干净。
唯一维护的 Lean 项目仍是 `experiments/kl-for-mathlib`。旧分支保留，不创建 PR、不合并、不强推。
代码检查点已通过完整构建、普通导入、19 项公理闭包及精确接口/8 项相关回归检查。
实现试验与全量验收待完成；执行 SHA 与验收证据在完成后补入。

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
`p.imageSplit_projector hv he`。分裂像的 vertex/edge 往返也经过 image 分解和旧
projector 求值/split 规律，不再展开 range 投影实现。

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

## 实现变化与冻结对照

待试验完成后记录结果。脚本 `api_saturation_trial.py` 使用正常 module setup 的 scratch
工件，不提供选定 producer 的 `.olean.private`；与构建互斥，在 finally 恢复正式源码与工件。
变体从 range 上的投影先构造双射，再取逆，代替从 image inclusion 正向构造 section-range map。
这两种由同一分裂诱导的等价，正向计算路径不同；变体不进入生产实现。

## 验收与成本

当前完整构建通过，原始接口 4001→4014：恰好 13 条数学定理新增，零生成新增，
无旧声明缺失、类型或归属变化。全量历史兼容与回归验收待完成。
首次原始导出为 4020 条：13 条数学定理之外，还多出 `ModuleData.rangeMap.congr_simp`
及 `SplitIn.downEnd.eq_1`、`imageTo.eq_1`、`liftEnd.eq_1`、`projector.eq_1`、`toImage.eq_1`。
精确检查拒绝这六条未登记的生成声明；没有扩大豁免。它们来自新证明中 `simp` 展开定义与
依赖参数的自动 congruence 生成，随后改用显式等式传递、有限的 `change` 和 `Hom.comp_assoc`，
避免把这些实现辅助名称带入正式接口。首份完整导出、差异和失败日志保留。
另一次从仓库根目录启动增量构建的命令在工具链选择前立即退出，未产生编译结果；
改回项目内的既有串行环境执行。该启动失败不计入 API 收益。

新 source/type 层只登记本轮两个文件与精确声明，不刷新前五轮记录、不作前缀豁免。
历史输入仅允许明确 Git 提交和哈希；当前完整产品仍要求等于新 overlay。

保存环境最初缺失 `.lake` 与 Lean 工具链缓存，按 `scripts/setup.sh` 恢复固定版本和官方缓存，
没有更新 pins、重跑前五轮试验或全编 mathlib。复现：

```sh
source scripts/env.sh
scripts/check.sh all
cd experiments/kl-for-mathlib
python3 api_saturation_trial.py  # 不与构建并行
```

token 遥测不可用，不估算 token 或性能收益。

## 后续停止边界

建议本轮完成后停止按排列继续补接口，等待新证明给出下一批组合需求。
目前逆规律与三个 range 整体规律已经属于面向未来的补齐；其余逆排列可由两侧消去推导，
更多加法/标量规律又会涉及尚未建立的 Hom 代数结构。此次已经找到的实际重复集中于
image/corner 的组合，这支持有界完成当前家族，而不支持再凑一轮等量声明。
这不是否定未来扩展；下一次优先依据新生产证明和明确的结构设计重新评估。
