# 小规模语义 API 实验（2026-10-24）

起点为已合并 main `178ccf2a9fa1f0bff04d6b029db1361f881fef33`，分支
`experiment/semantic-api-20261024`。唯一维护项目仍是 `experiments/kl-for-mathlib`。
没有 PR、合并、升级 pin、公共 matcher 包装或全 Mathlib 源码构建。
本轮四项候选不是全库覆盖；expose 数量不是质量指标。

最终通过代码为 `83ae9455fbb51d3022a95c6a517dec475ac31597`；完整 **69阶段验收通过**。
后续提交只归档证据和更新报告，不改生产 Lean 或检查器。四项候选中，API覆盖与交付策略分开判断：
split 的所选客户端覆盖成功但保留计算契约；map 的 sheaf 层覆盖仍不足；baseChangeQuotient
覆盖成功但保留旧公共 eq_1；quotientPullback 交付隐藏，接受明确的一项实现可见性变化。

## 起点与选择

读取根 AGENTS.md、项目 README、module-completion/module-interface-decisions、module import
研究和此前 lemma granularity 报告。仓库内没有附加 AGENTS.md 或 .agents/skills；工作区
`.agents` 为空。初始 checkout 是旧 `work` 分支 `7e28e63`，工作区干净；fetch 后直接从指定
`178ccf2` 建新分支，没有修改 main。Lean/Mathlib pin 保持原值。
环境没有工具链或 `.lake`，使用标准 `scripts/setup.sh` 安装精确版本及官方二进制 cache。

先查源码中已有声明和真实使用点，再选以下四项；包装结构已有的 `ext`、`val`、`equivVal`
已足够，不添 casesOn 的同义包装。`Projective/Range.splitEquiv` 是另一种 range splitting；
Mathlib `Submodule.prodEquivOfIsCompl` 描述两个互补子模，不能直接替代给定右逆的坐标规则。
固定 Mathlib 的 `LinearEquiv.skewProd_apply/skewProd_symm_apply`（LinearAlgebra/Prod.lean
809–815）提供方向性求值规则的先例；Projection.lean 的互补分解有类似分量规则。
这里只借鉴命名与正规形，不声称这些项目 API 已达到 Mathlib 上游接收标准。

## 四项候选与真实下游

| 候选 | 应公开的语义行为、实际用途 | 新增/复用 | 实现边界判断 |
| --- | --- | --- | --- |
| `LocalCover.splitEquiv` | 给定 `g ∘ s = id`，第一坐标为 `g b`，第二坐标为 `b - s (g b)`；逆向以 `s p + k` 重建。用于局部最小自由覆盖、graded kernel 的自由性和分裂保次数 | 新增 `splitEquiv_apply_fst`、`splitEquiv_apply_snd_coe`、`splitEquiv_symm_apply`；复用标准 LinearEquiv 法则 | 交付保留 expose，因为既有普通消费者明确承诺正反向 `rfl`。另作真实 producer 暂时隐藏试验，结果见验收节 |
| `CoefficientChange.map` | 在新系数下作用于同一个向量；`val (map e f m) = f (val m)`，不公开线性映射 record 的构造。用于 graded `changeHom`、等价与配对输运 | 新增 `val_map` 和 `map_id_apply`，复用已有 `CoefficientChange.ext`，标准 equivalence inverse 法则 | 交付保留 expose；隐藏试验中三个小客户端通过，但实际 GradedSheaf.Duality 仍有缺口，不扩大本轮修复范围 |
| `Sheaf.quotientPullback` | 沿命题蕴含预合成函数，并逐点投到主理想商。用于 tensor base-change 自然性进而构造 structureBaseChangeIso | 新增 `quotientPullback_apply`；复用 TensorProduct induction、已有 pi/tensor 求值规则 | 撤下 expose，以逐点规则取代展开 LinearMap.pi/comp/proj |
| `Sheaf.baseChangeQuotient` | 纯张量 `s ⊗ [r]` 映到 `[s·algebraMap r]`。用于 structure sheaf 边模的 base change | 不添定理，复用已有 `[simp] baseChangeQuotient_tmul`、LinearEquiv.injective/apply_symm_apply | 交付保留 expose：纯张量规则覆盖所选证明，但隐藏会使旧公共 baseChangeQuotient.eq_1 消失，严格门禁拒绝该缺失 |

透明对照：`baseChangeQuotient`（保留旧公共方程）、`CoefficientChange.map`（部分覆盖的负面结果）、`CoefficientChange.equivVal`、两个 wrapper 的构造/val/ext、structureSheaf 的
stalk/edge 载体表示和 structureVertexIso 均保留。类型类 transport 仍可按旧计算接口归约，
不把实例推断问题转移给 simp，也不添新 instance/ext 属性。

### 实际证明前后

1. `LocalCover.exists_split_minimal_cover`：原 `change b - s (g b) = b` 和末尾 `rfl`
   改为坐标规则；`Graded.ModuleData.Hom.splitEquiv_graded` 原靠 constructor 后目标自动归约，
   现在明确用第一/第二坐标公式；`Hom.kernel_free_of_split` 用 snd 公式证明 kernel 投影的复合为 id。
   原证明很短，新版略长，收益是抽象边界明确，而不是行数优化。它们依然在真实最小覆盖/graded
   自由性构造链上，并非另造 toy 定理。
2. `Graded.ModuleData.changeHom.graded`：原直接把 `f.graded` 当作目标，要求隐藏 map 的 val
   定义归约；新版通过 `CoefficientChange.val_map` 的等式输运后用同一个 grading 事实。
   `CoefficientChange.Dual.mapEquiv` 的两个逆律也经 val_map；实际 pairingEquiv_apply 原 `rfl`
   改为穿过 map 的语义规则。新证明更显式，兼容隐藏后的 map。全量构建进一步发现真实 `changeTop_split`
   的原 `change` 还依赖两次 coefficient map 的恒等计算；因此补有实际用途的 `map_id_apply`，
   用两次身份规则消掉冗余 transport，再复用原 `changeUnitHom_inv`。这是第六条定理和第七个文件，
   没有为占候选数量加入无用 functor 定理。
   但真实 GradedSheaf.Duality 进一步有 lower/upper 自然性、upperQuotient、flabby、sections 和
   pairing transport 依赖 map 的直接归约。它们提示更高一层的 sheaf evaluation/transport API 缺口；
   从逻辑上 val/ext 足以继续重写这些等式，但 sheaf 层缺少自然的求值/输运规则，
   本轮不把十余处适配变成另一轮大改，也不据此认定 map 永远不能隐藏。故交付恢复 map expose，保留已验证有用的六条 API，
   用独立 artifact overlay 复现“小客户端通过、实际 sheaf 客户端失败”。
3. `baseChangePi_natural` 的 tmul 分支，原先两次 `change` 将实现展开成 quotient mk，最后
   `congrArg` 拼接 scalar formula；新版保留 tensor/pi 求值后，依次重写
   `quotientPullback_apply`、`baseChangeQuotient_tmul`、`quotientPullback_apply`、
   `baseChangePiScalar_tmul`。保留 add 分支和真实 structureBaseChangeIso 调用。后者的 lower/upper 两个字段原来
   靠 quotientPullback 的定义相等衔接；隐藏后分别在 R/S 上用 ext 和逐点 API 证明 lower/upper
   等于对应 quotientPullback，再输运自然性。这四个局部 map 等式不展开 quotientPullback，
   但依赖保留透明的 structureSheaf 表示，明显增加了实现侧证明成本。
   这是本候选的负面证据，不能把“可隐藏”直接解读为“更值得隐藏”。
4. baseChangeQuotient 已有生成元定理，保留现成 API；普通消费者进一步用 injective 和
   apply_symm_apply 导出逆向纯张量公式，验证没有依赖所选 quotient-equivalence 的组合实现。

完整精确差异在 `semantic-api-source.json`（七个生产/客户端文件）及 Git diff。
当前生产 Lean 差异为 7 文件、+114/−23 行（净增 91）；这只是文本规模，不当作证明复杂度指标。

## 自动化与计算契约

六条新增定理均为 `[simp]`，只朝可观察的坐标/val/逐点值化简，不给完整定义标 simp，
不增加反向折叠规则。snd 只在 coercion 到原模块时化简，不拆 kernel 的证明字段。
这些规则消去最外层新操作，右侧不再出现同一个操作；没有新增双向循环。
新定理写 `by rfl`，避免固定 Lean 对裸 `:= rfl` 自动添加 defeq/backward_defeq；
隐藏实现的语义等式不应额外宣称公开 definitional equality。split 的三条公式显式 omit
不必要的 IsLocalRing 假设，可以用于实际非局部的 graded 代数。
纯张量规则复用原有 simp 属性，baseChangePiScalar_tmul 等未为本轮随意加属性。
普通消费者用已有 ext 加 val_map 证明 map 的复合性；未为这种一次组合加新全局 simp 规则。

quotientPullback 撤下 expose 不改变数学命题、定义值或运行时函数，但会打破依赖其定义体的普通现代
`rfl/change` 调用。这是本实验分支明确接受的这一项实现可见性契约调整，不声称完全源码兼容。
`SemanticApiChecks.lean` 为 pullback 保留 `fail_if_success exact rfl` 负对照，再用 API 完成证明。
split 的公开计算契约和既有八项生成名退休策略保持原样。
baseChangeQuotient 的历史 `eq_1` 等名字仍受原门禁保护；本轮消费者显式只用纯张量和
通用 equivalence 法则，不依赖该实现方程。这不是清理全部历史实现泄露或建立完全抽象模块的宣称。

## 有界门禁与复现

`semantic_api.py` 与 hash 绑定的 source manifest 仅接受七个文件的精确旧新编辑。
migrate 的最后一层生成本轮产品；历史 source/proof 检查的输入视图只撤销这七项精确编辑。
其他文件及未登记字节变化仍拒绝。原始历史来源、3902-type snapshot、比较器和既有 manifest 不刷新。
六项新增 theorem 的全记录单独固定于 `semantic-api-types.json`；完整实际导出为 3947 项（相对本轮 main 的3940项新增7项），
去除本轮登记新增的历史对照输入视图仍为3940项。与更早的3947记录数恰好相同，不表示恢复八个退休名字。仅在核对六项数学 API 与一项精确登记的生成 congruence 声明的名字/type/kind/levels/owner 后，从旧比较视图去掉这七项，
没有按名字前缀忽略任意新增声明。
`semantic-api-generated.json` 单独固定 `LocalCover.splitEquiv.congr_simp` 的完整记录；它由实际
simp 使用触发，未手写兼容包装、不算第七条数学 API，也不承诺其名字为稳定数学接口。
首次导出也捕获 baseChangeQuotient.eq_1 缺失，故恢复其 expose，而非豁免真实公共方程。

原 ModernAllTypes.lean 及它的 hash 证据不改。由它派生一个 ignored ordinary exporter，仅为
仅为 quotientPullback 这一名允许 `original kind = def`、`visible = axiom`（module 隐藏正文的表示）；其余类型、名字、
kind、owner、公理和 12 个已有精确 type-pair 约束沿用。派生源码保存在本轮证据中。
这不是所有定义可改成 axiom 的放宽；普通消费者必须证明相应语义且验证隐藏，原始 kind 仍为 def。

原 `ModernStructureCompat` 的旧私有 Iso 构造辅助值在当前 opaque quotientPullback 下确实不能
原样重建：它把 quotientPullback 的自然性证明靠定义相等直接接到 structureSheaf.lower。
该失败保留，不冒称旧实现体在当前 opaque 环境仍可编译。冻结的原消费者/JSON 不改；
本轮派生的历史实现审计仅在辅助值的重建中，将两个精确名字 quotientPullback 和
baseChangePi_natural 指向由 Git 178ccf2 原文提取的两个私有审计副本。20个旧辅助值仍完整
内核检查，135个公共历史名字/type/levels/属性检查仍用实际当前公共名字，没有名字跳过、
通配归一化或公理放宽。真实普通 API 消费者不包含这些审计定义，仍验证 quotientPullback
正文不可见和 rfl 失败。这将“历史实现重建”与“当前公共数学接口/下游”分开，属于本轮
明确记录的有界审计上下文变化，不是完全定义体兼容的声明。

```sh
bash scripts/setup.sh
bash scripts/check.sh static
bash scripts/check.sh all
# 生产构建就绪后可用 warm 重跑全部接口/公理/回归
bash scripts/check.sh warm
# 隔离的真实 producer/client 隐藏对照；先确保没有其他构建运行
source scripts/env.sh
cd experiments/kl-for-mathlib
python3 semantic_api_split_trial.py
python3 semantic_api_split_trial.py --map
python3 semantic_api_split_trial.py --quotient
```

`SemanticApiChecks.lean` 是 module，以普通 import 加载真实生产模块及真实 graded 客户端；
不用 import all。继承的 implementation exporter 仅用于历史完整清单比较，不是隐藏试验的数学消费者。

## 验收、成本与限制

| 验证项 | 实际结果 |
| --- | --- |
| 当前生产构建 | ForMathlib/OAI全部9186 jobs通过；261个生产模块，依赖 pin 不变 |
| 相对指定 main 的完整导出 | 3940→3947；零missing、零type/kind/levels变化、零owner变化；六项数学API与一项生成声明分别登记 |
| 普通 modern 消费者 | quotientPullback正文不可见、rfl负对照成功，语义/组合/逆向tensor证明通过；其他三候选和wrapper保持可见计算控制 |
| 定向公理 | 六项新API、生成congruence与七项实际客户端共14项闭包，只含原三公理 |
| split隔离对照 | 隐藏真实producer通过；旧实际MinimalCover客户端失败；改写后同一客户端及普通消费者通过 |
| map隔离对照 | 隐藏producer及三个实际客户端通过；原GradedSheaf.Duality失败，保留为覆盖不足证据 |
| quotient隔离对照 | 隐藏baseChangeQuotient后实际tensor消费者通过，但旧eq_1不可访问；这是兼容策略取舍，不是所选数学API覆盖失败 |
| 恢复 | 三项试验source与正式工件的记录hash恢复/未变；未另建维护项目，不提交olean缓存 |
| Source/基线 | Git身份、34原始blob、精确源码重建/覆盖、七文件有界编辑与原21文件proof-evolution检查通过 |
| 完整门禁 | 69阶段全部通过；原16项主审计、81项pilot闭包、比较器/分区/演化回归及全部继承批次通过；无sorry、新增公理或unsafe |

旧完整项目没有重新构建；历史来源/冻结type导出重放与当前编译分别报告。135个公共历史
类型的实际检查与20个旧helper的有界历史实现上下文检查见前节，不能把后者解读成旧实现体
在当前opaque环境仍可原样使用。当前生产数学用例与普通API消费者独立于该审计上下文。

| 实测命令/阶段 | wall秒 | 最大子进程RSS KiB | 结果 |
| --- | ---: | ---: | --- |
| 首次编辑期完整构建 | 621.071 | 3295052 | 调试失败，非固定源码benchmark |
| 双quotient隐藏的可编译候选 | 1139.441 | 3376384 | 编译通过；随后接口检查拒绝eq_1缺失 |
| 恢复baseChangeQuotient后的重建 | 121.217 | 3238560 | 通过（重用未改工件） |
| split真实隐藏对照 | 17.328 | 3178380 | 旧失败/新通过，恢复通过 |
| map真实隐藏对照 | 20.982 | 3137572 | 小客户端通过/真实sheaf失败，恢复通过 |
| quotient真实隐藏对照 | 8.130 | 3182180 | tensor API通过/eq_1缺失确认，恢复通过 |
| 最终完整69阶段 | 456.662 | 7781104 | 全部通过 |

[证据manifest](evidence/semantic-api/manifest.json) 记录每项原文/存储SHA与复用位置；
[最终阶段](evidence/semantic-api/accepted/stages.json.gz) 与
[最终输入](evidence/semantic-api/accepted-inputs.json) 固定397个当前项目、脚本、溯源/指令输入及精确pins。
完整原始导出、旧新类型比较、三个试验的真实命令/退出码、normal import派生setup、恢复hash、
原始失败及有界Structure审计源码均保留。相同的完整导出和已有冻结基线按manifest引用复用，不重复存储。

调试中保留的失败：裸 rfl 自动 defeq 属性与 doc/omit 的语法位置；三条 split 公式误带
IsLocalRing；默认 implicit 透明度下结构载体/实例与 toFun 的重写匹配；quotientPullback
与透明 structureSheaf 的边界衔接；真实 changeTop_split 的两次恒等输运；隐藏 map 后
实际 GradedSheaf.Duality 的剩余缺口。还有一次过早并行 producer rebuild 与全库读工件
竞争，导致 UpperSections 找不到临时被替换的 olean；随后完全串行重建，不为此改数学代码。
前几次构建发生在编辑期间，不能当作固定源码的性能基准。最终验收另绑定固定输入。

环境从无工具链/依赖缓存开始。setup 成功但没有独立计时器，精确初始化 wall time 不可得；
日志的文件系统时间跨度不冒充完整命令计时。后续命令使用 measure.py 或阶段计时记录。
时间包含编译锁排队，各命令有重叠，不能直接相加当总经过时间；RSS 是最大子进程值，
不是容器总峰值。既有 module-completion 的 UpperSections job 记录为948秒（含排队），
仅作已有昂贵模块的背景，不据此主张本轮加速/回退。

不宣称全库所有定义适合隐藏，也不宣称本小实验测得编译速度提升。token 无遥测，不可得。


结论限于这四项候选：小型求值/坐标API确实可支持真实数学下游，并不要求一律隐藏定义。
map的剩余工作是更高层sheaf求值/输运API；baseChangeQuotient若未来明确允许旧eq_1退出稳定
契约，可在不补新数学定理的前提下隐藏。本轮保守保留其兼容承诺，不等同于接口设计失败。
quotientPullback的隐藏可行，但四个局部R/S桥接和历史实现审计适配是实际维护成本，不据此推广
全库unexpose策略。实验已完成，无环境/权限或未决执行阻塞；上述候选缺口是结果，不是未完成验收。
