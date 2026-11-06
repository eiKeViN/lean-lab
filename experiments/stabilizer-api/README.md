# feat(stabilizer): 用通用系数映射和可组合搬运完善下游接口

本实验基于固定版本 Lean-QEC，目标是让构造、生成元计算、二元线性代数和重编号共用一套公开接口。源码在本目录的 `overlay/` 中完整保留；`environment/` 是可重建的运行工作区。

返回 [lean-lab 项目入口](../../README.md)。本实验使用独立的 Lean **4.30.0-rc2**，不会升级 KL 或量子概率实验的工具链。

## 为什么改

一个稳定子码已经提供有效性与交换性保证，下游应该能直接用它们做代数、计算生成元组合、转换到二元表示，并在变换码后复用结论。

原接口把交换性保存在记录字段中，使用者还要连接实例、成员证明与表示。初步重构提供了 `C.Stabilizer`、`C.Presentation`、二元桥和单次变换。本轮进一步接通通用系数线性接口和变换的组合规律，让用户可以连续完成一项任务。

## 改了什么

### 构造只接收独立条件，稳定子类型接通通用代数

`StabCode` 保存子群与排除 `−I` 的证明；交换性由 qubit Pauli 群的性质推出。支持从子群、校验矩阵、独立交换行、共同固定的非零向量及其生成元构造码。

`C.Stabilizer` 是保留码参数的普通 `def`，沿用原子群的运算数据，并提供交换群、有限性、有限类型和可判定相等。`C.toPauli`、`C.toUnitary` 是结构化映射；`C.mul_comm` 服务于已有环境元素与成员证明。

```lean
example (C : StabCode n) (s t : Finset ι) (f g : ι → C.Stabilizer) :
    C.prod s f * C.prod t g = C.prod t g * C.prod s f :=
  mul_comm _ _
```

本轮将 `C.prod` 的默认结果统一为 `C.Stabilizer`；显式需要环境 Pauli 时用 `C.prodPauli` 或 `C.toPauli`。

### 所有有限 presentation 都有系数线性映射

`P : C.Presentation ι` 保存选定生成元及其生成性。对任意有限 `ι`，提供：

```lean
P.coefficientLinearMap
-- (ι → ZMod 2) →ₗ[ZMod 2] Additive C.Stabilizer

P.combination_add
P.combination_surjective
P.coefficientLinearMap_surjective
P.range_coefficientLinearMap
```

定义复用 mathlib 的 `Fintype.linearCombination`。系数映射与已有 `P.combination` 相符，生成性推出满射；矩阵的组合满射性直接复用这个通用结论。

系数线性映射的核表示所有生成元关系。用户可以直接调用线性代数，例如完整流程中的关系空间维数定理：

```lean
theorem relations_dimension [Fintype ι] (C : StabCode n) (P : C.Presentation ι) :
    Module.finrank (ZMod 2) (LinearMap.ker P.coefficientLinearMap) + C.numGenerators =
      Fintype.card ι := by
  have h := LinearMap.finrank_range_add_finrank_ker P.coefficientLinearMap
  rw [P.range_coefficientLinearMap, finrank_top, C.binaryLinearEquiv.finrank_eq] at h
  simpa [StabCode.numGenerators, add_comm] using h
```

### 二元表示、码与生成元的搬运可以组合

`C.binaryLinearEquiv` 接通稳定子的加法表示与二元子空间。一般环境群等价通过 `C.map`、`C.mapStabilizer` 和 `P.map` 同时搬运对象、元素与生成元；`C.mapStabilizerLinearEquiv` 还给出线性等价。

`P.coefficientLinearMap_map` 证明系数映射与搬运相容，因此生成元关系也随变换保留。

量子比特重编号在 Pauli、码、稳定子和 presentation 层都有恒等、复合、逆变换规律。规范化方向是把连续变换合为一次复合。码相等带来的载体对齐由 `StabCode.stabilizerCongr` 和 `P.congrCode` 处理。

```lean
example (C : StabCode n) : C.reindex (Equiv.refl _) = C := by simp

example (C : StabCode n) (P : C.Presentation ι) (σ : Equiv.Perm (Fin n)) :
    ((P.reindexQubits σ).reindexQubits σ.symm).congrCode (C.reindex_symm σ) = P := by
  simp

example (C : StabCode n) (σ τ : Equiv.Perm (Fin n)) (d : ℕ) (hd : d ≤ C.distance) :
    d ≤ ((C.reindex σ).reindex τ).distance := by simpa using hd
```

还补齐了 `toUnitary (ofMem …)` 的化简入口。

## 借鉴的 mathlib 实践

| 实践 | 本实验的采用方式 |
| --- | --- |
| [`HierarchyDesign` 的 commutative subobjects 说明](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Algebra/HierarchyDesign.lean#L266) | 稳定地表示交换子对象的载体直接提供 `CommGroup`；需要时仍用有名字的交换性定理处理环境元素。由维护者提供搜索入口与桥接。 |
| [`AddEquiv.module` 与 `AddEquiv.linearEquiv`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Algebra/Module/TransferInstance.lean) | 沿已有加法等价传输模结构，保留稳定子的现有加法运算；在一个位置安装线性接口。 |
| [`Fintype.linearCombination`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/LinearAlgebra/Finsupp/LinearCombination.lean#L313) | 生成元组合直接成为标准线性映射；下游使用核、像、满射与秩—零化度定理。 |

## 完整下游任务与阅读入口

主入口是 `import LeanQEC.Stabilizer.API`。

| 文件 | 任务 |
| --- | --- |
| [Interface.lean](overlay/LeanQEC/Stabilizer/Interface.lean) | 稳定载体、代数结构、typed 产品与环境映射 |
| [Constructors.lean](overlay/LeanQEC/Stabilizer/Constructors.lean) | 自然证书与独立交换行构造 |
| [Generators.lean](overlay/LeanQEC/Stabilizer/Generators.lean) | presentation、码字与 normalizer 入口 |
| [BinaryBridge.lean](overlay/LeanQEC/Stabilizer/BinaryBridge.lean) | 双向二元桥、通用系数线性映射与满射 |
| [Transport.lean](overlay/LeanQEC/Stabilizer/Transport.lean) | 一般搬运、组合规律与系数自然性 |
| [Reindex.lean](overlay/LeanQEC/Stabilizer/Reindex.lean) | 量子比特排列、各层组合律与码距保持 |
| [PublicTypes.lean](overlay/LeanQEC/Stabilizer/Examples/PublicTypes.lean) | 可编译的公开类型契约 |
| [PresentationWorkflow.lean](overlay/LeanQEC/Stabilizer/Examples/PresentationWorkflow.lean) | 非矩阵构造、重复生成元关系、秩与零化度、重编号、码距界 |
| [DownstreamAPI.lean](overlay/LeanQEC/Stabilizer/Examples/DownstreamAPI.lean) | 其他常用下游示例与关键公理依赖打印 |
| [前后对照](comparison/README.md) | 原始旧接口与当前接口的独立编译对照 |
| [评审整改](REVIEW.md) | 评审意见、采取的修改与相应证据 |

最终收益是：用户提供数学数据、有效性条件以及生成元/排列等主动选择；库负责公共实例、成员资格、表示桥与变换后的证明连接。

## 复现

先安装仓库固定的 Lean 工具链与 `git-lfs`，然后从本目录执行：

```bash
python3 scripts/setup.py --workspace ../../../lean-qec-stabilizer-work --with-regressions
python3 scripts/check.py
python3 scripts/profile_instances.py
```

`setup.py` 下载固定上游，核查原始源码并施加可审阅 overlay，写入本实验自己的精简 Lake 配置，然后取得官方 Mathlib 缓存。`--workspace` 把运行工作区放在指定目录，以 `environment/` 链接访问。只下载定向回归需要的六份 LFS 证明，不下载所有码的证书。已有正确缓存时可显式加 `--skip-cache`。

只检查核心接口时，使用 `setup.py`（省略 `--with-regressions`）和 `check.py --core-only`。源码身份、类型/编译、公理打印与前后对照的结果分别记录在 `results/`。

## 边界、兼容性与验证口径

- 固定 Lean-QEC [8d115519](https://github.com/VerifiedQC/Lean-QEC/tree/8d115519b471b71a21fbdddf5341d8203b841cc9)，Lean `v4.30.0-rc2`，mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`。全部 74 份原始 `LeanQEC` Lean 源码记录在 [baseline-sources.json](provenance/baseline-sources.json)，所有活动 overlay 记录在 [overlay-sources.json](provenance/overlay-sources.json)。身份覆盖与实际构建覆盖分别报告。
- 删除 `h_comm` 字段后，旧三参数构造与三字段解构需要迁移；`C.h_comm` 读取和旧具名构造器保留。相比初步实验，`C.prod` 现在返回 typed stabilizer；原环境输出由 `C.prodPauli` 提供。
- Presentation 的生成元选择与生成性证明仍需提供，满射性不要求生成元线性无关。矩阵原始二元像定理只要求交换性，继续保留；presentation 版本面向已构造的合法码。
- 二元逆映射、有限类型和传输模结构采用非计算性定义。这些接口面向形式化数学，未提供高效解码或枚举算法。
- 原始上游源码和依赖构建产物可复用；旧 `Basic/CSS` 在独立导入目录中重新编译，旧侧消费代码与新侧消费代码分别检查。比较不要求存在任何未发布的原型 Git 提交。
- 定向构建包括 API 示例、公开类型、完整 workflow、Steane、Golay、BB54、平面码、环面码及其依赖，不等于全仓库构建。最终运行范围和状态见 [验收记录](evidence/acceptance.json)。本实验没有重建其他 lean-lab 项目。
- 关键打印声明检查 `sorryAx`；二元桥与相关结论保留基线有限 Pauli 表中的 `native_decide` 公理项。没有声称所有依赖都经过独立 kernel 重检。
- 本次执行复用固定上游快照与已有 Mathlib 缓存，未另做从空目录开始的联网安装验收。运行器的 `/proc` 命名空间需要一份仅调整本进程 executable 路径查询的 [兼容代码](evidence/runner-compat.c)。嵌套运行目录曾出现源码还原，相关 [失败摘要](evidence/nested-workspace-failure.json) 保留；最终验收使用分离的运行目录并核查构建前后的源码。
- 否定实例搜索从通过性测试中移出。预算探针将 `resource_limit`、`no_instance_reported` 等结果分别记录；超时不作为不存在实例的证明，也不据此断言新增性能回归。运行记录见 [实例探针](evidence/instance-outcomes.json)。
- 本目录保留独立工具链与运行目录；不迁入 Alioth，不修改其他项目的依赖。上游 Apache-2.0 许可证保留于 [LICENSE-Lean-QEC](provenance/LICENSE-Lean-QEC)。
