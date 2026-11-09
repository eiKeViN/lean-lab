# API 与真实下游源码摘录

本轮固定提交`2d8a70eac578ec65047e50caa653bad4cf6d5755`；上轮固定提交`bdbca7ff639bc32f94a85647c88cb16d9e80b294`。
以下均从相应Git对象逐行截取，保留原样缩进，省略文件外层namespace、universe及variable上下文。
这些是实际声明/证明，不是改写成更短的演示版，也不是可独立编译的小文件。
完整可复现验证见[本轮实验报告](mathematical-api-families.md)。

## restriction 与零延拓

上下文为Sheaf命名空间，B是G上的sheaf，K是ambient顶点集合。
两个接口把一次性的子图边/cast论证与延拓的数学步骤分开；retraction只是一侧恒等式。

[两个实际API](https://github.com/eiKeViN/lean-lab/blob/2d8a70eac578ec65047e50caa653bad4cf6d5755/experiments/kl-for-mathlib/ForMathlib/Combinatorics/MomentGraph/Sheaf/Restriction.lean#L49)，原文件第49–70行：

```lean
/-- Restriction is a retraction of extension by zero. -/
@[simp] theorem restrict_extendAssignment (f : (B.restrict K).Assignment) :
    B.restrictAssignment K (B.extendAssignment K f) = f := by
  funext x
  exact B.extendAssignment_mem K f x

/-- Compatibility on a subgraph set is exactly compatibility on its ambient image. -/
theorem restrict_compatible_iff (Ω : Set K) (f : B.Assignment) :
    (B.restrict K).CompatibleOn Ω (B.restrictAssignment K f) ↔
      B.CompatibleOn (Subtype.val '' Ω) f := by
  constructor
  · intro hf e hs ht
    obtain ⟨x,hx,hxe⟩ := hs
    obtain ⟨y,hy,hye⟩ := ht
    have hsk : G.source e ∈ K := hxe ▸ x.property
    have htk : G.target e ∈ K := hye ▸ y.property
    let ee : {e : E // G.source e ∈ K ∧ G.target e ∈ K} := ⟨e,hsk,htk⟩
    have hsx : (inducedGraph G K).source ee = x := Subtype.ext hxe.symm
    have hty : (inducedGraph G K).target ee = y := Subtype.ext hye.symm
    exact hf ee (hsx ▸ hx) (hty ▸ hy)
  · intro hf e hs ht
    exact hf e.val ⟨_,hs,rfl⟩ ⟨_,ht,rfl⟩
```

[实际extend_compatible](https://github.com/eiKeViN/lean-lab/blob/2d8a70eac578ec65047e50caa653bad4cf6d5755/experiments/kl-for-mathlib/ForMathlib/Combinatorics/MomentGraph/Sheaf/Restriction.lean#L87)，原文件第87–92行：

```lean
 theorem extend_compatible (Ω : Set K) (f : (B.restrict K).Assignment)
    (hf : (B.restrict K).CompatibleOn Ω f) :
    B.CompatibleOn (Subtype.val '' Ω) (B.extendAssignment K f) := by
  apply (B.restrict_compatible_iff K Ω (B.extendAssignment K f)).mp
  rw [B.restrict_extendAssignment K f]
  exact hf
```

## 同构对assignment的输运

前一块位于Sheaf.Iso命名空间，j : Iso B C。
后一块位于Structure文件的Sheaf.Iso命名空间；它是实际flabbiness输运证明。
逆向双射扰动中只重证assignments_apply，这份Structure整文件冻结通过。

[点值API](https://github.com/eiKeViN/lean-lab/blob/2d8a70eac578ec65047e50caa653bad4cf6d5755/experiments/kl-for-mathlib/ForMathlib/Combinatorics/MomentGraph/Sheaf/Iso.lean#L44)，原文件第44–49行：

```lean
/-- Transport of an assignment is pointwise transport at the vertices. -/
@[simp] theorem assignments_apply (f : B.Assignment) (x : V) :
    j.assignments f x = j.vertex x (f x) := by rfl

@[simp] theorem assignments_symm_apply (f : C.Assignment) (x : V) :
    j.assignments.symm f x = (j.vertex x).symm (f x) := by rfl
```

[实际flabby输运](https://github.com/eiKeViN/lean-lab/blob/2d8a70eac578ec65047e50caa653bad4cf6d5755/experiments/kl-for-mathlib/ForMathlib/Combinatorics/MomentGraph/Sheaf/Structure.lean#L124)，原文件第124–133行：

```lean
 theorem flabby (hb : B.Flabby) : C.Flabby := by
  intro Ω hΩ f hf
  have hsf : B.CompatibleOn Ω (j.assignments.symm f) := by
    apply (j.compatible_iff Ω _).mp
    simpa only [LinearEquiv.apply_symm_apply] using hf
  obtain ⟨g,hg,hgf⟩ := hb Ω hΩ (j.assignments.symm f) hsf
  refine ⟨j.assignments g,(j.compatible_iff Set.univ g).mpr hg,?_⟩
  intro x hx
  rw [j.assignments_apply,hgf x hx,j.assignments_symm_apply]
  exact (j.vertex x).apply_symm_apply _
```

## 局部kernel与product/pi的分量

前两块是Sheaf命名空间API；后一块是Models中现有pi_upwardKernel_iff的实际改造。
交核表示扰动中只重证mem_upwardKernel_iff，六份新客户端（包括Models）冻结通过。

[局部约束与完整核](https://github.com/eiKeViN/lean-lab/blob/2d8a70eac578ec65047e50caa653bad4cf6d5755/experiments/kl-for-mathlib/ForMathlib/Combinatorics/MomentGraph/Sheaf/Iso.lean#L123)，原文件第123–133行：

```lean
/-- Local kernel constraints, independent of the submodule construction. -/
theorem mem_upwardKernel_iff (x : V) (F : Set (Outgoing (G := G) x)) (v : B.vertex x) :
    v ∈ B.upwardKernel x F ↔ ∀ e ∈ F, B.stalkMap x v e = 0 := by rfl

/-- Imposing every outgoing constraint is the kernel of the full stalk map. -/
theorem upwardKernel_univ (x : V) :
    B.upwardKernel x Set.univ = LinearMap.ker (B.stalkMap x) := by
  ext v
  rw [mem_upwardKernel_iff, LinearMap.mem_ker]
  simp only [Set.mem_univ, true_implies]
  exact ⟨fun h => funext h, fun h e => congrFun h e⟩
```

[pi stalk分量](https://github.com/eiKeViN/lean-lab/blob/2d8a70eac578ec65047e50caa653bad4cf6d5755/experiments/kl-for-mathlib/ForMathlib/Combinatorics/MomentGraph/Sheaf/Pi.lean#L27)，原文件第27–33行：

```lean
/-- Stalk constraints of a dependent product are coordinatewise constraints. -/
@[simp] theorem pi_stalkMap_apply (B : ι → Sheaf.{u,v,w,z} (R := R) G)
    (x : V) (f : (pi B).vertex x) (e : Outgoing (G := G) x) (i : ι) :
    (pi B).stalkMap x f e i = (B i).stalkMap x (f i) e := by
  rcases e with ⟨e,he⟩
  subst x
  rfl
```

[实际pi局部核判据](https://github.com/eiKeViN/lean-lab/blob/2d8a70eac578ec65047e50caa653bad4cf6d5755/experiments/kl-for-mathlib/ForMathlib/Combinatorics/MomentGraph/Sheaf/Models.lean#L163)，原文件第163–172行：

```lean
theorem pi_upwardKernel_iff {ι : Type*} (B : ι → Sheaf.{ur,uv,ue,uz} (R := R) G)
    (x : V) (F : Set (Outgoing (G := G) x)) (v : (pi B).vertex x) :
    v ∈ (pi B).upwardKernel x F ↔ ∀ i, v i ∈ (B i).upwardKernel x F := by
  simp only [mem_upwardKernel_iff]
  constructor
  · intro h i e he
    exact (pi_stalkMap_apply B x v e i).symm.trans (congrFun (h e he) i)
  · intro h e he
    funext i
    exact (pi_stalkMap_apply B x v e i).trans (h i e he)
```

## 上轮：配对的系数输运

上下文为GradedSheaf命名空间，e为系数代数等价，he保持分次。
配对公式把输运还原为旧配对；实际对称性证明由两次该公式和旧对称性组成。
本轮没有修改这两个文件。

[配对输运API](https://github.com/eiKeViN/lean-lab/blob/bdbca7ff639bc32f94a85647c88cb16d9e80b294/experiments/kl-for-mathlib/ForMathlib/Combinatorics/MomentGraph/GradedSheaf/Duality.lean#L343)，原文件第343–349行：

```lean
 /-- Pairing transport is coefficient transport after inverse section transport. -/
 theorem PerfectPairing.coefficientChange_apply {S : GradedSheaf (𝓐 := 𝓐) G} {d : ℤ}
     (p : PerfectPairing S d) (m n : (GradedSheaf.coefficientChange e he S).forget.sections Set.univ) :
     (p.coefficientChange e he).pairing m n =
       e (p.pairing ((coefficientChangeSections e he S Set.univ).symm m).val
         ((coefficientChangeSections e he S Set.univ).symm n).val) := by
   exact CoefficientChange.pairingEquiv_apply e p.pairing _ _
```

[实际对称配对输运](https://github.com/eiKeViN/lean-lab/blob/bdbca7ff639bc32f94a85647c88cb16d9e80b294/experiments/kl-for-mathlib/ForMathlib/Combinatorics/MomentGraph/GradedSheaf/Uniqueness.lean#L124)，原文件第124–130行：

```lean
 @[expose] def SymmetricPerfectPairing.coefficientChange {S : GradedSheaf (𝓐 := 𝓐) G} {d : ℤ}
    (p : SymmetricPerfectPairing S d) : SymmetricPerfectPairing (coefficientChange e he S) d where
  toPerfectPairing := p.toPerfectPairing.coefficientChange e he
  symmetric m n := by
    exact (PerfectPairing.coefficientChange_apply e he p.toPerfectPairing m n).trans
      ((congrArg e (p.symmetric _ _)).trans
        (PerfectPairing.coefficientChange_apply e he p.toPerfectPairing n m).symm)
```
