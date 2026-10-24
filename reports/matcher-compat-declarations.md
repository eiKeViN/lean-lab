> **历史提案已撤回，未交付这八个公共兼容定义。** 用户已明确批准八个生成名退出稳定公共契约；最新实现和验收状态见 [迁移报告](module-completion.md)。以下保留实际旧声明的完整类型/正文作为证据。

# 拟补回的八个精确兼容声明

起点为 382d29d94aaa8e32bcdeb24633f070d29695dcc3，Lean 4.34.1
(5045d0056413266e57c625dcd7c365b10e377c52)，Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612。
以下类型和定义体直接来自该起点真实旧声明的 Lean 打印，保留完整限定名、宇宙参数、隐式参数及实例参数；无省略号。打印中的 notation 为 Lean 本身的 notation。

拟实施策略：八项都显式补回为相同完整限定名的公共 `def`，位于原 producer，保留 `[instance_reducible]`、完整定义体、matcher 元数据及编译代码。七项取当前同名私有 matcher 的类型和值，重新以内核检查过的公共定义发布；LocalCover 的旧 match_3 则取同型新 match_6 的定义体。不会把旧名仅改成字符串别名，也不公开 quotientLinear。公共定义独立于私有 helper 名，原生产函数/证明仍使用编译器生成的私有 helper。

一个固定版本小型控制已验证“私有实际 helper 与同名公共兼容定义并存”可行，现代与 legacy 调用及 rfl 通过。以下八个真实 producer 的实现与逐项旧类型/计算验证仍待运行，不能将清单当作已验收。

新 `OAI.KLInvariance.LocalCover.splitEquiv.match_6` 是编译器生成的附带公共声明，不是手写兼容项；它与旧 match_3 的类型指纹、universes、kind 和 producer 相同。拟保留它并逐项审计新增记录，不豁免任意新增。其余新附带声明若出现，将另行列明。

## 1. `OAI.KLInvariance.CoefficientChange.ext.match_1`

CoefficientChange 包装值的单分支消去：把包装元素交给 val 分支。

拟议类型与定义体：

```lean
@[instance_reducible] def OAI.KLInvariance.CoefficientChange.ext.match_1.{u_1, u_2, u_3, u_4} : ∀ {k : Type u_1}
  {inst : Field.{u_1} k} {A : Type u_2} {inst_1 : CommRing.{u_2} A} {inst_2 : Algebra.{u_1, u_2} k A} {B : Type u_3}
  {inst_3 : CommRing.{u_3} B} {inst_4 : Algebra.{u_1, u_3} k B} {_e : AlgEquiv.{u_1, u_2, u_3} k A B} {M : Type u_4}
  (motive : OAI.KLInvariance.CoefficientChange.{u_1, u_2, u_3, u_4} _e M → Prop)
  (h : OAI.KLInvariance.CoefficientChange.{u_1, u_2, u_3, u_4} _e M),
  (∀ (val : M), motive (OAI.KLInvariance.CoefficientChange.mk.{u_1, u_2, u_3, u_4} val)) → motive h :=
fun {k} {inst} {A} {inst_1} {inst_2} {B} {inst_3} {inst_4} {_e} {M} motive h h_1 =>
  OAI.KLInvariance.CoefficientChange.casesOn.{0, u_1, u_2, u_3, u_4} h fun val => h_1 val
```

## 2. `OAI.KLInvariance.LocalCover.splitEquiv.match_3`

P × ker g 的二元组消去：将 p、b 原样交给唯一分支。

拟议类型与定义体：

```lean
@[instance_reducible] def OAI.KLInvariance.LocalCover.splitEquiv.match_3.{u_1, u_2, u_3} : ∀ {R : Type u_3}
  {B : Type u_2} {P : Type u_1} [inst : CommRing.{u_3} R] [inst_1 : AddCommGroup.{u_2} B]
  [inst_2 : Module.{u_3, u_2} R B] [inst_3 : AddCommGroup.{u_1} P] [inst_4 : Module.{u_3, u_1} R P]
  (g : LinearMap.{u_3, u_3, u_2, u_1} (RingHom.id.{u_3} R) B P)
  (motive : Prod.{u_1, u_2} P ↥(LinearMap.ker.{u_3, u_3, u_2, u_1} g) → Prop)
  (x : Prod.{u_1, u_2} P ↥(LinearMap.ker.{u_3, u_3, u_2, u_1} g)),
  (∀ (p : P) (b : ↥(LinearMap.ker.{u_3, u_3, u_2, u_1} g)), motive (Prod.mk.{u_1, u_2} p b)) → motive x :=
fun {R} {B} {P} [CommRing.{u_3} R] [AddCommGroup.{u_2} B] [Module.{u_3, u_2} R B] [AddCommGroup.{u_1} P]
    [Module.{u_3, u_1} R P] g motive x h_1 =>
  Prod.casesOn.{0, u_1, u_2} x fun fst snd => h_1 fst snd
```

## 3. `OAI.KLInvariance.MomentGraph.GradedSheaf.extendBottom_upperQuotient.match_1_1`

存在证明消去：将 α d • w = v 的见证 w 与等式证明交给分支。

拟议类型与定义体：

```lean
@[instance_reducible] def OAI.KLInvariance.MomentGraph.GradedSheaf.extendBottom_upperQuotient.match_1_1.{u_1, u_2, u_3} : ∀
  {k : Type u_3} [inst : Field.{u_3} k] {A : Type u_1} [inst_1 : CommRing.{u_1} A] [inst_2 : Algebra.{u_3, u_1} k A]
  {𝓐 : ℤ → Submodule.{u_3, u_1} k A} {V E : Type u_2} [inst_3 : PartialOrder.{u_2} V]
  {G : OAI.KLInvariance.MomentGraph.OrderedGraph.{u_2, u_2} V E} {D : Type u_2} [inst_4 : Fintype.{u_2} V]
  [inst_5 : Fintype.{u_2} D] [inst_6 : IsNoetherianRing.{u_1} A]
  (B : OAI.KLInvariance.MomentGraph.GradedSheaf.{u_3, u_1, u_2} G) (τ : D → V) (α : D → A)
  (hα : ∀ (d : D), Membership.mem.{u_1, u_1} (𝓐 1) (α d))
  (C :
    OAI.KLInvariance.Graded.ModuleData.MinimalCover.{u_3, u_1, u_2}
      (OAI.KLInvariance.MomentGraph.GradedSheaf.attachImage.{u_3, u_1, u_2} B τ α hα))
  (d : D)
  (v :
    ↑(OAI.KLInvariance.Graded.ModuleData.obj.{u_3, u_1, u_2}
        (OAI.KLInvariance.MomentGraph.GradedSheaf.vertex.{u_3, u_1, u_2}
          (OAI.KLInvariance.MomentGraph.GradedSheaf.extendBottom.{u_3, u_1, u_2} B τ α hα C)
          (OAI.KLInvariance.MomentGraph.OrderedGraph.target.{u_2, u_2}
            (OAI.KLInvariance.MomentGraph.bottomGraph.{u_2} G τ) (Sum.inr.{u_2, u_2} d)))))
  (motive : (∃ w, Eq.{max (u_1 + 1) (u_2 + 1)} (HSMul.hSMul.{u_1, max u_1 u_2, max u_1 u_2} (α d) w) v) → Prop)
  (x : ∃ w, Eq.{max (u_1 + 1) (u_2 + 1)} (HSMul.hSMul.{u_1, max u_1 u_2, max u_1 u_2} (α d) w) v),
  (∀
      (w :
        ↑(OAI.KLInvariance.Graded.ModuleData.obj.{u_3, u_1, u_2}
            (OAI.KLInvariance.MomentGraph.GradedSheaf.vertex.{u_3, u_1, u_2}
              (OAI.KLInvariance.MomentGraph.GradedSheaf.extendBottom.{u_3, u_1, u_2} B τ α hα C)
              (OAI.KLInvariance.MomentGraph.OrderedGraph.target.{u_2, u_2}
                (OAI.KLInvariance.MomentGraph.bottomGraph.{u_2} G τ) (Sum.inr.{u_2, u_2} d)))))
      (hw : Eq.{max (u_1 + 1) (u_2 + 1)} (HSMul.hSMul.{u_1, max u_1 u_2, max u_1 u_2} (α d) w) v),
      motive (Exists.intro.{max (u_1 + 1) (u_2 + 1)} w hw)) →
    motive x :=
fun {k} [Field.{u_3} k] {A} [CommRing.{u_1} A] [Algebra.{u_3, u_1} k A] {𝓐} {V E} [PartialOrder.{u_2} V] {G} {D}
    [Fintype.{u_2} V] [Fintype.{u_2} D] [IsNoetherianRing.{u_1} A] B τ α hα C d v motive x h_1 =>
  Exists.casesOn.{max (u_1 + 1) (u_2 + 1)} x fun w h => h_1 w h
```

## 4. `OAI.KLInvariance.MomentGraph.GradedSheaf.extendBottom_upperQuotient.match_1_3`

存在证明消去：将 v = α d • w 的见证 w 与等式证明交给分支。

拟议类型与定义体：

```lean
@[instance_reducible] def OAI.KLInvariance.MomentGraph.GradedSheaf.extendBottom_upperQuotient.match_1_3.{u_1, u_2, u_3} : ∀
  {k : Type u_3} [inst : Field.{u_3} k] {A : Type u_1} [inst_1 : CommRing.{u_1} A] [inst_2 : Algebra.{u_3, u_1} k A]
  {𝓐 : ℤ → Submodule.{u_3, u_1} k A} {V E : Type u_2} [inst_3 : PartialOrder.{u_2} V]
  {G : OAI.KLInvariance.MomentGraph.OrderedGraph.{u_2, u_2} V E} {D : Type u_2} [inst_4 : Fintype.{u_2} V]
  [inst_5 : Fintype.{u_2} D] [inst_6 : IsNoetherianRing.{u_1} A]
  (B : OAI.KLInvariance.MomentGraph.GradedSheaf.{u_3, u_1, u_2} G) (τ : D → V) (α : D → A)
  (hα : ∀ (d : D), Membership.mem.{u_1, u_1} (𝓐 1) (α d))
  (C :
    OAI.KLInvariance.Graded.ModuleData.MinimalCover.{u_3, u_1, u_2}
      (OAI.KLInvariance.MomentGraph.GradedSheaf.attachImage.{u_3, u_1, u_2} B τ α hα))
  (d : D)
  (v :
    ↑(OAI.KLInvariance.Graded.ModuleData.obj.{u_3, u_1, u_2}
        (OAI.KLInvariance.MomentGraph.GradedSheaf.vertex.{u_3, u_1, u_2}
          (OAI.KLInvariance.MomentGraph.GradedSheaf.extendBottom.{u_3, u_1, u_2} B τ α hα C)
          (OAI.KLInvariance.MomentGraph.OrderedGraph.target.{u_2, u_2}
            (OAI.KLInvariance.MomentGraph.bottomGraph.{u_2} G τ) (Sum.inr.{u_2, u_2} d)))))
  (motive : (∃ w, Eq.{max (u_1 + 1) (u_2 + 1)} v (HSMul.hSMul.{u_1, max u_1 u_2, max u_1 u_2} (α d) w)) → Prop)
  (x : ∃ w, Eq.{max (u_1 + 1) (u_2 + 1)} v (HSMul.hSMul.{u_1, max u_1 u_2, max u_1 u_2} (α d) w)),
  (∀
      (w :
        ↑(OAI.KLInvariance.Graded.ModuleData.obj.{u_3, u_1, u_2}
            (OAI.KLInvariance.MomentGraph.GradedSheaf.vertex.{u_3, u_1, u_2}
              (OAI.KLInvariance.MomentGraph.GradedSheaf.extendBottom.{u_3, u_1, u_2} B τ α hα C)
              (OAI.KLInvariance.MomentGraph.OrderedGraph.target.{u_2, u_2}
                (OAI.KLInvariance.MomentGraph.bottomGraph.{u_2} G τ) (Sum.inr.{u_2, u_2} d)))))
      (hw : Eq.{max (u_1 + 1) (u_2 + 1)} v (HSMul.hSMul.{u_1, max u_1 u_2, max u_1 u_2} (α d) w)),
      motive (Exists.intro.{max (u_1 + 1) (u_2 + 1)} w hw)) →
    motive x :=
fun {k} [Field.{u_3} k] {A} [CommRing.{u_1} A] [Algebra.{u_3, u_1} k A] {𝓐} {V E} [PartialOrder.{u_2} V] {G} {D}
    [Fintype.{u_2} V] [Fintype.{u_2} D] [IsNoetherianRing.{u_1} A] B τ α hα C d v motive x h_1 =>
  Exists.casesOn.{max (u_1 + 1) (u_2 + 1)} x fun w h => h_1 w h
```

## 5. `OAI.KLInvariance.ReflectionFrobenius.wallCoordinate_injective.match_1_2`

Fin 2 × ι 的二元组消去：将 ε、j 原样交给分支。

拟议类型与定义体：

```lean
@[instance_reducible] def OAI.KLInvariance.ReflectionFrobenius.wallCoordinate_injective.match_1_2.{u_1} : ∀
  {ι : Type u_1} (motive : Prod.{0, u_1} (Fin 2) ι → Prop) (h : Prod.{0, u_1} (Fin 2) ι),
  (∀ (ε : Fin 2) (j : ι), motive (Prod.mk.{0, u_1} ε j)) → motive h :=
fun {ι} motive h h_1 => Prod.casesOn.{0, 0, u_1} h fun fst snd => h_1 fst snd
```

## 6. `OAI.KLInvariance.ReflectionFrobenius.wallMatrix_mulVec.match_1_1`

Fin 2 × ι 的二元组消去：将 r、j 原样交给分支。

拟议类型与定义体：

```lean
@[instance_reducible] def OAI.KLInvariance.ReflectionFrobenius.wallMatrix_mulVec.match_1_1.{u_1} : ∀ {ι : Type u_1}
  (motive : Prod.{0, u_1} (Fin 2) ι → Prop) (h : Prod.{0, u_1} (Fin 2) ι),
  (∀ (r : Fin 2) (j : ι), motive (Prod.mk.{0, u_1} r j)) → motive h :=
fun {ι} motive h h_1 => Prod.casesOn.{0, 0, u_1} h fun fst snd => h_1 fst snd
```

## 7. `OAI.KLInvariance.ReflectionPairTranslation.Twist.ext.match_1`

Twist 包装值的单分支消去：把包装元素交给 val 分支。

拟议类型与定义体：

```lean
@[instance_reducible] def OAI.KLInvariance.ReflectionPairTranslation.Twist.ext.match_1.{u_1, u_2} : ∀ {R : Type u_1}
  {inst : CommRing.{u_1} R} {_τ : RingEquiv.{u_1, u_1} R R} {Y : Type u_2}
  (motive : OAI.KLInvariance.ReflectionPairTranslation.Twist.{u_1, u_2} _τ Y → Prop)
  (h : OAI.KLInvariance.ReflectionPairTranslation.Twist.{u_1, u_2} _τ Y),
  (∀ (val : Y), motive (OAI.KLInvariance.ReflectionPairTranslation.Twist.mk.{u_1, u_2} val)) → motive h :=
fun {R} {inst} {_τ} {Y} motive h h_1 =>
  OAI.KLInvariance.ReflectionPairTranslation.Twist.casesOn.{0, u_1, u_2} h fun val => h_1 val
```

## 8. `OAI.KLInvariance.TitsSpace.exists_common_transverse.match_1_1`

对 (E × E) ⊕ (Bool × E × E × E) 分支消去；保留任意 Sort 的 motive，分别调用两参数或四参数分支，具有实际数据归约行为。

拟议类型与定义体：

```lean
@[instance_reducible] def OAI.KLInvariance.TitsSpace.exists_common_transverse.match_1_1.{u_1, u_2} : (E : Type u_2) →
  let A := Sum.{u_2, u_2} (Prod.{u_2, u_2} E E) (Prod.{0, u_2} Bool (Prod.{u_2, u_2} E (Prod.{u_2, u_2} E E)));
  (motive : A → Sort u_1) →
    (x : A) →
      ((a b : E) → motive (Sum.inl.{u_2, u_2} (Prod.mk.{u_2, u_2} a b))) →
        ((i : Bool) →
            (a b c : E) →
              motive (Sum.inr.{u_2, u_2} (Prod.mk.{0, u_2} i (Prod.mk.{u_2, u_2} a (Prod.mk.{u_2, u_2} b c))))) →
          motive x :=
fun E =>
  let A := Sum.{u_2, u_2} (Prod.{u_2, u_2} E E) (Prod.{0, u_2} Bool (Prod.{u_2, u_2} E (Prod.{u_2, u_2} E E)));
  fun motive x h_1 h_2 =>
  Sum.casesOn.{u_1, u_2, u_2} x (fun val => Prod.casesOn.{u_1, u_2, u_2} val fun fst snd => h_1 fst snd) fun val =>
    Prod.casesOn.{u_1, 0, u_2} val fun fst snd =>
      Prod.casesOn.{u_1, u_2, u_2} snd fun fst_1 snd =>
        Prod.casesOn.{u_1, u_2, u_2} snd fun fst_2 snd => h_2 fst fst_1 fst_2 snd
```

## 验证与展开约定

- 对八项检查准确名字、旧参数（包括可命名参数）、旧类型的实际使用、原声明的 matcher/reducibility 元数据。
- 公共导出保留 `defnInfo` 和完整值；原 matcher 注册信息复制到兼容名字，使相关 matcher 识别及 split/simp 机制继续可用。
- 三个真正的结构消去族与两个 Exists 消去族保留 casesOn 的分支参数；第八项对任意 Sort，必须另测左右分支及嵌套 tuple 的实际 rfl/计算，不能仅依赖 proof irrelevance。
- 检查实际旧值与新值、内核/三公理、普通现代消费者；完整记录保留原始差异，额外 match_6 单独登记。未批准任何 owner 任意迁移或旧名删除。
