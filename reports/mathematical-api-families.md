# 数学 API 操作族实验（第三轮）

状态：分阶段进行；本页不代表最终全库验收。
基点 bdbca7ff639bc32f94a85647c88cb16d9e80b294，分支
`experiment/mathematical-api-families-20261024`。保留前两轮完整结果，main不变，不建PR、不合并。

## 轻量盘点与边界

- 同构输运：Iso.assignments/sections/boundary已有兼容性和自然性定理，但Structure的
  flabby/generated直接change成vertex公式。补点值接口并复用原自然性；不隐藏计算。
- 局部upward kernel：Pullback与Models直接把成员假设当函数应用，依赖carrier写法。
  补语义成员/普通stalk核对应，重用现有像与输运定理。
- product/pi：已有pi_compatible、prod/pi kernel判据和Models的像分量判据。
  优先复用这些数学接口，补必要分量自然性与prod兼容性，减少重复逐边cast分析。
- restriction：extend_compatible当前逐边重建子图边并处理cast；计划补restriction与
  extendAssignment的retraction及局部兼容性等价，表达其数学原因。

范围是四组相连的操作模式，不按新增定理数量、expose数量或行数下降衡量。
不预造范畴框架，不添加无消费者引理。先补接口与真实消费者，再扩大下一组。

## 阶段一

新增Iso.assignments_apply、assignments_symm_apply、sections_val_apply、boundary_apply。
向原vertex/edge值归一化，使用simp，没有反向折叠或新ext/instance。
实际改造Iso.compatible_iff、stalkMap/boundaryMap自然性、upwardKernel输运的一个实现依赖步骤，
以及Structure中Iso.flabby/generated。其余既有API仍复用。
`lake build ...Sheaf.Structure`成功；完整门禁尚未执行。

## 实现压力试验计划

至少两种表示选择：同构输运改为从逆向线性双射构造；upwardKernel改为相关线性核的交。
保持数学类型/标量约定和expose，试验变体不进入生产实现。
冻结整个改造后客户端，逐步记录只改实现、重证API、旧客户端对照、恢复及字节身份。
对于旧新都通过的对照不声称维护收益；未受扰动覆盖的API另行标明。

时间、规模、失败和最终证据待各阶段完成后补齐。token无遥测，不估造。
