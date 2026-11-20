# Giallar 验证缺口：自然语言模型、数学证明与形式化基础

日期：2026-11-20。对象：Giallar（PLDI 2022）所暴露的验证任务，以及前次讨论提出的扩展方向。

这份文档完成两项工作：给出六类任务的明确数学模型、规格和证明；为这些模型定位可复用的形式化定义与定理。数学证明针对本文写明的模型和算法。连接到某个版本的原 Qiskit Python／Rust 实现，还需要实现对应证明。本轮没有编写或运行新的 Lean／Rocq 证明。

**结论先行。** 路由与相位优化在 SQIR／VOQC 中已有很接近的已证明对象；Lean 的 mathlib 与 Physlib 已提供近似误差论证所需的大量线性代数、范数和量子状态基础。脉冲调度需要补齐离散日程与连续演化的联系。外部求解器可以通过结果证书接入，规格是否要求最优性会直接改变证书内容。

|编号|验证任务|本轮具体证明的内容|
|---|---|---|
|A|近似综合与误差控制|逐段误差组合；含参考系统的输出误差；删除小受控相位门的完整电路族误差界|
|B|跨表示的全局优化|CNOT＋相位门的相位表示提取、系数合并与重新综合正确性|
|C|随机／启发式路由|任意合法选择的语义保持；硬件邻接约束；有界尝试加路径回退的终止性；重复尝试的概率界|
|D|外部求解器|具体路由与调度证书的可靠性；线性下界证书及整数分支证书的最优性保证|
|E|脉冲层调度|偏序调度语义；固定资源顺序下的最早日程；矩形脉冲模型的门级对应；Hamiltonian 扰动界|
|F|模板之外的循环与递归|保持语义的任务展开算法；可显式计算的终止度量与执行步数上界|

论文中 12 个未覆盖 pass 的归因是脉冲层、随机路由、外部求解器和近似综合；非局部表示与新循环模式另见 limitations。对应位置为 [G] §8。本表把这些研究缺口细化为可审查的命题；它并不声称逐一复现了那 12 个实现。

**随机性本身不是必须转交证明助手的理由。** 论文 §7 已把修复后 LookaheadSwap 的随机数视为任意符号数，以验证语义保持。本文 C1 沿用同一原则。尚需补足的是具体搜索算法的建模、进展／终止，以及需要概率规格时的成功概率或期望时间。类似地，D 允许通过已验证检查器接纳外部搜索结果；并不要求形式化求解器内部全部算法。

## 0. 共同语义与基础引理

### 0.1 对象、方向与相位约定

固定有限个 qubit，令 \(X_n=\{0,1\}^n\)，Hilbert 空间为 \(\mathcal H_n=\mathbb C^{X_n}\)，计算基记为 \(|x\rangle\)。电路是按执行顺序排列的有限门序列 \(C=(g_1,\ldots,g_m)\)。每个门已经包含所作用的有序 qubit 列表，解释为整个空间上的酉算子 \(U_{g_i}\)，未作用的线取恒等。电路均要求良构：线索引在范围内，同一个多 qubit 门的各条线互不相同；特别是 CNOT 的控制线与目标线不同。

统一约定：

\[
\llbracket C\rrbracket=U_{g_m}\cdots U_{g_1},\qquad
\llbracket C;D\rrbracket=\llbracket D\rrbracket\llbracket C\rrbracket.
\]

下文以精确相等为默认规格。只有在 A 中显式使用相位距离时，才将整个电路的全局相位忽略。受控子程序不能直接套用这种商空间规格：例如 \(I\) 与 \(-I\) 仅差全局相位，但对它们加控制后，差异成为控制线上的相对相位。

混态为 \(\rho\succeq0\)、\(\operatorname{tr}\rho=1\) 的矩阵，酉演化为 \(\mathcal U(\rho)=U\rho U^\dagger\)。算子范数为 \(\|A\|=\sup_{\|v\|_2=1}\|Av\|_2\)，迹范数为 \(\|A\|_1=\operatorname{tr}\sqrt{A^\dagger A}\)。两者不能与矩阵逐元素的最大值范数混用。

### 0.2 后文所用的范数事实及证明

**引理 L1（乘法与酉不变性）。** \(\|AB\|\leq\|A\|\|B\|\)，且对酉矩阵 \(U,V\)，\(\|UAV\|=\|A\|\)。

**证明。** 对单位向量 \(x\)，\(\|ABx\|\leq\|A\|\|Bx\|\leq\|A\|\|B\|\)。取上确界得第一式。左乘酉矩阵不改变向量范数；右乘酉矩阵把单位球双射到自身，所以第二式成立。特别地，非零空间上酉矩阵的算子范数为 1。□

**引理 L2（参考系统）。** 对任意有限维非零空间 \(R\)，\(\|A\otimes I_R\|=\|A\|\)。

**证明。** 取 \(R\) 的标准正交基，将向量写成 \(w=\sum_jv_j\otimes e_j\)。则
\[
\|(A\otimes I)w\|^2=\sum_j\|Av_j\|^2
\leq\|A\|^2\sum_j\|v_j\|^2=\|A\|^2\|w\|^2.
\]
反方向，对任意单位向量 \(v\) 和固定单位向量 \(e\)，输入 \(v\otimes e\) 给出 \(\|Av\|\)；再取上确界。□

**引理 L3（迹范数三角不等式与夹乘界）。**
\[
\|X+Y\|_1\leq\|X\|_1+\|Y\|_1,\qquad
\|AXB\|_1\leq\|A\|\|X\|_1\|B\|.
\]

**证明。** 由有限维奇异值分解 \(X=\sum_i s_i u_iv_i^\dagger\)，\(s_i\geq0\)，得到
\[
\|X\|_1=\sup_{\|Z\|\leq1}|\operatorname{tr}(Z^\dagger X)|.
\]
确实，任一这样的 \(Z\) 都使右侧不超过 \(\sum_i s_i\)，因为每项 \(|v_i^\dagger Z^\dagger u_i|\leq1\)；将两个正交基的对应关系扩展成酉矩阵，取 \(Z v_i=u_i\)，即达到该值。对 \(X+Y\) 使用这个等式和复数三角不等式，得到第一式。

秩一矩阵 \(ab^\dagger\) 唯一可能非零的奇异值为 \(\|a\|\|b\|\)，因为其平方 \((ab^\dagger)^\dagger ab^\dagger=\|a\|^2bb^\dagger\)。故
\[
\|AXB\|_1\leq\sum_i s_i\|Au_i\|\|B^\dagger v_i\|
\leq\|A\|\|B\|\sum_i s_i.
\]
这里 \(\|B^\dagger\|=\|B\|\) 同样由奇异值分解得到。□

**引理 L4（测量事件）。** 若 \(D=D^\dagger\)、\(\operatorname{tr}D=0\)、\(0\preceq E\preceq I\)，则
\[
|\operatorname{tr}(ED)|\leq\tfrac12\|D\|_1.
\]

**证明。** 按正负特征值分解 \(D=D_+-D_-\)。两部分皆半正定，且 \(\operatorname{tr}D_+=\operatorname{tr}D_-=t=\|D\|_1/2\)。对任一半正定 \(P\)，在其特征基中展开可得 \(0\leq\operatorname{tr}(EP)\leq\operatorname{tr}P\)。于是 \(\operatorname{tr}(ED)\) 是两个 \([0,t]\) 中的实数之差。□

这些证明使用的背景是有限维谱定理／奇异值分解和有限求和；后文新增结论不再把误差组合等关键步骤藏在未证明的假设里。

## A. 近似综合：从局部近似到整个程序的可观测误差

### A.1 自然语言模型

编译器把源电路分成若干块，每块原本实现酉算子 \(U_i\)，替换后实现 \(V_i\)。局部综合器须给出可核查的误差证据。全局验证器的责任是保证替换位置、qubit 嵌入和执行顺序正确，并将局部误差累加为整个电路的保证。

先使用保留相位的局部规格 \(\|U_i-V_i\|\leq\varepsilon_i\)。若应用只关心整体量子信道，可以给出单位复数 \(z_i\) 及 \(\|U_i-z_iV_i\|\leq\varepsilon_i\)。保留这些相位证据，便能明确控制其使用位置。

### A.2 定理 A1：组合误差

设 \(U_i,V_i\) 均酉，\(\varepsilon_i\geq0\)，\(\|U_i-V_i\|\leq\varepsilon_i\)。则
\[
\left\|U_m\cdots U_1-V_m\cdots V_1\right\|
\leq\sum_{i=1}^m\varepsilon_i.
\tag{A1}
\]

**证明。** 定义 \(T_j=U_m\cdots U_{j+1}V_j\cdots V_1\)，其中 \(T_0=U_m\cdots U_1\)，\(T_m=V_m\cdots V_1\)。逐项相减后望远镜求和给出
\[
T_0-T_m=\sum_{j=1}^m
U_m\cdots U_{j+1}(U_j-V_j)V_{j-1}\cdots V_1.
\]
每个求和项的左右因子都是酉矩阵，依 L1 其范数恰为 \(\|U_j-V_j\|\)。用三角不等式即得结论。空序列两边为零。□

定义相位距离
\[
\delta(U,V)=\min_{|z|=1}\|U-zV\|.
\]
最小值存在：单位圆紧，范数表达式关于 \(z\) 连续。对每块选择达到最小值的 \(z_i\)，对 \(U_i,z_iV_i\) 应用 A1，再取整体相位 \(z=\prod_i z_i\)，得到
\[
\delta(U_m\cdots U_1,V_m\cdots V_1)
\leq\sum_i\delta(U_i,V_i).
\tag{A1φ}
\]
这一步没有假设原电路各块彼此可交换。

### A.3 定理 A2：纠缠输入和测量结果也受控

设 \(\delta(U,V)\leq\eta\)。对任意有限维参考系统 \(R\)、任意联合混态 \(\rho\) 和任意测量事件 \(0\preceq E\preceq I\)，有
\[
\tfrac12\| (U\otimes I)\rho(U^\dagger\otimes I)
 -(V\otimes I)\rho(V^\dagger\otimes I)\|_1\leq\eta,
\tag{A2a}
\]
以及该事件在两个输出上的概率之差不超过 \(\min(1,\eta)\)。

**证明。** 取 \(|z|=1\) 使 \(\|U-zV\|\leq\eta\)。整体相位不改变共轭信道，因此可将 \(V\) 换成 \(zV\)。将 \(U,V\) 都扩张为带 \(I_R\) 的算子后，差为
\[
(U-V)\rho U^\dagger+V\rho(U^\dagger-V^\dagger).
\]
由 L2、L3、\(\|\rho\|_1=\operatorname{tr}\rho=1\)，两项迹范数各不超过 \(\eta\)，即得 A2a。输出差是迹零 Hermitian 矩阵，用 L4 得到概率界；概率本身均在 \([0,1]\)，所以也受 1 约束。□

若采用未除以 2 的 diamond norm 定义
\[
\|\Phi\|_\diamond=\sup_{r\geq1}\sup_{X\ne0}
\frac{\|(\Phi\otimes\mathrm{id}_r)(X)\|_1}{\|X\|_1},
\]
同一个展开对任意复矩阵 \(X\) 成立，给出
\[
\|\mathcal U-\mathcal V\|_\diamond\leq2\delta(U,V).
\tag{A2b}
\]
因此此处不需要先证明一般 CPTP 信道的 diamond norm 理论，便能建立酉综合所需的稳定误差界。

### A.4 定理 A3：一个完整、可执行描述的近似算法

取 \(P(\theta)=\operatorname{diag}(1,e^{i\theta})\)。一个受控 \(P(\theta)\) 门在计算基中对满足控制条件且目标为 1 的基向量乘 \(e^{i\theta}\)，其他基向量不变。用恒等门替换它，误差是
\[
\|CP(\theta)-I\|=|e^{i\theta}-1|=2|\sin(\theta/2)|\leq|\theta|.
\tag{A3a}
\]

**证明。** 对角矩阵的算子范数等于最大对角元绝对值：上界由向量范数逐坐标求和得到，下界由选取对应基向量达到。最后一个不等式由 \(\sin t=\int_0^t\cos s\,ds\) 与 \(|\cos s|\leq1\) 得到。□

考虑一个明确的 QFT 型电路族。qubit 编号为 \(1,\ldots,n\)；依次对 \(j=1,\ldots,n\)，先在 \(j\) 上执行 Hadamard，再按 \(k=j+1,\ldots,n\) 执行控制线为 \(k\)、目标线为 \(j\)、角度为 \(\pi/2^{k-j}\) 的受控相位门；末尾交换第 \(j\) 与第 \(n+1-j\) 条线，其中 \(1\leq j\leq\lfloor n/2\rfloor\)。因此对每个 \(r=1,\ldots,n-1\)，恰有 \(n-r\) 个角度为 \(\pi/2^r\) 的受控相位门。近似算法保持其余门与顺序不变，删除所有 \(r\geq b\) 的受控相位门，其中 \(b\geq1\)。记原电路为 \(Q_n\)，删除结果为 \(\widetilde Q_{n,b}\)。则
\[
\|\llbracket Q_n\rrbracket-\llbracket\widetilde Q_{n,b}\rrbracket\|
\leq\pi\sum_{r=b}^{n-1}\frac{n-r}{2^r}
\leq\frac{2\pi n}{2^b}.
\tag{A3b}
\]

**证明。** 将源电路每个门看作一块；保留门误差为零，删除门用 A3a 及 L2 得到对应角度的误差。应用 A1 并按 \(r\) 计数，得第一不等式。再用 \(n-r\leq n\) 和几何级数 \(\sum_{r=b}^{\infty}2^{-r}=2^{1-b}\)。若 \(b\geq n\)，实际和为空且误差为零。□

这证明的是删除算法相对于给定源电路的误差；源电路实现离散 Fourier 变换的算法正确性是另一项命题，无需作为此误差证明的前提。选择 \(b\) 使 \(2\pi n/2^b\leq\epsilon\)，即可通过 A2 获得任意纠缠输入与末端测量的 \(\epsilon\) 保证。

**与原实现的连接责任。** 对原 `UnitarySynthesis`，还需验证实际输出的局部误差证据及参数数值表示。本文没有假定任意综合器会自动满足 A1 前提；A3 提供的是一个前提已经实际推导完成的近似算法。

## B. 相位多项式：提取、优化和重新综合

### B.1 自然语言模型

本节处理由 CNOT 和 \(P(\theta)\) 构成的片段。CNOT 改变计算基 bit string，且这种改变是 \(\mathbb F_2\) 上的可逆线性变换；相位门只向某个当前 bit 为 1 的基向量增加相位。于是整个片段可以用“一项线性变换＋一项依赖输入 bit string 的相位函数”表示。

令 \(a\in\mathbb F_2^n\)，\(\ell_a(x)=\sum_j a_jx_j\in\mathbb F_2\)。在实数表达式中，把 \(\ell_a(x)\) 解释为 0 或 1。一个相位表示是
\[
(A,\alpha),\qquad A\in GL(n,\mathbb F_2),\quad
\alpha:\mathbb F_2^n\setminus\{0\}\to\mathbb R,
\]
其中只有有限个系数非零，其语义是
\[
U_{A,\alpha}|x\rangle
=e^{if_\alpha(x)}|Ax\rangle,\qquad
f_\alpha(x)=\sum_{a\ne0}\alpha(a)\ell_a(x).
\tag{B0}
\]
这确实是酉算子：\(A\) 置换计算基，每个系数的模长为 1，因此基向量像仍构成正交基。

### B.2 定理 B1：提取算法正确

从 \(A=I,\alpha=0\) 出发，按执行顺序处理每个门：

1. 遇到 \(\mathrm{CNOT}(c,t)\)，将 \(A\) 的第 \(t\) 行加上第 \(c\) 行，保持 \(\alpha\) 不变。
2. 遇到 \(P(\theta)\) 作用于 \(j\)，令 \(a\) 为当前 \(A\) 的第 \(j\) 行，将 \(\alpha(a)\) 增加 \(\theta\)，保持 \(A\) 不变。

所得表示的算子恰为源片段的算子。

**证明。** 对已处理门数归纳。不含门时 B0 为恒等。设处理前每个 \(|x\rangle\) 已变成 \(e^{if_\alpha(x)}|Ax\rangle\)。CNOT 将输出的第 \(t\) 个 bit 加上第 \(c\) 个 bit，正是第 1 条行变换；相位不受影响。相位门额外乘 \(e^{i\theta(Ax)_j}=e^{i\theta\ell_a(x)}\)，正是第 2 条更新。每个行加法是其自身的逆，因此 \(A\) 始终可逆，行 \(a\) 不会为零。归纳得到所有基向量上的等式，线性性将等式扩展到任意向量。算法每步消费一个门，所以终止。□

### B.3 定理 B2：合并与模周期优化正确

若输出线性变换不变，并且对每个 \(a\ne0\)，新系数满足
\[
\beta(a)=\alpha(a)+2\pi k_a,\qquad k_a\in\mathbb Z,
\]
则 \(U_{A,\alpha}=U_{A,\beta}\)。因此，合并所有相同 parity 的项，再删除系数为 \(2\pi\) 整数倍的项，保持语义。

**证明。** 对每个 \(x\)，相位差为
\[
f_\beta(x)-f_\alpha(x)=2\pi\sum_a k_a\ell_a(x),
\]
括号内是整数，因此两相位的复指数相同。两算子又将 \(|x\rangle\) 映到同一 \(|Ax\rangle\)，故在基上相等。合并相同 parity 只是有限实数求和的结合与交换，完全保留 \(f\)。□

这是一个充分条件；不声称所有等价相位表达式都能通过逐项系数比较识别。若希望一个可判定的实现，可先令 \(\theta\in\pi\mathbb Q\)，用精确有理数运算提供证书；任意实参数则需要符号等式证据。

### B.4 定理 B3：重新综合可实现每个这样的表示

**相位 gadget。** 对非零 \(a\)，选择一个 \(a_p=1\) 的 pivot。对所有其他 \(a_j=1\)，执行 \(\mathrm{CNOT}(j,p)\)，随后在 \(p\) 上执行 \(P(\alpha(a))\)，再逆序撤销前面的 CNOT。

**证明 gadget 语义。** 计算阶段只改变 pivot，使其值成为 \(\bigoplus_{j:a_j=1}x_j=\ell_a(x)\)。中间相位门因此贡献 \(e^{i\alpha(a)\ell_a(x)}\)。撤销阶段把所有 bit 恢复为 \(x\)。故 gadget 恰实现这一项的对角相位。串联所有 gadget，即实现 \(e^{if_\alpha(x)}|x\rangle\)。每个 gadget 最多使用 \(2(n-1)\) 个 CNOT。□

**线性部分。** 用 \(\mathbb F_2\) 上的 Gaussian elimination 将 \(A\) 化为 \(I\)：第 \(k\) 轮在尚未处理的行中选择第 \(k\) 列为 1 的行，交换到 pivot，再把该列其他行的 1 消去。这样的 pivot 必定存在；否则，前 \(k-1\) 列已是单位列时，第 \(k\) 列只位于前 \(k-1\) 个坐标的张成空间，导致列线性相关，与可逆性矛盾。未处理行在前面已处理的列均为零，因此新行操作不会破坏先前结果。经过 \(n\) 轮得到 \(I\)。

行加法由一个 CNOT 实现。两行交换可由三次行加法实现：\((x,y)\mapsto(x,x+y)\mapsto(y,x+y)\mapsto(y,x)\)。这些操作各自可逆。若消元顺序为 \(E_1,\ldots,E_s\)，则 \(E_s\cdots E_1A=I\)，所以按反向顺序执行这些自逆门可实现 \(A\)。

先执行全部相位 gadget，再执行上述线性电路，所得输出为 \(e^{if_\alpha(x)}|Ax\rangle\)，即 B0。结合 B1、B2，得到完整的“提取→合并→重新综合”正确性。□

这里证明的是语义保持。合并减少了相位项数量，但上述朴素 gadget 综合未必减少 CNOT 总数或电路深度；若要求资源改善，可比较综合前后的精确成本，仅在满足成本规格时接受结果。

**语义接口。** 本节使用 \(P(\theta)\)。常见 \(R_z(\theta)=\operatorname{diag}(e^{-i\theta/2},e^{i\theta/2})\) 满足 \(R_z(\theta)=e^{-i\theta/2}P(\theta)\)。从使用后一约定的代码导入时必须记录这项相位。Hadamard、测量和 reset 不属于本节片段；可在这些边界处分段并用电路组合等式连接。

## C. 路由：把随机选择与正确性分开

### C.1 自然语言模型

固定 \(N\geq1\) 个物理位置以及无向连通硬件图 \(G=(V,E)\)，\(|V|=N\)。源电路已分解为单 qubit 与双 qubit 门。假设单 qubit 门任意位置可用，允许的双 qubit 原语及 SWAP 可在每条边上实现，且其门级实现已有精确语义。若原电路只有 \(n\leq N\) 条线，补 \(N-n\) 条闲置线，源算子在它们上面作用为恒等。

布局 \(\pi\) 是全部 \(N\) 条逻辑线到物理位置的双射，包括闲置线。定义置换酉算子 \(P_\pi|x\rangle=|y\rangle\)，其中 \(y_{\pi(j)}=x_j\)。于是
\[
P_\sigma P_\pi=P_{\sigma\circ\pi},\qquad
P_\pi^{-1}=P_{\pi^{-1}}.
\tag{C0}
\]
两式直接由每个 bit 的去向得到，并由线性性推广。由于它置换正交基，\(P_\pi\) 酉。

路由状态是 \((k,\pi,W)\)：已执行前 \(k\) 个逻辑门，当前布局为 \(\pi\)，已发出的物理门序列算子为 \(W\)。令 \(L_k=U_{g_k}\cdots U_{g_1}\)，核心不变量为
\[
W P_{\pi_0}=P_\pi L_k.
\tag{C1}
\]
它精确记录了编译后输入和输出的 qubit 解释。

### C.2 定理 C1：任意合法选择都保持语义

允许两类步骤：

- **SWAP 步骤：** 选硬件边 \((a,b)\)，令 \(\tau\) 交换这两个位置，更新 \(W'=P_\tau W\)、\(\pi'=\tau\circ\pi\)，保持 \(k\)。
- **逻辑门步骤：** 当前下一个门 \(g_{k+1}\) 在布局 \(\pi\) 下可执行，将其映射到物理线，算子为 \(U_{\pi(g)}=P_\pi U_gP_\pi^{-1}\)，更新 \(W'=U_{\pi(g)}W\)、\(k'=k+1\)，布局不变。

任意由这些步骤组成并消费全部源门的有限执行，都输出
\[
W P_{\pi_0}=P_{\pi_f}\llbracket C\rrbracket,
\tag{C2}
\]
且所有发出的双 qubit 操作满足硬件邻接约束。

**证明。** 初始 \(W=I,k=0,\pi=\pi_0\)，C1 成立。SWAP 情形，
\[
W'P_{\pi_0}=P_\tau P_\pi L_k=P_{\tau\circ\pi}L_k.
\]
逻辑门情形，
\[
W'P_{\pi_0}=P_\pi U_gP_\pi^{-1}P_\pi L_k=P_\pi L_{k+1}.
\]
映射门的共轭等式可逐个基向量核对：先撤销布局，在指定逻辑坐标作用局部门，再恢复布局，等于直接在对应物理坐标使用同一局部门。所有步的条件又逐步保证硬件合法。对步数归纳，最终取 \(k=m\) 即得 C2。□

这是路径逐条成立的性质，所以选择边的策略可以是随机的、启发式的或来自未验证的优化器。正确性规格仍须检查该策略给出的每个步骤是否合法。

### C.3 定理 C2：构造一个保证终止的策略包装

取自然数预算 \(B\)。对每个尚未执行的双 qubit 门，最多允许 \(B\) 次启发式 SWAP；每次候选建议的计算也有有限步数预算，超时则直接触发回退。若仍未相邻，取两个当前位置之间的一条简单路径
\(v_0,\ldots,v_r\)，依次交换 \((v_0,v_1),\ldots,(v_{r-2},v_{r-1})\)，随后执行门。简单路径可由有限图搜索找到：连通性保证有 walk，删除重复顶点之间的回路后得到简单路径。

若 \(N\geq2\)，这个策略每个双 qubit 门最多插入 \(B+N-2\) 个 SWAP，且整个编译总会终止。

**证明。** 简单路径不重复顶点，所以 \(r\leq N-1\)。回退的 \(r-1\) 次 SWAP 把第一个目标逻辑 qubit 从 \(v_0\) 移到 \(v_{r-1}\)；第二个目标 qubit 位于 \(v_r\)，不会被这些 SWAP 移动。两者最终相邻。每处理一个源门都只进行有限步并将 \(k\) 增加 1，源门数有限，所以终止。累计 SWAP 上界是 \(m_2(B+N-2)\)，其中 \(m_2\) 是源双 qubit 门数。正确性由 C1 给出。\(N=1\) 的良构电路没有双 qubit 门。□

这是明确设计的包装器，不是对原 `StochasticSwap` 终止行为的断言。它也不保证 SWAP 数最优。

### C.4 定理 C3：若采用随机重试，可另外证明成功时间

假设每次候选搜索尝试及证书核查合计最多耗费 \(q\) 个计算步骤。令 \(K\) 为首次成功的尝试次数；假设存在 \(0<p\leq1\)，使每个满足 \(\Pr(K>r)>0\) 的 \(r\geq0\) 都有 \(\Pr(K=r+1\mid K>r)\geq p\)。这里的成功指找到并通过 C1 或 D 检查的合法完整候选。若更强地对每一种失败历史都有这个下界，也蕴含此假设。则
\[
\Pr(K>r)\leq(1-p)^r,\qquad
\Pr(K<\infty)=1,\qquad \mathbb E[K]\leq1/p.
\]

**证明。** 对 \(r\) 归纳，\(r=0\) 时上界为 1。若 \(\Pr(K>r)=0\)，下一轮尾概率也为零；否则，由条件概率假设，\(\Pr(K>r+1)\leq(1-p)\Pr(K>r)\)。所以几何尾界成立，其极限为零，由概率的上连续性得到无限失败概率为零。对取值于正整数或 \(\infty\) 的 \(K\)，逐点有 \(K=\sum_{r\geq0}\mathbf1_{K>r}\)；由非负级数交换期望，\(\mathbb E[K]=\sum_{r\geq0}\Pr(K>r)\leq1/p\)。计算时间期望因此至多 \(q/p\)。不需要各次尝试独立。□

条件概率下界必须由具体搜索策略另外建立，不能从“使用随机数”推出。

## D. 外部求解器：输出证书及最优性证书

### D.1 路由证书的具体内容

让外部工具返回：初始布局、动作列表、最终布局。动作只能是 `swap(a,b)` 或 `emit(next_source_gate)`。一个有限检查器逐项执行以下检查：布局是双射；SWAP 两端为边；emit 恰好消费下一个源门，门参数和线映射一致，物理门可执行；最后源门已经全部消费，记录的布局等于计算出的布局，实际输出电路等于动作列表产生的门序列。

**定理 D1。** 检查器接受，则输出满足 C2 和硬件约束。

**证明。** 接受保证初始状态满足 C1 的初值，且每项动作恰是 C1 的合法步骤。对动作列表长度归纳使用 C1；末端检查保证 \(k=m\) 且输出对应同一 \(W,\pi_f\)，所以得到 C2。每项邻接检查又保证硬件约束。□

这个检查器处理“插入 SWAP、移动布局”的路由证书；额外的门优化需要附加重写证书。对不含逐步证书的两个电路，VOQC 的 `check_swap_equivalence` 是另一种已经形式化的做法，见复用表。

### D.2 调度证书

输入是有限事件集合、严格偏序、正持续时间、资源集合，以及外部工具给出的开始时间。时间使用整数 tick 或有理数，便于精确比较。检查器验证每个事件恰出现一次、\(s_v\geq0\)、所有先后约束 \(s_u+d_u\leq s_v\)，以及每对共享独占资源的不同事件满足
\[
s_u+d_u\leq s_v\quad\text{或}\quad s_v+d_v\leq s_u.
\tag{D3}
\]

**定理 D2。** 接受则输出是资源可行并满足全部先后关系的日程。

**证明。** 对应性质就是这些有限全称条件；完整遍历事件及成对检查，分别确立每个条件。若只检查依赖图的边，则沿任意依赖路径逐次使用非负持续时间与不等式传递，即得其传递闭包上的先后约束。□

量子语义保持还需 E 中的交换条件和脉冲模型；本定理本身只保证日程可行。

### D.3 定理 D3：线性下界证书

考虑精确有理系数的最小化问题
\[
\min c^Tx\quad\text{满足}\quad Ax\geq b.
\]
变量可以是实数，也可以额外约束为整数／二元；变量上下界均写进 \(Ax\geq b\)。若证书给出 \(\lambda\geq0\)、\(A^T\lambda=c\)，则每个可行解满足 \(c^Tx\geq\lambda^Tb\)。若一个可行候选 \(x_*\) 满足 \(c^Tx_*=\lambda^Tb\)，它就是全局最优解。

**证明。** 将每行约束乘以非负的 \(\lambda_i\) 后相加：
\[
c^Tx=(A^T\lambda)^Tx=\lambda^TAx\geq\lambda^Tb.
\]
候选达到这个对所有可行解成立的下界，因此没有更优解。整数可行集是实数可行集的子集，结论照样成立。□

同理，若 \(\lambda\geq0\)、\(A^T\lambda=0\)、\(\lambda^Tb>0\)，则该约束系统不可行：可行解会推出 \(0=\lambda^TAx\geq\lambda^Tb>0\)，矛盾。

### D.4 定理 D4：整数分支树证书

有些整数最优值不能由根节点的单个线性证书达到。此时允许一棵有限二叉树：内部节点在整数变量 \(x_j\) 上以整数 \(k\) 分支为 \(x_j\leq k\) 和 \(x_j\geq k+1\)；每片叶子附带以下之一：D3 的不可行证书，或该叶子全部解的目标值至少为候选值 \(v_*\) 的线性下界证书。各节点的约束恰为原约束并上根到该节点路径中的分支约束，由检查器自行累积，不能任意增加限制。候选本身须满足原整数约束且目标值为 \(v_*\)。

**证明。** 在叶子处，下界或无解结论由 D3 成立。在内部节点，任一整数解必属于左右子节点之一；由两个子节点的结论，该解目标值至少为 \(v_*\)。对树作结构归纳，根节点所有整数可行解目标值至少为 \(v_*\)；候选达到它，故最优。有限树的核查只需要精确有理运算与有限遍历。□

这是证书**可靠性**，不保证证书总是短，也不保证现有 CPLEX／Z3 调用直接输出该格式。只有确实要求最优性时才需要 D3／D4；若要求的是语义正确与约束可行，D1／D2 已覆盖相应责任。

## E. 调度与脉冲：从偏序到演化

### E.1 自然语言模型

将电路操作看作有限事件集合 \(V\)。严格偏序 \(u\prec v\) 表示必须先完成 \(u\)，再执行 \(v\)。每个事件有持续时间 \(d_v>0\)、资源集合 \(R_v\) 和门算子 \(U_v\)。要求任何在偏序中不可比的事件，其门算子可交换。

硬件资源约束可能比量子 qubit 支持集更严格，例如两个不相交 qubit 仍共享控制电子学通道。必须显式建模 \(R_v\)，不能只从门的支持集猜测资源约束。

### E.2 引理 E1：两个合法线性化之间的变换

有限偏序的任意两个线性扩展，可以通过有限次交换相邻且不可比的元素相互转换。

**证明。** 对事件数归纳。取目标线性扩展的首元素 \(a\)。在当前扩展中，位于 \(a\) 之前的任一元素 \(b\) 与它不可比：若 \(b\prec a\)，目标序列不能以 \(a\) 开头；若 \(a\prec b\)，当前序列不能把 \(b\) 放在 \(a\) 之前。因此可反复将 \(a\) 向左与相邻元素交换，直到首位，每次都是允许的交换。删除两序列共同的首元素，在剩余偏序上使用归纳假设。空集显然。□

**定理 E1（门级调度语义）。** 若不可比事件的算子可交换，则所有线性扩展的电路算子相等。

**证明。** 使用引理 E1；每次相邻交换只将乘积中两个可交换因子的次序对换，其余左右上下文保持不变，所以整体乘积不变。有限次交换后得到结论。□

### E.3 定理 E2：固定资源顺序下的最早日程

假定偏序已经为每对共享资源的不同事件指定先后顺序，且保持无环。按任一拓扑顺序定义
\[
s_v=\max\bigl(\{0\}\cup\{s_u+d_u:u\prec v\}\bigr).
\tag{E2}
\]
则日程满足全部依赖与独占资源约束；并且在所有满足同一偏序的日程 \(t\) 中，逐项有 \(s_v\leq t_v\)，因此其 makespan 最小。

**证明。** 有限无环关系存在极小元素：若没有，沿前驱不断选择将因有限性重复顶点，产生环。反复删除极小元素得到拓扑顺序，所以递推有定义。

由最大值定义，\(s_v\geq0\)，且对 \(u\prec v\)，\(s_v\geq s_u+d_u\)。共享资源者已可比较，所以时间区间不重叠。对于任意可行 \(t\)，沿拓扑顺序归纳：若所有前驱已有 \(s_u\leq t_u\)，则 \(t_v\geq t_u+d_u\geq s_u+d_u\)，又 \(t_v\geq0\)，故 \(t_v\geq s_v\)。最后比较 makespan \(\max(\{0\}\cup\{s_v+d_v:v\in V\})\) 即得结论；空日程的 makespan 为零。□

这里的最优性是相对于**已经选定的资源顺序**。在不同资源顺序之间寻找最优日程，仍是另外的组合优化问题，可用 D 的证书核查结果。

### E.4 指数矩阵所需事实

对有限矩阵定义 \(e^A=\sum_{k\geq0}A^k/k!\)。由 \(\|A^k/k!\|\leq\|A\|^k/k!\)，该级数绝对收敛。在任意有界时间区间，\(e^{tA}\) 及其逐项导数级数被收敛的标量指数级数一致控制，因此
\[
\frac{d}{dt}e^{tA}=Ae^{tA}=e^{tA}A.
\]
若 \(AB=BA\)，用绝对收敛级数的 Cauchy 乘积和二项式公式，得到
\[
e^{A+B}=e^Ae^B.
\tag{Eexp}
\]
共轭转置可逐项作用，故 \((e^A)^\dagger=e^{A^\dagger}\)。对 Hermitian \(H\)，\((e^{-itH})^\dagger e^{-itH}=e^{itH}e^{-itH}=I\)，所以演化酉。

这些论证足以支持以下分段常数模型，无需假定一般非自治微分方程的存在唯一性。

### E.5 定理 E3：矩形脉冲日程实现同一个门电路

为每个事件指定 Hermitian 矩阵 \(H_v\)，它在持续时间内保持常数；令
\[
U_v=e^{-id_vH_v}.
\]
单位约定为 \(\hbar=1\)。取各开始时间非负、满足偏序先后约束的日程 \(s\)。对任意不可比的 \(v,w\)，要求 \([H_v,H_w]=0\)。理想总 Hamiltonian 为
\[
H_s(t)=\sum_{v:\ s_v\leq t<s_v+d_v}H_v.
\tag{E3model}
\]
模型中没有额外漂移、串扰项或耗散。从时间零到 makespan，把所有开始／结束时间作为切分点，按每个区间上的常数 Hamiltonian 取指数，并按时间组合，得到 \(U_s\)；空日程的演化取恒等。则 \(U_s\) 等于任一线性扩展中按顺序执行各 \(U_v\) 的结果。

**证明。** 在任一切分区间，同时活跃的事件不可能可比较，因为日程满足先后完成约束。因此其 Hamiltonian 两两可交换。由 Eexp，该区间长度 \(\Delta\) 上的演化
\(e^{-i\Delta\sum H_v}\) 等于各 \(e^{-i\Delta H_v}\) 的乘积。

将每个脉冲拆成它跨越的这些区间片段。建立扩展偏序：同一事件的片段按时间排序；若 \(v\prec w\)，则 \(v\) 的所有片段都先于 \(w\) 的所有片段。按实际时间展开得到的片段序列是这个偏序的线性扩展；按原事件的任一线性扩展，将同一事件所有片段连续放置，也是其线性扩展。

两个不可比片段来自不可比事件，其 Hamiltonian 可交换，所以指数矩阵也可交换。用 E1 将实际片段序列重排为按事件分组的序列，不改变算子。每组由同一个 \(H_v\) 的指数构成，利用 Eexp 合并为
\(e^{-i(\sum\Delta)H_v}=e^{-id_vH_v}=U_v\)。这就是目标门电路。□

一个容易检查的充分条件是不可比事件作用于不相交的 tensor 因子：在统一张量因子顺序下，\((A\otimes I)(I\otimes B)=A\otimes B=(I\otimes B)(A\otimes I)\)。有公共 qubit 时仍可能可交换，但需要另外的矩阵证明。

### E.6 定理 E4：实际 Hamiltonian 偏离理想模型时的误差

先设一个区间长 \(t\geq0\)，理想和实际 Hamiltonian 为 Hermitian 矩阵 \(H,K\)。则
\[
\|e^{-itH}-e^{-itK}\|\leq t\|H-K\|.
\tag{E4a}
\]

**证明。** 令 \(F(s)=e^{-i(t-s)H}e^{-isK}\)。利用上节指数导数及乘积法则，
\[
F'(s)=i e^{-i(t-s)H}(H-K)e^{-isK}.
\]
因此 \(F(t)-F(0)=\int_0^tF'(s)\,ds\)。左右指数因子酉，由 L1 和积分三角不等式，积分范数不超过 \(\int_0^t\|H-K\|\,ds=t\|H-K\|\)。而 \(F(t)=e^{-itK}\)、\(F(0)=e^{-itH}\)，故得结论。□

若理想与实际总 Hamiltonian 都分段常数，取公共细分后在第 \(j\) 个区间分别为 \(H_j,K_j\)，长度为 \(\Delta_j\)，则
\[
\|U_H-U_K\|\leq\sum_j\Delta_j\|H_j-K_j\|.
\tag{E4b}
\]

**证明。** 每个区间用 E4a 得局部误差，再用 A1 组合。□

把 E3 与 E4 结合，就能从“理想调度实现目标门电路”和“实际 Hamiltonian 在各区间的偏差证据”推出整体误差，并通过 A2 得到测量误差保证。时间单位、脉冲标定、泄漏能级和噪声若不满足本模型，需要扩充对象与语义；测量采集、经典反馈和帧更新指令也需要各自的解释，不能仅靠调整这个证明中的参数覆盖。

## F. 循环与递归：验证可复用的展开机制

### F.1 自然语言模型

一个编译任务可能被不断拆成子任务，并放回待处理队列。我们希望允许这种超出固定遍历模板的程序结构，同时证明：展开不会改变目标语义；展开过程必定结束。

设每个任务 \(t\) 有算子语义 \(S(t)\) 和自然数等级 \(h(t)\)。处理队列首任务时允许：

- 输出一个已验证片段 \(D\)，其算子满足 \(\llbracket D\rrbracket=S(t)\)，并移除该任务；
- 用按执行顺序排列的 \(t_1,\ldots,t_k\) 替换它，其中 \(k\leq b\)、\(h(t_i)<h(t)\)，且
\[
S(t)=S(t_k)\cdots S(t_1).
\tag{F0}
\]

假定 \(b\geq1\)，每个任务总有上述一种可执行处理，单次处理本身有限完成。已经输出的片段放在待处理任务之前。

### F.2 定理 F1：语义保持与终止上界

上述算法总会结束，输出算子等于初始任务序列的算子。处理步骤数至多
\[
\Phi_0=\sum_{t\in\text{初始任务序列}}(b+1)^{h(t)}.
\]

**证明。** 设已输出算子为 \(W\)，待处理序列为 \(t_1,\ldots,t_r\)。不变量为
\[
S(t_r)\cdots S(t_1)W=U_{\mathrm{target}}.
\]
输出首任务时，\(W\) 更新为 \(S(t_1)W\)，不变量保持。展开首任务时，用 F0 将其对应因子替换为子任务乘积，不变量同样保持。初始时恒等成立，所以对步数归纳不变量始终成立。

令当前势函数 \(\Phi=\sum_t(b+1)^{h(t)}\)。输出一个任务严格减少至少 1。展开等级 \(h\geq1\) 的任务时，新任务总权重不超过
\[
b(b+1)^{h-1}<(b+1)^h,
\]
故仍至少减少 1。等级 0 的任务不能有更低等级子任务，只能输出或展开为空列表，也严格减少。势函数为非负整数，因此至多 \(\Phi_0\) 步后终止；可执行性假设排除了非空队列卡住。最终队列空，不变量化为 \(W=U_{\mathrm{target}}\)。□

本定理可复用于递归门分解或结构化综合。要应用到实际 pass，需证明其每种展开符合 F0，并提供真正下降的等级；仅仅声明一个任意递归函数不能获得此结论。若某次重写会增加这个等级，则应重新设计度量或采用更一般的良基关系。

## 7. 形式化基础：哪些能复用，哪些只能参考

### 7.1 分类标准与版本

- **直接复用定义／基础定理：** 已读到与本文对象一致的声明或证明正文；目标工程采用同一证明助手与相容依赖时，可直接引用。是否全部能在新工程中编译，尚未通过实际导入测试确认。
- **直接复用已有验证任务：** 已有相近的算法及正确性定理，但必须满足其确切门集、参数、良构性、布局等前提。
- **参考／需要连接：** 证明思想和模型可参考；跨 Lean／Rocq、跨矩阵表示或外部工具格式，都需要另外的桥接。不存在自动的证明跨系统搬运。

源码快照、入口和定位列在文末。本文 [M1]–[M19] 均定位在 Physlib 所固定的 mathlib commit，相关文件已读取。该组合使用 Lean 4.35.0；另行查阅的 mathlib 当前开发快照使用不同工具链，未将两个版本当作同一依赖环境。

### 7.2 Lean：可直接复用的对象与基础定理

|本文对象／命题|已有声明与文件|复用判断及需补部分|
|---|---|---|
|有限维 Hilbert 空间|`EuclideanSpace`，`Mathlib/Analysis/InnerProductSpace/PiL2.lean` [M1]|定义可直接用；可取指标 `Fin n → Fin 2` 表示 bit string。不要把普通函数空间默认的 sup 范数当成 Hilbert 范数。|
|酉算子、算子范数、A1|`LinearIsometryEquiv` [M2]；`ContinuousLinearMap.opNorm`、`le_opNorm`、`opNorm_comp_le` [M3]|定义与基础界可直接用；可将酉算子嵌入连续线性映射。本文具体非交换乘积误差定理、相位商距离及其接口仍需组装。|
|矩阵酉群与范数|`Matrix.unitaryGroup` [M4]；矩阵 L2 operator norm 见 [M5]|选择矩阵路线时直接复用。必须显式使用 L2 operator 范数，不能依赖随 imports 改变的其他矩阵 norm 实例。|
|混态和酉演化|`MState`、`MState.psd`、`MState.tr'` [P1]；`MState.uConj` [P2]|与 A2 的对象直接一致；qubit 指标与源 IR 需要解释映射。|
|迹范数夹乘与三角界|`Matrix.traceNorm`、`traceNorm_mul_le_opNorm_traceNorm`、`traceNorm_mul_le_traceNorm_opNorm`、`traceNorm_add_le` [P3]|L3 的主要内容已有对应形式化，不必重新造迹范数。文件在相关部分打开 `Matrix.Norms.L2Operator`。|
|迹距离|`TrDistance` [P4]|定义就是混态差的迹范数的一半；本轮未定位可直接覆盖 A2 全部参考系统／diamond 界的组合定理。|
|量子信道|`MatrixMap` [P5]；`CPTPMap` [P6]；`CPTPMap.compose`、`ofUnitary`、`ofUnitary_eq_conj` [P7]|定义、CP／TP 封装、组合及酉共轭到信道的连接可直接用；本文 A2b 的 diamond 距离接口仍需连接或补充。|
|随机路由的支持集论证|`PMF` [M6]；`PMF.bind`、`support_bind`、`mem_support_bind_iff` [M7]|适合有限／可数概率分支。C1 的不变量可沿支持集归纳；C3 的无限尝试还要建立过程与停止次数，不能只靠 `PMF.bind` 得到。|
|硬件图与路径|`SimpleGraph.Walk` [M8]；布局可采用 `Equiv.Perm`，矩阵置换见 [M9]|图、walk 和置换有现成定义；qubit 布局与整个量子态置换的语义连接需补。|
|矩阵／算子指数|`NormedSpace.exp`、`exp_add_of_commute`、`star_exp` [M10]；`Matrix.exp_conjTranspose` [M11]|Eexp 的主要基础直接可用；不会自动给出事件日程的语义。|
|E4 的微积分|`NormedSpace.hasDerivAt_exp_smul_const` 及其右乘版本 [M12]|固定 Hamiltonian 指数求导已存在；区间积分、片段组合与误差定理需要组装。一般 ODE 入口 [M13] 可供以后扩展。|
|偏序与良基循环|线性扩展基础 [M14]；`WellFounded` 相关库 [M15]|可复用类型与归纳工具；E1 的相邻不可比交换接口和 F1 的任务语义、势函数定理需补。|

**B 的 Lean 路线。** 可用 mathlib 的 `ZMod 2` [M16]／有限函数、`Matrix.mulVec` 及线性映射连接 [M17]、矩阵一般线性群 [M18] 和有限映射保存 parity 系数。这些是基础对象；本文的 `PhaseIR`、提取函数、gadget 综合及对应语义定理仍需要定义。本轮找到的最直接的既有任务级证据在 VOQC。张量积采用矩阵路线时，可复用 Kronecker product 及 `mul_kronecker_mul` [M19]，再补 qubit 索引重排的连接。

**D 的 Lean 路线。** D1、D2 的证书格式需要新增；基本数组／列表、有限图、整数与有理数运算可直接复用。D3、D4 的数学可靠性只需要有限线性代数与有序域不等式，没有必要先形式化整个 CPLEX。证明证书可靠性与实现一个可运行的证书解析器是两项责任。

### 7.3 Rocq：已有任务级证明

|项目与精确入口|已核查的内容|与本文的关系|
|---|---|---|
|SQIR `SQIR/UnitarySem.v` [S1]|`uc_eval`、`uc_equiv`、`denote_Rz`、`denote_swap`|现成的电路矩阵语义。注意其 `Rz` 在此语义中对应 `phase_shift`，不能只凭名字认作 \(e^{-i\theta Z/2}\)。|
|VOQC `VOQC/RotationMerging.v` [S2]|`merge_rotations_sound`：良构输入经 `merge_rotations` 后语义相等|可直接复用现有旋转合并算法及定理。它不等同于本文 B 的整个重新综合算法；本文 B 可以参考其表示、证明分解与 gate-list 接口。|
|VOQC `VOQC/RzQGateSet.v` [S3]|`URzQ_Rz (a : Q)`，其解释角度为 `Q2R a * PI`|明确限制为有理倍 \(\pi\) 的相位参数；任意实参数 B1 不能无条件直接套现有定理。|
|VOQC `VOQC/Layouts.v` [S4]|`layout`、`layout_bijective`、`swap_log_preserves_bij`|C 的布局数据结构及双射保持有直接对应物。布局用两个有限映射实现，并非 Lean 的 `Equiv.Perm`。|
|VOQC `VOQC/SwapRoute.v` [S5]|`uc_equiv_perm_ex`、`swap_route_sound`、`swap_route_respects_undirected`|C 的输入／输出置换语义及基于路径的路由已有任务级证明；路径函数及其性质是定理前提。|
|VOQC `VOQC/MappingValidation.v` [S6]|`check_swap_equivalence`、`check_swap_equivalence_implies_equivalence`、`check_constraints_implies_respect_constraints`|最接近 D1 的直接复用结果：检查器接受蕴含布局意义下等价，并有硬件约束检查定理。|
|CoqQ `src/mxnorm.v` [Q1]|`i2norm`、`trnorm`、`i2normUl`、`trnormMl`、`trnormMr`|A 的另一条范数基础路线。它使用 MathComp 的矩阵／复数体系，与 SQIR／QuantumLib 不自动共享表示。|
|CoqQ `src/QIT/series.v` [Q2]|`expM`、收敛结果、`expM_trans_xcom`|E 的算子指数基础可参考或在 CoqQ 内复用；不等于现成的 pulse-schedule 验证器。|
|Giallar 自身 Coq 目录 [G1]–[G3]|`qgate`、`eval`、`symb_eval_soundness` 以及具体门重写定理|适合研究现有符号层与矩阵层的关系。不能据此认定任意 Python pass、任意扩展门或整个 SMT 编码已被 Coq 核验。|
|SMTCoq [T1]|外部 SAT／SMT proof witness 的已认证检查机制|可参考其“外部搜索＋小检查器”架构；其文档列出的 solver 格式不等于直接支持任意 Z3／CPLEX 输出，更不提供本文量子映射语义。|

`check_swap_equivalence_implies_equivalence` 的声明要求两个输入电路良构、两个初始布局双射，以及检查器返回 `Some`。其文件还明确列出识别边界：显式 SWAP 与分解成三个 CNOT 的形式不会自动视作同一对象；一般语义上的门交换及边路由边优化可能不被识别。拒绝结果不意味着两个电路不等价。

### 7.4 两项补充参考及其边界

**Prosa：可以参考的调度形式语义。** 已查看其官方 `prosa.behavior.schedule` 文档 [R1]：`ProcessorState` 抽象处理器状态、运行中的 job 与获得的 service，`schedule` 是从时刻到处理器状态的函数。它为将来扩展到执行时间、阻塞和实时约束提供现成的建模参考。不过，本文 E 使用有限事件、多个独占控制资源和量子演化；不能直接把 Prosa 的处理器／job 定理解释为脉冲正确性。本轮将它归为“需建立对应关系的参考基础”，没有承诺直接集成。

**Gleipnir：可以参考的量子误差逻辑。** 论文 [R2] 采用由近似状态与距离界约束的 diamond 误差度量，适合研究如何利用输入态信息收紧 A 的最坏情况误差。本轮定位到的是论文中的模型与推理规则，未核验到可以直接导入 Lean／Rocq 的相应证明模块，因而仅列作数学与逻辑设计参考，不计入已确认的机器证明基础。

### 7.5 对直接复用的具体建议

1. **A、E 的分析层优先以 mathlib／Physlib 为一组依赖。** 算子范数、迹范数、混态和指数已具备明确入口。新增工作集中在误差契约、组合定理及日程解释。
2. **B、C、D 的已有 Rocq 成果作为任务级基线。** 若目标必须在 Lean，优先移植规格和证明结构，并明确建立表示对应；不能把导入另一证明助手的源码视为直接复用。
3. **先实现与策略无关的合同。** C1、D1 不依赖搜索启发式；A1、A2 不依赖具体近似综合器；E1、E3 不依赖某个调度器。这些合同可以长期服务于不同实现。
4. **不要把规格弱化藏进复用。** “电路没变”不等于分析 pass 输出正确；“可行”不等于最优；“随机选择都保持语义”不等于一定终止；“单次输出通过检查”不等于源编译器所有输出都正确。

## 8. 从本报告到真实实现还需完成的连接

|任务|已完成的数学保证|尚需针对真实实现核查的内容|
|---|---|---|
|A|给定局部证据的组合；具体删门算法的全局误差|`UnitarySynthesis` 实际算法、浮点／区间数值证据、角度与相位约定、允许的目标门集|
|B|本文 CNOT＋相位片段的提取与重新综合|Qiskit IR 导入、符号参数语义、片段边界、额外门与条件执行|
|C|合法路由 trace 的正确性和本文包装器终止性|原随机路由的状态更新、失败回退、终止策略、定向硬件门和 SWAP 分解|
|D|本文有限证书检查的可靠性和最优性证书定理|外部输出解析、编码与原问题对应、实际证书格式、数值误差、错误处理|
|E|资源合法性、固定偏序最优性、矩形脉冲对应、分段常数扰动界|具体脉冲指令、帧／相位更新、采样时钟、控制资源、漂移／串扰／泄漏／耗散模型和标定假设|
|F|本文展开规则的语义保持与终止|实际循环体满足合同、任务等级下降、工具函数及异常行为的语义|

本轮的完整证明覆盖表中“已完成的数学保证”。最后一列既没有被偷偷加成结论的假设，也没有被声称已解决；它们是将抽象定理用于指定实现时必须另行交付的证据。

## 9. 来源、版本与核验范围

直接复用项的源码来源采用固定 commit 链接；补充参考中的动态文档单独标明。对于标为直接复用的关键对象，本轮读取了相应定义、定理声明及相关证明正文。没有执行 Lean／Rocq 构建，没有进行全依赖公理闭包审计；因此“存在可复用声明”与“已经在新项目中成功集成”明确分开。

对读取的源码进行文本检查没有发现 `sorry`／`Admitted` 标记；这只说明该批已读文件的表面情况，不推出所有传递依赖无额外公理。未找到某个即用定理，也只表示本轮没有定位到，不能推出整个生态不存在它。

以下来源索引给出固定版本和对应文件，便于下一阶段直接从这些位置开始。

### 9.1 版本快照

|项目|固定 commit|依赖／核查说明|
|---|---|---|
|mathlib（本文引用版本）|[56a005855ea1](https://github.com/leanprover-community/mathlib4/tree/56a005855ea17e0b0958f73ec801ae140b0a1679)|Physlib 清单固定的 mathlib，Lean 4.35.0|
|Physlib|[acb218ef79a2](https://github.com/leanprover-community/physlib/tree/acb218ef79a228b13865b4d0cadb0599ce82ad83)|Lean 4.35.0；[lake-manifest.json](https://github.com/leanprover-community/physlib/blob/acb218ef79a228b13865b4d0cadb0599ce82ad83/lake-manifest.json)|
|SQIR／VOQC|[134fb9422650](https://github.com/inQWIRE/SQIR/tree/134fb942265091baa3e3972f78f72da41827351f)|[coq-voqc.opam](https://github.com/inQWIRE/SQIR/blob/134fb942265091baa3e3972f78f72da41827351f/coq-voqc.opam)：Coq ≥ 8.16、QuantumLib ≥ 1.6.0、SQIR ≥ 1.3.2、Interval ≥ 4.9.0|
|CoqQ|[b169ea462b13](https://github.com/coq-quantum/CoqQ/tree/b169ea462b13d20b05e03615ad1d56cc8d8f5784)|[coq-mathcomp-quantum.opam](https://github.com/coq-quantum/CoqQ/blob/b169ea462b13d20b05e03615ad1d56cc8d8f5784/coq-mathcomp-quantum.opam)：Coq 8.18.0、MathComp 2.2.0、MathComp Analysis 1.3.1|
|Giallar|[7110ee838ee2](https://github.com/taorunz/Giallar/tree/7110ee838ee25f2f9689db2c5d1ab9b51cc93ced)|读取选定 Coq 文件；未重建其历史依赖环境|
|SMTCoq|[c0bd765e4283](https://github.com/smtcoq/smtcoq/tree/c0bd765e4283eef55a8f495706475305dc83c583)|读取 README 的证书支持说明；本轮作为架构参考|

### 9.2 定义与定理入口

下列链接指向固定版本的文件；有明确单一入口的，链接同时定位到声明所在行。完整文件提供该声明的前提、命名空间和证明上下文。

|编号|文件路径|主要入口|
|---|---|---|
|[M1]|`Mathlib/Analysis/InnerProductSpace/PiL2.lean`|`EuclideanSpace`|
|[M2]|`Mathlib/Analysis/Normed/Operator/LinearIsometry.lean`|`LinearIsometryEquiv`|
|[M3]|`Mathlib/Analysis/Normed/Operator/Basic.lean`|`opNorm_comp_le`|
|[M4]|`Mathlib/LinearAlgebra/UnitaryGroup.lean`|`Matrix.unitaryGroup`|
|[M5]|`Mathlib/Analysis/CStarAlgebra/Matrix.lean`|`L2 operator norm`|
|[M6]|`Mathlib/Probability/ProbabilityMassFunction/Basic.lean`|`PMF`|
|[M7]|`Mathlib/Probability/ProbabilityMassFunction/Monad.lean`|`PMF.mem_support_bind_iff`|
|[M8]|`Mathlib/Combinatorics/SimpleGraph/Walk/Basic.lean`|`SimpleGraph.Walk`|
|[M9]|`Mathlib/LinearAlgebra/Matrix/Permutation.lean`|`Matrix.permMatrixHom`|
|[M10]|`Mathlib/Analysis/Normed/Algebra/Exponential.lean`|`NormedSpace.exp_add_of_commute`|
|[M11]|`Mathlib/Analysis/Normed/Algebra/MatrixExponential.lean`|`Matrix.exp_conjTranspose`|
|[M12]|`Mathlib/Analysis/SpecialFunctions/Exponential.lean`|`NormedSpace.hasDerivAt_exp_smul_const`|
|[M13]|`Mathlib/Analysis/ODE/ExistUnique.lean`|`ODE existence / uniqueness`|
|[M14]|`Mathlib/Order/Extension/Linear.lean`|`LinearExtension`|
|[M15]|`Mathlib/Order/WellFounded.lean`|`WellFounded`|
|[M16]|`Mathlib/Data/ZMod/Defs.lean`|`ZMod`|
|[M17]|`Mathlib/LinearAlgebra/Matrix/ToLin.lean`|`mulVec / linear-map bridge`|
|[M18]|`Mathlib/LinearAlgebra/Matrix/GeneralLinearGroup/Defs.lean`|`Matrix.GeneralLinearGroup`|
|[M19]|`Mathlib/LinearAlgebra/Matrix/Kronecker.lean`|`Matrix.mul_kronecker_mul`|
|[P1]|`QuantumInfo/States/Mixed/MState.lean`|`MState`|
|[P2]|`QuantumInfo/Operators/Unitary.lean`|`MState.uConj`|
|[P3]|`QuantumInfo/ForMathlib/MatrixNorm/TraceNorm.lean`|`traceNorm_mul_le_opNorm_traceNorm`|
|[P4]|`QuantumInfo/States/Mixed/TraceDistance.lean`|`TrDistance`|
|[P5]|`QuantumInfo/Channels/MatrixMap.lean`|`MatrixMap`|
|[P6]|`QuantumInfo/Channels/Bundled.lean`|`CPTPMap`|
|[P7]|`QuantumInfo/Channels/CPTP.lean`|`CPTPMap.ofUnitary`|
|[S1]|`SQIR/UnitarySem.v`|`uc_eval`|
|[S2]|`VOQC/RotationMerging.v`|`merge_rotations_sound`|
|[S3]|`VOQC/RzQGateSet.v`|`RzQ gate set`|
|[S4]|`VOQC/Layouts.v`|`layout`|
|[S5]|`VOQC/SwapRoute.v`|`swap_route_sound`|
|[S6]|`VOQC/MappingValidation.v`|`check_swap_equivalence_implies_equivalence`|
|[Q1]|`src/mxnorm.v`|`trnormMl`|
|[Q2]|`src/QIT/series.v`|`expM_trans_xcom`|
|[G1]|`giallar/coq_proof/certiq.v`|`qgate / eval`|
|[G2]|`giallar/coq_proof/soundness.v`|`symb_eval_soundness`|
|[G3]|`giallar/coq_proof/rewriting.v`|`cnot_cancel`|

### 9.3 论文与补充参考

- [G] Tao et al., *Giallar: Push-Button Verification for the Qiskit Quantum Compiler*, PLDI 2022；arXiv:2205.00661v1。§7 随机化修复案例；§8 未覆盖 pass 与 limitations。
- [T1] SMTCoq README，固定在上述 commit；外部 proof witness 支持范围与检查器定位。
- [R1] Prosa 官方生成文档，`prosa.behavior.schedule`，查阅日 2026-11-20。此链接是动态 master 文档，未作为已固定版本的直接依赖。
- [R2] Tao et al., *Gleipnir: Toward Practical Error Analysis for Quantum Programs*, PLDI 2021。仅作为误差规格与推理规则参考。

[M1]: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Analysis/InnerProductSpace/PiL2.lean#L114
[M2]: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Analysis/Normed/Operator/LinearIsometry.lean#L432
[M3]: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Analysis/Normed/Operator/Basic.lean#L408
[M4]: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/LinearAlgebra/UnitaryGroup.lean#L105
[M5]: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Analysis/CStarAlgebra/Matrix.lean#L196
[M6]: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Probability/ProbabilityMassFunction/Basic.lean#L45
[M7]: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Probability/ProbabilityMassFunction/Monad.lean#L119
[M8]: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Combinatorics/SimpleGraph/Walk/Basic.lean#L54
[M9]: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/LinearAlgebra/Matrix/Permutation.lean#L90
[M10]: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Analysis/Normed/Algebra/Exponential.lean#L521
[M11]: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Analysis/Normed/Algebra/MatrixExponential.lean#L93
[M12]: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Analysis/SpecialFunctions/Exponential.lean#L382
[M13]: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Analysis/ODE/ExistUnique.lean
[M14]: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Order/Extension/Linear.lean#L76
[M15]: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Order/WellFounded.lean
[M16]: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Data/ZMod/Defs.lean#L139
[M17]: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/LinearAlgebra/Matrix/ToLin.lean
[M18]: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/LinearAlgebra/Matrix/GeneralLinearGroup/Defs.lean#L42
[M19]: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/LinearAlgebra/Matrix/Kronecker.lean#L382
[P1]: https://github.com/leanprover-community/physlib/blob/acb218ef79a228b13865b4d0cadb0599ce82ad83/QuantumInfo/States/Mixed/MState.lean#L51
[P2]: https://github.com/leanprover-community/physlib/blob/acb218ef79a228b13865b4d0cadb0599ce82ad83/QuantumInfo/Operators/Unitary.lean#L33
[P3]: https://github.com/leanprover-community/physlib/blob/acb218ef79a228b13865b4d0cadb0599ce82ad83/QuantumInfo/ForMathlib/MatrixNorm/TraceNorm.lean#L305
[P4]: https://github.com/leanprover-community/physlib/blob/acb218ef79a228b13865b4d0cadb0599ce82ad83/QuantumInfo/States/Mixed/TraceDistance.lean#L24
[P5]: https://github.com/leanprover-community/physlib/blob/acb218ef79a228b13865b4d0cadb0599ce82ad83/QuantumInfo/Channels/MatrixMap.lean#L30
[P6]: https://github.com/leanprover-community/physlib/blob/acb218ef79a228b13865b4d0cadb0599ce82ad83/QuantumInfo/Channels/Bundled.lean#L75
[P7]: https://github.com/leanprover-community/physlib/blob/acb218ef79a228b13865b4d0cadb0599ce82ad83/QuantumInfo/Channels/CPTP.lean#L434
[S1]: https://github.com/inQWIRE/SQIR/blob/134fb942265091baa3e3972f78f72da41827351f/SQIR/UnitarySem.v#L24
[S2]: https://github.com/inQWIRE/SQIR/blob/134fb942265091baa3e3972f78f72da41827351f/VOQC/RotationMerging.v#L1215
[S3]: https://github.com/inQWIRE/SQIR/blob/134fb942265091baa3e3972f78f72da41827351f/VOQC/RzQGateSet.v#L18
[S4]: https://github.com/inQWIRE/SQIR/blob/134fb942265091baa3e3972f78f72da41827351f/VOQC/Layouts.v#L22
[S5]: https://github.com/inQWIRE/SQIR/blob/134fb942265091baa3e3972f78f72da41827351f/VOQC/SwapRoute.v#L578
[S6]: https://github.com/inQWIRE/SQIR/blob/134fb942265091baa3e3972f78f72da41827351f/VOQC/MappingValidation.v#L265
[Q1]: https://github.com/coq-quantum/CoqQ/blob/b169ea462b13d20b05e03615ad1d56cc8d8f5784/src/mxnorm.v#L4230
[Q2]: https://github.com/coq-quantum/CoqQ/blob/b169ea462b13d20b05e03615ad1d56cc8d8f5784/src/QIT/series.v#L720
[G1]: https://github.com/taorunz/Giallar/blob/7110ee838ee25f2f9689db2c5d1ab9b51cc93ced/giallar/coq_proof/certiq.v#L7
[G2]: https://github.com/taorunz/Giallar/blob/7110ee838ee25f2f9689db2c5d1ab9b51cc93ced/giallar/coq_proof/soundness.v#L201
[G3]: https://github.com/taorunz/Giallar/blob/7110ee838ee25f2f9689db2c5d1ab9b51cc93ced/giallar/coq_proof/rewriting.v#L6
[G]: https://arxiv.org/pdf/2205.00661v1
[T1]: https://github.com/smtcoq/smtcoq/blob/c0bd765e4283eef55a8f495706475305dc83c583/README.md
[R1]: https://prosa.mpi-sws.org/branches/master/pretty/prosa.behavior.schedule.html
[R2]: https://www.cs.columbia.edu/~rgu/publications/pldi21-tao.pdf
