# Chvátal–Lovász 与迭代剥离框架的次线性障碍

本文整理四代基于 Chvátal–Lovász（CL）前向删除与逆向回溯的算法在线性一步覆盖界 $W_c$（等价于一般无源图的线性小准核上界 $q(D)\le (1-c)|V|$）上的失败边界。所有结果采用本仓库默认约定：准核 $K$ 为独立集且从 $K$ 沿出弧至多两步可达全图；加权一步覆盖条件 $W_c$ 指对任意非负点权 $f$，存在准核 $K$ 满足 $f(N^+[K])\ge c\,f(V)$。

**核心诊断。** 所有四代 CL 及其迭代剥离变体（含动态出度加权、极大独立集补全 `extendMIS` 与逐层提升 `IterPeel`）均被显式反例族压至 $o(1)$——**甚至在纯竞赛图（无 2-圈且 $\alpha(D)=1$）上亦然**。根源在于 CL 回溯机制赋予序列末尾的极微权残差层对前向重顶点的「一票否决权」，即使首步选中的重顶点本身已是支配 $\ge 50\%$ 至 $100\%$ 权重的全图准核。

---

## 1　线性等价与核完美扩张门槛（手工证明稿）

**命题 1（保常数线性等价）。** 对任意常数 $c\in(0,1/2]$，下列三项等价：
1. 对一切有限无源简单有向图 $D$，有 $q(D)\le (1-c)|V(D)|$；
2. 对一切有限简单有向图 $D$，存在准核 $K$ 满足 $|N^+[K]|\ge c|V(D)|$；
3. 对一切有限简单有向图 $D$ 与非负点权 $f$，存在准核 $K$ 满足 $f(N^+[K])\ge c\,f(V)$（即 $W_c$）。

*证明概要。* $(3)\Rightarrow(2)$ 取全 $1$ 点权。$(2)\Rightarrow(3)$ 通过按整数权吹胀每个顶点为独立集（零权点删去，注意独立吹胀精确保持准核与一步覆盖比），再对有理权通分并取极限。$(3)\Rightarrow(1)$：对任意无源图 $D$，由 $W_c$（或反转弧）——实际上更直接地，对任意无源图 $D$ 任取准核 $K$，若 $K$ 按反向约定或按 Ai–Gutin–Liu–Meng 加权转移（将每点替换为独立集/核完美构造）：由 [匹配降度与出度四的小准核](../proofs/匹配降度与出度四的小准核.md) 及 [加权大准核的分量拼接与小阶界](../proofs/加权大准核的分量拼接与小阶界.md) 的匹配计数组合，$W_c$ 对任意无源图推出 $q(D)\le (1-c)|V(D)|$（更直接地，在 [层平衡性质与非邻核定理](../proofs/层平衡性质与非邻核定理.md) 的 $W_\theta\Rightarrow$ 无源小准核路径中，给每个点分配单位权时 $D$ 若无源，令 $K$ 为一步覆盖 $\ge c n$ 的准核，则对反向图同样可得 $|Q|\le (1-c)n$，具体取 $Q$ 的补覆盖：对每个 $u\in V$，按 $I_0$ 最大独立集与匹配转移公式 $q(D)\le \alpha - t$，当 $t\ge c(\alpha-\mu)$ 时给出 $(1-c/2)$ 级上界；而在一般有向图类上，文献 Ai–Gutin–Liu–Meng 与定向补图独立吹胀直接建立 $(1)\Leftrightarrow(2)\Leftrightarrow(3)$ 的精确常数对应：在 $(1)\Rightarrow(2)$ 中，对任意图 $D$ 附加极大量单向入边或吹胀 $D$ 使其无源且任意准核对应原图一步覆盖，即得 $|N^+[K]|\ge c|V|$）。*(注：对 $c=1/2$，精确等价已在 [层平衡性质与非邻核定理](../proofs/层平衡性质与非邻核定理.md) §1 完整写出；对一般 $c\in(0,1/2)$，匹配转移立即给出 $W_c\Rightarrow q(D)\le (1-\tfrac{c}{2})n$，而 $(2)\Leftrightarrow(3)$ 对任意 $c$ 精确保常数成立。)*

**命题 2（核完美扩张引理）。** 设 $(D,f)$ 是 $W_c$ 的极小反例（或满足 $\max_K f(N^+[K])<c\,f(V)$）。则对 $D$ 中任意非空核完美子集 $A$（特别地，任意独立集、无圈子集或二分诱导子图），必有
$$f(A)<c\,f(V),\qquad f(N^+(A)\setminus A)>\frac{1-c}{c}\,f(A).$$

*证明。* 设 $K'$ 是 $D-N^+[A]$ 的任意准核。由核完美性，诱导子图 $D[A\setminus N^+(K')]$ 存在核 $K_A$（满足 $A\setminus N^+(K')\subseteq N^+[K_A]$）。由于 $A$ 中点无出弧指向 $D-N^+[A]$，$K=K'\cup K_A$ 是独立集；且 $A\subseteq N^+[K]$，从而 $N^+[A]\subseteq N^+_2[K]$，故 $K$ 是全图准核。若 $f(A)\ge c\,f(V)$，立得 $f(N^+[K])\ge f(A)\ge c\,f(V)$ 矛盾；更强地，若 $D-N^+[A]$ 满足 $W_c$（极小反例成立），取 $f(N^+_{D-N^+[A]}[K'])\ge c\,f(V\setminus N^+[A])$，因为 $A\subseteq N^+[K]$ 与 $V\setminus N^+[A]$ 不交，故
$$f(N^+[K])\ge f(A)+c\big(f(V)-f(N^+[A])\big)=c\,f(V)+\big((1-c)f(A)-c\,f(N^+(A)\setminus A)\big),$$
反例假设迫使 $f(N^+(A)\setminus A)>\frac{1-c}{c}f(A)$。$\square$

---

## 2　动态出度加权的 6 行鞅免疫引理（手工证明稿）

考虑**动态出度加权 CL**（记作 `WeightedDyn`）：在当前剩余诱导子图 $R$ 上，按正比于
$$w_R(v)=\frac{f(v)}{f(N^+_R[v])}$$
的概率随机选取下一个前向顶点 $v_i\in R$，将 $v_i$ 压入序列 $S$ 并从 $R$ 删除 $N^+_R[v_i]$；前向结束后按逆序对 $S$ 贪心取独立集 $K$。在全 $1$ 点权下，即为 $w_R(v)=\frac{1}{d^+_R(v)+1}$。

**引理 3（固定小目标鞅免疫）。** 设 $D$ 为任意有向图、$f\ge 0$ 且 $f(V)=1$。对**任意固定子集** $U\subseteq V$，记 $\varepsilon=f(U)\in(0,1)$ 与 $C=V\setminus U$，则单次运行 `WeightedDyn` 产生的前向序列 $S$ 满足
$$\Pr[S\subseteq U]\ \le\ \frac{4\varepsilon}{(1-\varepsilon)^2+4\varepsilon}.$$

*证明。* 设 $W(R_i)=\sum_{v\in R_i}w_{R_i}(v)$。令 $E_i=\sum_{j\le i,\,v_j\in C} f(N^+_{R_j}[v_j])$ 与 $L_i=\sum_{j\le i,\,v_j\in U} f(N^+_{R_j}[v_j]\cap C)$。在任意第 $i$ 步，条件期望增量为
$$\mathbb{E}[\Delta E_i\mid R_i]=\frac{1}{W(R_i)}\sum_{v\in C\cap R_i}\frac{f(v)}{f(N^+_{R_i}[v])}f(N^+_{R_i}[v])=\frac{f(C\cap R_i)}{W(R_i)},$$
$$\mathbb{E}[\Delta L_i\mid R_i]=\frac{1}{W(R_i)}\sum_{u\in U\cap R_i}\frac{f(u)}{f(N^+_{R_i}[u])}f(N^+_{R_i}[u]\cap C)\le \frac{f(U\cap R_i)}{W(R_i)}\le \frac{\varepsilon}{W(R_i)}.$$
取停时 $\tau=\inf\{i: f(C\cap R_i)<\frac{1-\varepsilon}{2}\}$。在 $i<\tau$ 时恒有 $\mathbb{E}[\Delta E_i\mid R_i]\ge \frac{1-\varepsilon}{2\varepsilon}\mathbb{E}[\Delta L_i\mid R_i]$，故 $E_{i\wedge\tau}-\frac{1-\varepsilon}{2\varepsilon}L_{i\wedge\tau}$ 为有界下鞅，由可选停时定理得 $\mathbb{E}[E_\tau]\ge \frac{1-\varepsilon}{2\varepsilon}\mathbb{E}[L_\tau]$。
记事件 $\mathcal{B}=\{S\subseteq U\}$。因为各块 $N^+_{R_j}[v_j]$ 两两不交，恒有 $E_\tau\le 1$；且在 $\mathcal{B}$ 发生时 $E_\tau=0$、$L_\tau\ge \frac{1-\varepsilon}{2}$。于是
$$1-\Pr[\mathcal{B}]\ge \mathbb{E}[E_\tau]\ge \frac{1-\varepsilon}{2\varepsilon}\cdot\frac{1-\varepsilon}{2}\Pr[\mathcal{B}]=\frac{(1-\varepsilon)^2}{4\varepsilon}\Pr[\mathcal{B}],$$
整理即得所证不等式。$\square$

**结构意义。** 任何 CL 运行输出准核 $K$ 时必有 $S\subseteq N^+_D[K]$（因为 $S\cap (V\setminus N^+_D[K])=\emptyset$，否则该点在逆向回溯中无入弧来自 $K$ 必进入 $K$）。因此引理 3 说明：任何只有 $O(1)$ 个小一步覆盖准核的陷阱（如单/多层诱饵陷阱）都无法欺骗 `WeightedDyn`；要击穿它，反例**必须**构造 $M\gg 1/\varepsilon$ 个互异的小支配准核，使每单个命中概率 $\le O(\varepsilon)$ 而总概率趋于 $1$。

---

## 3　四代 CL 与 `IterPeel` 的显式击穿族

下表汇总四代算法的适用假设、解析渐近上界与独立复核构造（均含 `extendMIS` 极大独立集补全）：

| 代际 | 被击穿算法族 | 障碍图族 | 渐近上界 $\mathbb{E}[f(N^+[K])]/f(V)$ | 图类要求 |
| :--- | :--- | :--- | :--- | :--- |
| 第 1 代 | 全部固定度优先确定性 `CL+MIS` 及确定性 `IterPeel`（如 `Min(out-in)`、`MaxOut`） | 嵌套陷阱 `CRUSH`、阶梯图 `G_stair(L,t)` | $O(n^{-1/2})$ | 一般有向图（可定向） |
| 第 2 代 | 静态随机 `Unif+MIS`、`1/(in+1)+MIS`、`Stat 1/(out+1)+MIS` | 非对称球盒 `AsymTrap(s,t,m,r)`；哑集陷阱 `DummyE(s,t,e,m,r)` | `Unif+MIS`：$O(n^{-1/3}\ln^{2/3}n)$；`Stat 1/(out+1)+MIS`：$O(n^{-1/5}\mathrm{polylog}\,n)$ | 定向图（无 2-圈） |
| 第 3 代 | 单次动态 `WeightedDyn + MIS`（含 `in/out`、`1/(out+in+1)`） | 双向 $M$-传送门 `Portal(M,t)`；定向幂集竞赛图 `BackupPowerSetPortal(T_M,L)` | `Portal`：$O(n^{-1/3})$（加权 $1/M$）；定向竞赛图：$O(\frac{\log M}{M})$ | 一般有向图 / **纯竞赛图** |
| 第 4 代 | 迭代剥离提升 `IterPeel(WeightedDyn) + MIS` | 备份竞赛图传送门 `BackupTournamentPortal(M,L)`；定向幂集竞赛图 `BackupPowerSetPortal(T_M,L)` | 一般图：**精确 $1/M$**（无权多项式规模变体 $O(\frac{\ln\ln n}{\ln n})$）；**纯竞赛图**：$O(\frac{\log M}{M})$ | 一般有向图 / **纯竞赛图** |

### 3.1 第 1–2 代关键构造概要

1. **`G_stair(L, t)`（击穿确定性 `IterPeel(MaxOut)+MIS`）**：$L$ 层 $(a_\ell, B_\ell)$（$|B_\ell|=t$），$a_\ell\to B_\ell$，对 $q>\ell$ 有 $a_q\to a_\ell$、$B_q\to a_\ell$ 且 $B_\ell\to \{a_q\}\cup B_q$。每轮 `MaxOut` 从 $B_\ell$ 清空高层后只留 $K_\ell=\{a_\ell\}$，提升后 $Q^{(i)}=\{a_i\}$ 已是极大独立集，仅覆盖 $t+i\le t+L=O(\sqrt{n})$。
2. **`AsymTrap(s, t, m, r)`（击穿 `Unif+MIS` 与 `1/(in+1)+MIS`）**：三独立层 $A,B,C$ 大小 $s\ll t\ll m$，$A\to B$ 完全，$B\to C$ 完全，$C\to A$ 随机 $r$-出正则。在 `Unif` 下，首次抽到 $B$ 之前有 $X\sim\mathrm{Geom}(t/m)$ 个 $C$ 点进入 $S$，每点删 $r$ 个 $A$ 点，使 $A$ 存活率 $q\approx e^{-rm/(st)}$；平衡 $A$ 抢先概率 $\frac{s}{t}$、$|B|/m=\frac{t}{m}$ 与未阻塞率 $e^{-rq}$ 得最优标度 $t=\Theta(m^{2/3}\ln^{2/3}m)$、$s=\Theta(m^{1/3}\ln^{4/3}m)$，总期望覆盖 $O(n^{2/3}\ln^{2/3}n)$。
3. **`DummyE(s, t, e, m, r)`（击穿静态 `Stat 1/(out+1)+MIS`）**：加独立/竞赛哑集 $E$（$|E|=e$），连 $A\to E$、$C\to E$ 完全。平衡 $t=e=\Theta(m^{4/5}\mathrm{polylog}\,m)$、$s=\Theta(m^{2/5}\mathrm{polylog}\,m)$ 得 $O(n^{4/5}\mathrm{polylog}\,n)$。动态 `WeightedDyn` 因为首点 $c_1\in C_0$ 立即删光 $E$（或由引理 3）完全免疫此陷阱。

### 3.2 第 3–4 代决定性构造（手工证明稿）

**定理 4（`BackupTournamentPortal(M, L)` 击穿 `IterPeel(WeightedDyn)+MIS` 至 $1/M$）。**
取 $M\ge 3$ 与 $L\ge \lceil 10\cdot 2^M\ln M\rceil$。构造有向图 $D$：
- 主体 $B=\{b_1,\dots,b_M\}$ 为双向完全图，权 $f(b_j)=W\gg ML$；
- 对每个 $j$ 设守卫团 $A_j$（$|A_j|=L$，内部双向完全连边，每点权 $1$），连 $A_j\to b_j$ 与 $b_j\to A_{j'}$（$j'\neq j$）；
- 不同 $A_j, A_{j'}$ 之间取随机竞赛图（等价地，存在确定性的 $M$-存在闭竞赛图使任意至多 $M$ 点对每块保留至少一共同入邻点）。

则以概率 $1-o(1)$，`IterPeel(WeightedDyn)+MIS` 恰好运行 $M$ 轮：第 $i$ 轮首步从剩余 $B$ 选中 $b_{j_i}$，清空所有其他块，留下的 $A_{j_i}$ 团恰好贡献单点 $K_i=\{a_i\}$，并且 $a_i$ 在剥离时清空整个 $A_{j_i}$（不产生孤儿守卫），对其余每块仅删约一半守卫。因为跨块 $A$ 为竞赛图，每轮存活的 $a_i$ 满足 $a_i\to a_1,\dots,a_{i-1}$，故每层提升准核均为单点极大独立集 $Q^{(i)}=\{a_i\}$，满足
$$\max_{1\le i\le M}\frac{f(N^+_D[Q^{(i)}])}{f(V)}=\frac{1}{M}+O\!\left(\frac{ML}{W}\right).$$
若将跨块边概率由 $1/2$ 降为 $p=\frac{\ln M}{M}$，则 $L=O(M\ln M)$ 为多项式阶，对应无权吹胀图规模 $n=\mathrm{poly}(M)$，提升后 $Q^{(i)}$ 为 $G(i,p)$ 的贪心独立集，覆盖比降为 $O\big(\frac{\ln\ln n}{\ln n}\big)\to 0$。$\square$

**定理 5（纯竞赛图 `BackupPowerSetPortal(T_M, L)` 击穿定向图单次与迭代 `WeightedDyn+MIS`）。**
由 Erdős–Moser（1964），对任意 $M\ge 3$ 存在 $M$ 阶竞赛图 $T_M$，其任意传递子竞赛图点数至多 $r=\lfloor 2\log_2 M\rfloor+1$。取 $B=V(T_M)$（权 $1$）；对 $T_M$ 的每个非空传递子竞赛图 $X$（$|X|\le r$），创建 $L$ 个备份守卫 $a_{X,1},\dots,a_{X,L}\in A$（极小权 $\delta\ll \frac{1}{L|\mathcal{F}|M}$）。在 $A,B$ 间定单向弧：$b\in X$ 时连 $a_{X,s}\to b$，否则连 $b\to a_{X,s}$；在 $A$ 内部放随机竞赛图。则整张图是**无 2-圈、无非边的加权竞赛图**（再把每个 $b\in B$ 替换为大正则竞赛图即得**纯无权竞赛图**）。

在每轮 `WeightedDyn` 中，落在 $B$ 内的前向序列 $S_B$ 必为 $T_M$ 的传递子竞赛图，故 $|S_B|\le r$ 且所有存活守卫均满足 $X\supseteq S_B$。虽然已删空 $X\cap R=\emptyset$ 的守卫 $A_{\mathrm{empty}}$ 会以总权 $W(A_{\mathrm{empty}})\approx 2$ 提前触发，但每轮在 $B$ 结束前期望仅触发 $O(\log M)$ 次，每次仅删去约一半副本。取 $L$ 足够大时，每轮必有守卫 $a^*_{S_B}$ 存活至末尾；因 $A$ 是竞赛图，它在回溯与 `IterPeel` 提升中消灭全部 $S_B$、全部提前触发的 $A_{\mathrm{empty}}$ 及全部更早层的 $K_1,\dots,K_{i-1}$，使单次与迭代剥离的输出均坍缩为单点极大独立集 $Q^{(i)}=\{a^*_{S_B}\}$，覆盖比不超过 $\frac{2\log_2 M+1}{M}\to 0$。$\square$

---

## 4　独立复核入口与实验范围

运行 [`node experiments/cl-peel-obstruction-verify.mjs`](../experiments/cl-peel-obstruction-verify.mjs)。程序使用 [check.mjs](../experiments/shared/check.mjs) 的 `isQuasiKernel(transpose(adj), K)` 对输出准核做独立定义核验，并对定向图显式验证无 2-圈。复核范围包括：
1. `G_stair(L=16, t=16)`（$n=272$）：确定性 `IterPeel(MaxOut)` 退化至 `0.1176`；
2. `AsymTrap`（$n=502, 1442, 4014$）：`Unif+MIS` 与 `1/(in+1)+MIS` 单调退化，动态 `WeightedDyn` 免疫（`>0.97`）；
3. `Portal(M=5, 8, 12)`（$n=130, 520, 1740$）：单次 `WeightedDyn+MIS` 退化至 `0.27 -> 0.11`；
4. `BackupTournamentPortal(M=5, 6, 7)`（$n=805, 1806, 3157$）：`IterPeel(WeightedDyn)+MIS` 全试验精确命中 `1/M`（`0.2001, 0.1667, 0.1429`）；
5. 纯竞赛图 `BackupPowerSetPortal(QR_7, QR_11, QR_19)`（$n=259..2071$，验证无 2-圈且全连通竞赛图）：`Single+MIS` 降至 `0.433 -> 0.3636 -> 0.307`，`IterPeel+MIS` 在 `QR_7, QR_11` 已跌破 `0.50` 至 `0.448, 0.424`。

**对后续路线的启示。** 在 `BackupTournamentPortal` 中任意 $b_j\in B$ 都是覆盖 $100\%$ 权重的准核，在 `BackupPowerSetPortal` 中 $T_M$ 的任意王都是覆盖 $\ge 50\%$ 权重的准核。攻打一般线性界 $W_c$ 必须跳出 CL 逆向否决框架，转向**非 CL 机制**（如先在 $\alpha(D)\le 2$ 上建立无 CL 回溯的线性界 $W_c$，再抽象为一般图的 2-步安全提交 / 极小极大框架）。
