# 禁出星图（出邻集独立数受限）与 $(\Delta^+, \alpha^+)$ 局部不等式相图

沿用[Clow 5.1 与一般有向图小准核证明](Clow-5.1-证明.md)的记号。设 $D$ 是非空有限无源简单有向图（无自环，除非特别声明均**允许双向边**）。对任意顶点子集 $W \subseteq V(D)$，令 $\alpha(D[W])$ 表示导出子图 $D[W]$ 的最大独立集大小（独立集内任意两点双向均无弧），并定义**出邻集独立数**
$$\alpha^+(D) := \max_{u \in V(D)} \alpha\bigl(D[N^+(u)]\bigr).$$
在无双向边的定向图上，$\alpha^+(D) \le d - 1$ 与 Clow（[arXiv:2601.11847](https://arxiv.org/html/2601.11847v1)）研究的**禁诱导有向出星 $\vec{K}_{1,d}$-free** 条件完全等价；且 $\alpha(D[N^+(u)]) \le k$ 对取导出子图严格遗传。Clow 原文对 $\vec{K}_{1,d}$-free 图给出的准核上界为 $\frac{d^2 - 2d + 2}{d^2 - d + 1}n$（$d=2,3,4$ 时分别为 $\frac{2}{3}n, \frac{5}{7}n, \frac{10}{13}n$）。

本笔记记录向无界出度 $\alpha^+(D) \le k$ 方向推进所得的**已证正面定理**、**通用归纳约简引理**、**完整负面边界反例（含与 Seymour 第二邻域猜想的精确归约）**以及**下一阶段交接路线**。

---

## 1　通用增强归纳准则与从属子点约简引理

在不加任何度数或 $\alpha^+$ 限制的一般简单有向图上，[Clow-5.1-证明](Clow-5.1-证明.md)中带预覆盖集 $P$（$R(H) \subseteq P$）的强归纳框架 $\mathcal{P}(H, P)$ 可在两处直接加强。

### 1.1　精确单步阈值 $g^+(v) \ge 1$

**命题 1.** 在无源图 $H$ 上执行单步删除 $U = \{v\} \cup S_H(v) \cup E_H(v)$ 时，归纳不等式 $2|Q| \le |V(H)|$ 成立的充分条件为
$$g^+(v) := |E_H(v)| - |S_H(v)| + \mathbf{1}[v \in N_H^+(S_H(v))] \ge 1.$$

*证明.* 记 $S = S_H(v), E = E_H(v)$，恒有 $S \cap E = \emptyset$。若 $v \in N_H^+(S)$，则 $v \in E$，$|U| = |S| + |E|$；取 $Q = S \cup Q'$ 已一步覆盖 $v$ 并两步覆盖 $N_H^+(v)$，且 $2|Q| \le 2|S| + |V(H)| - |U| = |V(H)| - g(v) \le |V(H)|$ 只需 $g(v) \ge 0$（即 $g^+(v) \ge 1$）。若 $v \notin N_H^+(S)$，则 $v \notin E$，$|U| = 1 + |S| + |E|$，按 $v \in N_H^+(Q')$ 与否同原证，只需 $g(v) \ge 1$（仍即 $g^+(v) \ge 1$）。$\square$

### 1.2　从属入度 1 子点约简引理（引理 A）

**引理 A（从属子点约简，任意简单有向图通用）.** 设 $H$ 是有限简单有向图（允许双向边），$R(H) \subseteq P \subseteq V(H)$。若存在 $y \in V(H)$ 满足 $d_H^+(y) \ge 1$，且符合以下任一条件：
* **（A0，纯双向入邻）** $N_H^-(y) \subseteq N_H^+(y)$；或
* **（A1，从属单父点）** $N_H^-(y) \setminus N_H^+[y] = \{u\}$，且 $N_H^+(y) \subseteq N_H^+[u]$；

则令 $H' = H - N_H^+[y]$，$P' = (P \cap V(H')) \cup R(H')$。由 $(H', P')$ 的任意合法小准核 $Q'$（满足 $2|Q'| \le |V(H')|$）可如下构造 $(H, P)$ 的合法小准核 $Q$：
* 若属（A1）且 $u \in Q'$，取 $Q = Q'$；
* 其余情形均取 $Q = \{y\} \cup Q'$。

*证明.* 因 $d_H^+(y) \ge 1$，有 $|N_H^+[y]| = 1 + d_H^+(y) \ge 2$。
* 当属（A1）且 $u \in Q'$ 时，必有 $u \in V(H')$（故 $y \not\to u$），从而 $N_H^+(y) \subseteq N_H^+(u)$，且 $u \to y$。于是 $\{y\} \cup N_H^+(y) \subseteq N_H^+(u) \subseteq N_H^+(Q')$；对任意 $z \in R(H') \setminus P$，因 $R(H) \subseteq P$，$z$ 在 $H$ 中必有前驱落在 $N_H^+[y] \subseteq N_H^+(u)$ 内，故 $z \in N_H^{++}(u)$。因此 $Q = Q'$ 独立、两步覆盖 $V(H) \setminus P$，且 $2|Q| = 2|Q'| \le |V(H')| \le |V(H)| - 2$。
* 其余情形下，$N_H^-(y) \cap V(H') = N_H^-(y) \setminus N_H^+[y]$ 与 $Q'$ 不交，且 $N_H^+(y) \cap V(H') = \emptyset$，故 $Q = \{y\} \cup Q'$ 独立；$y$ 零步覆盖自身、一步覆盖 $N_H^+(y)$、两步覆盖 $R(H') \setminus P$；且 $2|Q| = 2 + 2|Q'| \le 2 + |V(H)| - |N_H^+[y]| \le |V(H)|$。$\square$

---

## 2　无界出度下的正面定理

### 2.1　$\alpha^+(D) \le 1$（局部出半完全有向图 / $\vec{K}_{1,2}$-free 图）

**定理 1.** 设 $D$ 是任意有限非空无源简单有向图（允许双向边，出度任意无界），满足 $\alpha^+(D) \le 1$。则：
1. **全局独立集界**：$D$ 的**任意独立集 $I$**（特别地，**任意准核 $Q$**）均满足 $2|I| \le |V(D)|$。这在一般简单有向图上将 Clow 在 $d=2$ 时的 $\frac{2}{3}n$ 上界推进至精确界 $\frac{1}{2}n$。
2. **强局部不等式**：存在显式根 $r \in C$，使 $\{r\} \cup A_C(r)$ 内必有顶点 $v$ 满足 $L^*(v) \ge 1$（有汇点时任取连汇点的核心点 $r$ 即有 $L^*(r) \ge 1$；无汇点时取最小出度点 $r = \arg\min_{u \in V(D)} d^+(u)$）。

*证明.*
1. 设 $I \subseteq V(D)$ 独立，记 $B = V(D) \setminus I$。因 $D$ 无源且 $I$ 独立，每个 $x \in I$ 在 $B$ 中至少有一个入邻点；又对每个 $b \in B$，$N^+(b) \cap I$ 是 $D[N^+(b)]$ 的独立子集，故 $|N^+(b) \cap I| \le \alpha(D[N^+(b)]) \le 1$。求和得 $|I| \le \sum_{b \in B} |N^+(b) \cap I| \le |B| = |V(D)| - |I|$，即 $2|I| \le |V(D)|$。
2. 反设对所有 $v \in C$ 均有 $L^*(v) \le 0$，取极小基数最优集 $F(v) \subseteq S(v) \cap Z$。因 $S(v)$ 恒为独立集，对每个 $a \in A_C(v)$ 均有 $|N^+(a) \cap S(v)| \le \alpha(D[N^+(a)]) \le 1$；同理 $k(v) = |A_K(v)| \le 1$。
   * 若存在汇点，取 $r \in C$ 使 $k(r) = 1$，则 $|S(r)| \le \sum_{a \in A_C(r)} |N^+(a) \cap S(r)| \le |A_C(r)| = d^+(r) - 1$，得 $L^*(r) \ge 1$，矛盾。
   * 若全图无汇点，取最小出度点 $r \in V(D)$，令 $\delta = d^+(r) \ge 1$。由 $\delta \le |F(r)| \le |S(r)| \le \sum_{a \in A(r)} |N^+(a) \cap S(r)| \le \delta$ 知 $F(r) = S(r)$，$|X(r)| = 0$，每个 $a \in A(r)$ 恰有唯一子点 $s_a \in S(r)$ 且 $d_D^-(s_a) = 1$。对每个 $s_a \in S(r)$，由 $|X(r)| = 0$ 与 $d^+(s_a) \ge \delta = |A(r)|$ 得 $N^+(s_a) = A(r)$。任取 $a \in A(r)$：对任意 $w \in N^+(a) \setminus \{s_a\}$，因 $d_D^-(s_a) = 1$ 知 $w \not\to s_a$，由 $\alpha(D[N^+(a)]) \le 1$ 迫使 $s_a \to w$，故 $w \in N^+(s_a) = A(r)$。于是 $N^+(a) \subseteq \{s_a\} \cup (A(r) \setminus \{a\})$，特别地 $a \not\to r$（因 $r \notin A(r) \cup \{s_a\}$）。由单向父点排斥（事实 1）知 $S(a) \cap A(r) = \emptyset$。又 $N^+(s_a) = A(r)$，且对每个 $b \in N^+(a) \cap A(r)$ 同理有 $N^+(b) \subseteq S(r) \cup A(r)$（其中仅 $s_b \notin A(r)$），故 $S(a) \subseteq \{s_b : b \in N^+(a) \cap A(r)\}$，$|S(a)| \le |N^+(a) \cap A(r)| = d^+(a) - 1$，$L^*(a) \ge 1$，矛盾。$\blacksquare$

### 2.2　$\alpha^+(D) \le 2$（$\vec{K}_{1,3}$-free 图）的结构工具与 $M = 0$ 定理

设 $\alpha^+(D) \le 2$，反设对所有 $v \in C$ 有 $L^*(v) \le 0$，取极小最优子集 $F(v) \subseteq S(v) \cap Z$，记 $X(v) = N^+(F(v)) \setminus A(v)$，$F_1(v) = F(v) \cap I_1$（大小 $f_1(v)$），$F_{\ge 2}(v) = F(v) \setminus I_1$（大小 $f_{\ge 2}(v)$）。

**引理 1（$\alpha^+ \le 2$ 扇出界与 2-扇出刚性）.**
1. 对任意 $v \in C$ 与 $a \in A_C(v)$，有 $|N^+(a) \cap S(v)| \le 2$；对任意 $u \in V(D)$，因 $N^+(u) \cap I_1$ 独立，有 $c_1(u) = |N^+(u) \cap I_1| \le 2$，从而 $M = \max_{u \in C} c_1^0(u) \in \{0, 1, 2\}$。
2. 若 $a \in A_C(v)$ 满足 $N^+(a) \cap F(v) = \{s_1, s_2\}$（大小 2），则对任意 $w \in N^+(a) \setminus \{s_1, s_2\}$，因 $\{w, s_1, s_2\}$ 不能独立且 $s_1, s_2$ 互不相邻，必有 $w \to s_i$（此时 $w \in N_D^-(s_i) \subseteq A_C(v)$）或 $s_i \to w$（此时 $w \in N^+(F(v)) \subseteq A(v) \cup X(v)$）。故恒有
   $$N^+(a) \setminus \{s_1, s_2\} \subseteq A(v) \cup X(v),$$
   且当 $s_1, s_2 \not\to v$ 时必有 $a \not\to v$。

**引理 2（无度数主恒等式）.** 对任意满足 $L^*(v) \le 0$ 的 $v \in C$（不论 $d^+(v)$ 多大），双向统计 $A_C(v)$ 到 $F(v)$ 的弧数即得精确恒等式
$$f_1(v) = 2k(v) + 2|X(v)| + 2\bigl(|F(v)| - d^+(v) - |X(v)|\bigr) + \sum_{a \in A_C(v)} \bigl(2 - |N^+(a) \cap F(v)|\bigr) + \sum_{s \in F_{\ge 2}(v)} \bigl(d_D^-(s) - 2\bigr), \tag{$\star$}$$
其中右端每一项均非负。

*证明.* 因 $F(v) \subseteq S(v)$ 中每点的前驱全在 $A_C(v)$ 内，弧数 $e(A_C(v), F(v))$ 一方面等于
$$2|A_C(v)| - \sum_{a \in A_C(v)} \bigl(2 - |N^+(a) \cap F(v)|\bigr) = 2d^+(v) - 2k(v) - \sum_{a \in A_C(v)} \bigl(2 - |N^+(a) \cap F(v)|\bigr),$$
另一方面等于
$$\sum_{s \in F(v)} d_D^-(s) = 2|F(v)| - f_1(v) + \sum_{s \in F_{\ge 2}(v)} \bigl(d_D^-(s) - 2\bigr).$$
联立移项即得 $(\star)$；由 $L^*(v) \le 0$ 知 $|F(v)| - d^+(v) - |X(v)| \ge 0$，结合引理 1.1 知右端逐项非负。$\square$

**定理 2（无界出度 $\alpha^+(D) \le 2$ 的 $M = 0$ 定理）.** 设 $D$ 是有限非空无源简单有向图（允许双向边，出度无界），满足 $\alpha^+(D) \le 2$ 且 $I_1 \cap Z = \emptyset$（特别地，若每个顶点入度 $\delta^-(D) \ge 2$，或每个非汇点入度 $\ge 2$ 且无私有汇点）。则必存在显式根 $r \in C$ 使 $\{r\} \cup A_C(r)$ 内有顶点满足 $L^*(v) \ge 1$。

*证明.* 反设处处 $L^*(v) \le 0$。因 $I_1 \cap Z = \emptyset$，对所有 $v \in C$ 有 $f_1(v) = 0$，代入主恒等式 $(\star)$ 知右端逐项为零：全图无汇点（$k(v) = 0$）、$|X(v)| = 0$、$|F(v)| = d^+(v)$、对每个 $a \in A(v)$ 有 $|N^+(a) \cap F(v)| = 2$、对每个 $s \in F(v)$ 有 $d_D^-(s) = 2$。

取最小出度点 $r \in V(D)$，令 $\delta = d^+(r)$。因 $|F(r)| = \delta \ge 1$ 且 $F(r)$ 中点在 $A(r)$ 内有 2 个前驱，必有 $\delta \ge 2$。对每个 $s \in F(r)$，由 $|X(r)| = 0$ 与 $d^+(s) \ge \delta = |A(r)|$ 得 $N^+(s) = A(r)$（故 $s \not\to r$）。任取 $a_1 \in A(r)$，设 $N^+(a_1) \cap F(r) = \{s_1, s_2\}$，由引理 1.2 及 $X(r) = \emptyset, s_1, s_2 \not\to r$ 得 $a_1 \not\to r$ 且 $N^+(a_1) = \{s_1, s_2\} \sqcup (N^+(a_1) \cap A(r))$。同理每个 $a_j \in N^+(a_1) \cap A(r)$ 也满足 $N^+(a_j) \subseteq F(r) \cup A(r)$。由事实 1 知 $S(a_1) \cap A(r) = \emptyset$，结合 $N^+(\{s_1, s_2\}) = A(r)$ 得 $S(a_1) \subseteq F(r) \setminus \{s_1, s_2\}$。每个 $s \in S(a_1)$ 满足 $d_D^-(s) = 2$ 且 $a_1 \not\to s$，故其两个前驱均落在 $N^+(a_1) \cap A(r)$ 中；而每个 $a_j \in N^+(a_1) \cap A(r)$ 至多向 $F(r)$ 送 2 条弧，故 $2|S(a_1)| \le 2|N^+(a_1) \cap A(r)| \implies |S(a_1)| \le |N^+(a_1) \cap A(r)| = d^+(a_1) - 2$，得 $L^*(a_1) \ge 2$，矛盾。$\blacksquare$

---

## 分节阅读

- [§3–4　局部判据反例、SSNC 归约与交接](Clow-禁出星图-负面边界.md)
