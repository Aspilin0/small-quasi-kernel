# Clow 猜想 5.1 与最大出度 3 一般有向图的小准核定理

沿用[前几轮笔记](Clow-5.1-覆盖的相容性.md)的记号，并**放开无双向边的限制**：设 $D$ 是非空有限无源简单有向图，无自环、无重弧，**允许双向边（2-环）**，最大出度 $\Delta^+(D) \le 3$。记非汇点集（核心）为 $C = \{v \in V(D) : d^+(v) \ge 1\}$，汇点集为 $K = V(D) \setminus C$。因 $D$ 非空且无源，$C$ 必非空。对每个 $v \in C$，记 $A(v) = N^+(v)$，$A_C(v) = A(v) \cap C$，$c(v) = |A_C(v)|$，$k(v) = |A(v) \cap K|$；记 $S(v)$ 为 $D - N^+[v]$ 的源点集，$E(v) = A(v) \cup N^+(S(v))$，$g(v) = |E(v)| - |S(v)|$。

在[覆盖的相容性](Clow-5.1-覆盖的相容性.md)中，令 $M(v) = \{s \in S(v) : d^-(s) = 1\}$，已证定向底图上 $v$ 在所有有限覆盖上的最小差值为
$$L(v) = \min_{M(v) \subseteq F \subseteq S(v)} \bigl(|A(v) \cup N^+(F)| - |F|\bigr).$$
本文进一步定义无约束的下界
$$L^*(v) = \min_{F \subseteq S(v)} \bigl(|A(v) \cup N^+(F)| - |F|\bigr).$$
显然对每个 $v \in C$ 均有 $L^*(v) \le L(v) \le g(v)$。

---

## 主要结果

**定理 1（一般有向图上的强 Clow 5.1）.** 对任意非空有限无源简单有向图 $D$（无自环，允许双向边，$\Delta^+(D) \le 3$），必存在 $v \in C$ 使 $L^*(v) \ge 1$。更具体地，存在由局部结构显式选出的根 $r \in C$，使得从 $r$ 出发沿核心弧至多 2 步可达的顶点集（定向图情形下仅需至多 1 步，即 $\{r\} \cup A_C(r)$）中至少有一点满足 $L^*(v) \ge 1$。

**直接推论.**
1. **Clow 猜想 5.1 成立（且推广至允许双向边）**：任意非空有限无源、$\Delta^+(D) \le 3$ 的有向图均存在 $v$ 使 $|N^+(v) \cup N^+(S(v))| \ge |S(v)| + 1$。
2. **覆盖底图问题的彻底否定回答**：不存在每个顶点都满足 $L(v) \le 0$ 的有限定向底图。对任意合格底图 $D$，均存在顶点 $v$ 在 $D$ 的全部有限覆盖中始终为见证点（$g(v') \ge L(v) \ge L^*(v) \ge 1$）。这直接解释了[六点覆盖搜索](Clow-5.1-覆盖的相容性.md)与[七点私有汇点搜索](clow-private-search.mjs)结果全为零的现象。
3. **超图与终端强连通分量保持性**：在 $D$ 外部添加任意顶点和只指向 $D$ 的弧，不改变 $D$ 内部各点的出邻集，则超图中对同一顶点 $v$ 有 $S_{\text{超}}(v) \subseteq S_D(v)$，故仍有 $g_{\text{超}}(v) \ge L^*_D(v) \ge 1$。

**定理 2（最大出度至多 3 的一般有向图满足小准核猜想）.** 任意有限无源简单有向图 $D$（无自环，允许双向边，$\Delta^+(D) \le 3$）都含有一个独立集 $Q$，使 $2|Q| \le |V(D)|$ 且 $D$ 中每个顶点都能从 $Q$ 沿至多两条弧到达，且 $Q$ 可在多项式时间内构造。等价地（反转全部弧方向，回到 [弧细分笔记](细分一条弧.md) 的约定），任意有限无汇、最大入度至多 3 的简单有向图存在大小至多 $|V(D)|/2$ 的准核。这在允许双向边的一般有向图上将 Clow 的 $\frac{4n}{7}$ 上界推进至 Erdős–Székely 猜想的精确上界 $\frac{n}{2}$。

---

## 定理 1 的证明

反证。假设对所有 $v \in C$ 均有 $L^*(v) \le 0$。

### 四个基础工具

**事实 1（单向父点排斥）.** 对任意 $v \in C$ 与 $a \in A_C(v)$，若 $a \not\to v$，则 $v \notin N^+[a]$，从而 $S(a) \cap A(v) = \emptyset$。

*证明.* 无自环故 $v \neq a$，结合 $a \not\to v$ 得 $v \notin N^+[a]$。于是每个 $b \in A(v) \setminus \{a\}$ 在 $D - N^+[a]$ 中仍保留入弧 $v \to b$，不在 $S(a)$ 中；而 $a \in N^+[a]$ 也不在 $S(a)$ 中。$\square$

**事实 2（汇点约简，双向边下仍成立）.** 每个 $v \in C$ 必满足 $c(v) \ge 1$ 与 $k(v) \le 1$。

*证明.* 若 $c(v) = 0$，则 $S(v) = \emptyset$，$L^*(v) = |A(v)| \ge 1$，矛盾。若 $k(v) \ge 2$，结合 $c(v) \ge 1$ 与 $\Delta^+(D) \le 3$ 得 $A(v) = \{z_1, z_2, w\}$（$z_1, z_2 \in K, w \in C$）。任何 $s \in S(v)$ 不能由 $v, z_1, z_2$ 指向，故 $S(v) \subseteq A(w)$，$|S(v)| \le d^+(w) \le 3 = |A(v)|$。由 $L^*(v) \le 0$ 得 $|F(v)| = |S(v)| = 3$，$S(v) = A(w)$，且 $N^+(A(w)) \subseteq A(v) = \{z_1, z_2, w\}$。考察 $w$：删去 $N^+[w] = \{w\} \cup A(w)$ 时 $w$ 自身已删去，故 $S(w) \subseteq N^+(A(w)) \setminus N^+[w] \subseteq \{z_1, z_2\}$，从而 $L^*(w) \ge |A(w)| - |S(w)| \ge 3 - 2 = 1$，矛盾。$\square$

记全图入度为 1 的顶点集（同时包含入度为 1 的核心点与私有汇点）为 $I_1 = \{x \in V(D) : d^-(x) = 1\}$。令 $c_1(u) = |A(u) \cap I_1|$，$Z = \{u \in V(D) : c_1(u) = 0\}$，$c_1^0(u) = |A(u) \cap (I_1 \cap Z)|$。注意 $K \subseteq Z$，故所有私有汇点均在 $I_1 \cap Z$ 中；且任何 $u \in Z$ 满足 $c_1^0(u) = 0$。

**引理 1（入度 1 子点剪枝）.** 对每个 $v \in C$，取在所有使 $|A(v) \cup N^+(F)| - |F| = L^*(v)$ 的子集 $F \subseteq S(v)$ 中基数 $|F|$ 最小的一个，记为 $F(v)$。则必有 $F(v) \subseteq S(v) \cap Z$。

*证明.* 若存在 $s \in F(v) \setminus Z$，取 $y \in A(s) \cap I_1$。因 $d^-(y) = 1$ 且 $s \in S(v) \implies s \neq v$，有 $y \notin A(v)$ 且 $y \notin N^+(F(v) \setminus \{s\})$。从 $F(v)$ 中删去 $s$ 使 $|A(v) \cup N^+(F)|$ 至少减 1 而 $|F|$ 恰减 1，矛盾于 $|F(v)|$ 极小。$\square$

记 $T(v) = F(v) \cap C$，$H(v) = F(v) \cap K$，$X(v) = N^+(T(v)) \setminus A(v)$，$f_1(v) = |F(v) \cap I_1|$，$f_{\ge 2}(v) = |F(v) \setminus I_1|$，$b(v) = |\{a \in A_C(v) : a \to v\}|$。由 $L^*(v) \le 0$ 与引理 1 得
$$|F(v)| = |T(v)| + |H(v)| = f_1(v) + f_{\ge 2}(v) \ge |A(v)| + |X(v)|, \qquad f_1(v) \le \sum_{a \in A_C(v)} c_1^0(a).$$
记 $M = \max_{u \in C} c_1^0(u) \in \{0, 1, 2, 3\}$。

**引理 2（3-出正则零外溢双生排除）.** 若 $D$ 是 3-出正则图（$K = \emptyset$），且存在 $v \in V(D)$ 满足 $|X(v)| = 0$ 并对每个 $a \in A(v)$ 也有 $|X(a)| = 0$，则矛盾。

*证明.* 由 $|X(v)| = 0$ 知 $N^+(T(v)) \subseteq A(v)$（大小 3），且 $|T(v)| \ge 3$。任取 $t \in T(v) \subseteq S(v)$ 及 $a \in N^-(t) \subseteq A(v)$（图无源，故存在），即 $t \in A(a)$。对 $a$ 同样由 $|X(a)| = 0$ 知每个 $a' \in T(a)$ 满足 $A(a') \subseteq A(a)$，又 $d^+(a') = 3 = |A(a)|$，故 $A(a') = A(a) \ni t$，即 $a' \to t$。因为 $t \in S(v)$ 的全部前驱都在 $A(v)$ 中，于是 $\{a\} \cup T(a) \subseteq N^-(t) \subseteq A(v)$。但 $a \notin T(a)$ 且 $|T(a)| \ge |A(a)| = 3$，得 $4 \le 1 + |T(a)| \le |A(v)| = 3$，矛盾。$\square$

**引理 3（$M = 1$ 虚汇点引理）.** 设 $M = 1$。若存在 $a \in C$ 及其出邻点 $t \in A(a)$ 使 $N^+(t) \cap S(a) = \emptyset$（例如 $t$ 为汇点，或 $N^+(t) \subseteq \{a\}$，或 $a \in A(v), a \not\to v$ 且 $N^+(t) \subseteq A(v)$），则矛盾（具体地，$\{a\} \cup A_C(a)$ 中必有 $L^* \ge 1$ 的点）。

*证明.* 若 $d^+(a) = 1$，则 $A(a) = \{t\}$，$S(a) = \emptyset$，矛盾。若 $d^+(a) = 2$（$A(a) = \{t, r_1\}$），则每个 $y \in S(a)$ 仅有前驱 $r_1$，故 $F(a) \subseteq A(r_1) \cap (I_1 \cap Z)$，$|F(a)| \le c_1^0(r_1) \le 1 < 2$（若 $r_1 \in K$ 则为 0），矛盾。

下设 $d^+(a) = 3$，$A(a) = \{t, r_1, r_2\}$。每个 $y \in S(a)$ 的前驱全在 $\{r_1, r_2\}$ 中；若 $r_1$ 或 $r_2$ 为汇点，同理得 $|F(a)| \le 1 < 3$ 矛盾，故 $r_1, r_2 \in C$。记 $F_1 = F(a) \cap I_1, F_2 = F(a) \setminus I_1$（基数 $f_1, f_2$），$b = \mathbf{1}[r_1 \to a] + \mathbf{1}[r_2 \to a]$。则 $f_1 \le c_1^0(r_1) + c_1^0(r_2) \le 2$，$f_1 + 2f_2 + b \le 6$，且 $f_1 + f_2 \ge 3 + |X(a)|$。
* $f_2 = 0$：$|F(a)| = f_1 \le 2 < 3$，矛盾。
* $f_2 = 3$：迫使 $f_1 = 0, b = 0, |X(a)| = 0$ 且 $A(r_1) = F(a)$（大小 3）。由 $r_1 \not\to a$ 与事实 1 得 $S(r_1) \subseteq X(a) = \emptyset$，矛盾。
* $f_2 = 2$：
  * 若 $f_1 = 2$，则 $b = 0, |X(a)| \le 1$，$d^+(r_1) = 3$ 且 $A(r_1) \subseteq F(a)$。由事实 1 得 $S(r_1) \subseteq X(a)$（大小至多 1），$L^*(r_1) \ge 2$，矛盾。
  * 若 $f_1 = 1$，则 $|X(a)| = 0$。不妨 $r_1$ 是 $F_1$ 唯一元素的父点，则 $A(r_1) = F(a)$（大小 3），从而 $r_1 \not\to a$；由事实 1 得 $S(r_1) \subseteq X(a) = \emptyset$，$L^*(r_1) = 3$，矛盾。
* $f_2 = 1$：迫使 $f_1 = 2, |F(a)| = 3, |X(a)| = 0$。记 $F_2 = \{p\}$，$F_1 = \{s_1, s_2\}$，因 $c_1^0(r_i) \le 1$ 必分别由 $r_1, r_2$ 独指（$r_1 \to s_1, r_2 \to s_2$）。
  * 若 $r_1 \not\to a$：由事实 1，$S(r_1) \cap A(a) = \emptyset$，又 $|X(a)| = 0$ 故 $N^+(\{p, s_1\}) \subseteq A(a)$ 不射入 $S(r_1)$。于是 $d^+(r_1) = 2$ 时 $S(r_1) = \emptyset$；$d^+(r_1) = 3$（$A(r_1) = \{p, s_1, q_1\}$）时 $F(r_1) \subseteq A(q_1) \cap (I_1 \cap Z)$ 致 $|F(r_1)| \le 1 < 3$，均矛盾。
  * 若 $r_1 \to a$：则 $A(r_1) = \{p, s_1, a\}$（大小 3）。由 $|X(a)| = 0$ 得 $N^+(A(r_1)) \subseteq A(a) = \{t, r_1, r_2\}$。删去 $N^+[r_1]$ 时 $r_1$ 已删，故 $S(r_1) \subseteq \{t, r_2\}$（大小至多 2），得 $L^*(r_1) \ge 3 - 2 = 1$，矛盾。$\square$

下面按 $M \in \{0, 3, 2, 1\}$ 逐一推出矛盾。

---

### 情形 $M = 0$

此时 $I_1 \cap Z = \emptyset$，对每个 $v \in C$ 均有 $f_1(v) = 0$，即 $F(v)$ 中每一点在 $A_C(v)$ 内至少有两个前驱。

* **有汇点（$K \neq \emptyset$）**：取 $w \in C$ 使 $k(w) = 1$。若 $c(w) = 1$，则 $|A_C(w)| = 1 \implies F(w) = \emptyset$，矛盾。若 $c(w) = 2$（$A_C(w) = \{a_1, a_2\}$），则 $2|F(w)| + b(w) \le 6$ 且 $|F(w)| \ge 3 + |X(w)|$，迫使 $|F(w)| = 3, |X(w)| = 0, b(w) = 0$ 且 $A(a_1) = F(w)$（大小 3）。由 $a_1 \not\to w$ 与事实 1 得 $S(a_1) \subseteq X(w) = \emptyset$，$L^*(a_1) = 3$，矛盾。
* **无汇点（$K = \emptyset$）**：
  * 若存在 $d^+(v) = 1$，则 $|A(v)| = 1 \implies F(v) = \emptyset$，矛盾。故全图 $d^+(v) \in \{2, 3\}$。
  * 若存在 $d^+(v) = 2$（$A(v) = \{a_1, a_2\}$），计数得 $4 + 2|X(v)| + b(v) \le 2|F(v)| + b(v) \le d^+(a_1) + d^+(a_2) \le 6$。
    * 若 $|X(v)| = 1$，迫使 $b(v) = 0, |F(v)| = 3, d^+(a_1) = 3, A(a_1) = F(v)$，由事实 1 得 $S(a_1) \subseteq X(v)$（大小 1），$L^*(a_1) \ge 2$，矛盾。
    * 若 $|X(v)| = 0$，因 $\delta^+(D) \ge 2$，所有 $t \in F(v)$ 满足 $A(t) = \{a_1, a_2\}$。若 $b(v) \le 1$，不妨 $a_1 \not\to v$，由事实 1 得 $S(a_1) \cap \{a_1, a_2\} = \emptyset$，故 $F(v)$ 不射入 $S(a_1)$；又 $|A(a_1) \setminus F(v)| \le 3 - 2 = 1$，故无点在 $A(a_1)$ 中有两个前驱，结合 $M = 0$ 得 $F(a_1) = \emptyset$，矛盾。若 $b(v) = 2$，迫使 $d^+(a_1) = 3, |F(v)| = 2, A(a_1) = F(v) \cup \{v\}$，于是 $N^+(A(a_1)) = \{a_1, a_2\}$，删去 $a_1$ 得 $S(a_1) \subseteq \{a_2\}$（大小至多 1），$L^*(a_1) \ge 2$，矛盾。
  * 故全图为 3-出正则。对任意 $u \in V(D)$，$6 + 2|X(u)| + b(u) \le 2|F(u)| + b(u) \le 9 \implies |X(u)| \in \{0, 1\}$。若某 $u$ 有 $|X(u)| = 1$，则 $|F(u)| = 4, 2|F(u)| = 8$，必存在 $a_1 \in A(u)$ 满足 $d^+(a_1) = 3$ 且 $A(a_1) \subseteq F(u)$（从而 $a_1 \not\to u$），由事实 1 得 $S(a_1) \subseteq X(u)$（大小 1），$L^*(a_1) \ge 2$，矛盾。故所有 $u$ 均有 $|X(u)| = 0$，矛盾于引理 2。

---

### 情形 $M = 3$

取 $u^* \in C$ 使 $c_1^0(u^*) = 3$。则 $A(u^*) \subseteq I_1 \cap Z \subseteq Z$，故 $f_1(u^*) = 0$。

* 若 $k(u^*) = 1$，同情形 $M = 0$ 的 $K \neq \emptyset, c(w) = 2$ 子情形，矛盾。
* 若 $k(u^*) = 0$，记 $A(u^*) = \{a_1, a_2, a_3\} \subseteq I_1 \cap Z$。则 $2|F(u^*)| + b(u^*) \le 9 \implies |F(u^*)| \le 4$，且 $2|H(u^*)| \le 3 \implies |H(u^*)| \le 1$，从而 $|T(u^*)| \ge 2$。对任一 $t \in T(u^*)$，因 $a_1, a_2, a_3 \in I_1$ 的唯一前驱是 $u^* \neq t$，有 $N^+(t) \cap A(u^*) = \emptyset$，故 $|X(u^*)| \ge 1$。联立得 $|F(u^*)| = 4, |X(u^*)| = 1$，且 $2|F(u^*)| = 8$ 迫使某 $a_1 \in A(u^*)$ 满足 $d^+(a_1) = 3$ 及 $A(a_1) \subseteq F(u^*)$（从而 $a_1 \not\to u^*$）。由事实 1 得 $S(a_1) \subseteq X(u^*)$（大小 1），$L^*(a_1) \ge 2$，矛盾。

---

### 情形 $M = 2$

取 $u^* \in C$ 使 $c_1^0(u^*) = 2$，则 $d^+(u^*) \in \{2, 3\}$。

* **子情形 2.1：$d^+(u^*) = 2$**。$A(u^*) \subseteq I_1 \cap Z \implies f_1(u^*) = 0$。若 $k(u^*) = 1$ 则 $F(u^*) = \emptyset$ 矛盾。若 $k(u^*) = 0$，记 $A(u^*) = \{a_1, a_2\} \subseteq I_1 \cap Z$，则 $2|F(u^*)| + b(u^*) \le 6 \implies |F(u^*)| \le 3$，$|H(u^*)| \le 1 \implies T(u^*) \neq \emptyset$。因 $a_1, a_2 \in I_1$ 唯一前驱为 $u^* \neq t$，有 $|X(u^*)| \ge 1$，迫使 $|F(u^*)| = 3, |X(u^*)| = 1, b(u^*) = 0, A(a_1) = F(u^*)$；由事实 1 得 $S(a_1) \subseteq X(u^*)$（大小 1），$L^*(a_1) \ge 2$，矛盾。
* **子情形 2.2：$d^+(u^*) = 3$ 且 $k(u^*) = 1$**。记 $u^*$ 的汇点为 $z^*$。若 $z^* \notin I_1$，则两核心后继都在 $I_1 \cap Z$ 中，$f_1(u^*) = 0$，同情形 $M = 0$ 的 $K \neq \emptyset$ 矛盾。若 $z^* \in I_1$，记 $A(u^*) = \{a_1, a_3, z^*\}$，其中 $a_1 \in I_1 \cap Z$（$c_1^0(a_1) = 0$），则每个 $x \in F(u^*)$ 均由 $a_3$ 指向，故 $F(u^*) \subseteq A(a_3)$（大小至多 3）。于是 $|F(u^*)| = 3$、$A(a_3) = F(u^*)$（故 $a_3 \not\to u^*$）且 $|X(u^*)| = 0$；由事实 1 得 $S(a_3) \subseteq X(u^*) = \emptyset$，$L^*(a_3) = 3$，矛盾。
* **子情形 2.3：$d^+(u^*) = 3$ 且 $k(u^*) = 0$**。记 $A(u^*) = \{a_1, a_2, a_3\}$，其中 $a_1, a_2 \in I_1 \cap Z$（$c_1^0(a_1) = c_1^0(a_2) = 0$）。分划 $F(u^*) = P \sqcup Q$，其中 $P = \{x \in F(u^*) : N^-(x) = \{a_1, a_2\}\}$，$Q = \{x \in F(u^*) : a_3 \to x\}$；记 $p = |P|$，$q_1 = |Q \cap I_1| \le c_1^0(a_3) \le 2$，$q_2 = |Q \setminus I_1|$，$b_i = \mathbf{1}[a_i \to u^*]$。有 $q_1 + q_2 + b_3 \le 3$，$2p + q_2 + b_1 + b_2 \le 6$，$p + q_1 + q_2 \ge 3 + |X(u^*)|$。
  * **$p = 0$**：迫使 $|Q| = 3, b_3 = 0, |X(u^*)| = 0, A(a_3) = Q$；由事实 1 得 $S(a_3) = \emptyset$，$L^*(a_3) = 3$，矛盾。
  * **$p = 1$**：$|Q| \in \{2, 3\}$，$|X(u^*)| \le 1$。若 $|Q| = 3$，则 $b_3 = 0, A(a_3) = Q$，由事实 1 得 $S(a_3) \subseteq X(u^*)$（大小至多 1），$L^*(a_3) \ge 2$，矛盾。若 $|Q| = 2$，则 $|F(u^*)| = 3, |X(u^*)| = 0$；因 $a_1, a_2 \in I_1$ 仅有前驱 $u^*$，每个 $t \in Q \cap C$ 满足 $N^+(t) = \{a_3\}$，故 $N^+(Q) \subseteq \{a_3\}$。若 $b_3 = 0$，由事实 1 知 $Q$ 不射入 $S(a_3)$，故 $d^+(a_3) = 2$ 时 $S(a_3) = \emptyset$，$d^+(a_3) = 3$（$A(a_3) = Q \cup \{r_3\}$）时 $F(a_3) \subseteq A(r_3) \cap (I_1 \cap Z)$ 致 $|F(a_3)| \le 2 < 3$；若 $b_3 = 1$，则 $A(a_3) = Q \cup \{u^*\}$（大小 3），$N^+(A(a_3)) \subseteq \{a_1, a_2, a_3\}$，删去 $a_3$ 得 $S(a_3) \subseteq \{a_1, a_2\}$（大小至多 2），$L^*(a_3) \ge 1$，均矛盾。
  * **$p = 3$**：迫使 $q_2 = b_1 = b_2 = 0$，$|X(u^*)| \le 2$，$A(a_1) = P$（大小 3）；由事实 1 得 $S(a_1) \subseteq X(u^*)$（大小至多 2），$L^*(a_1) \ge 1$，矛盾。
  * **$p = 2$**：此时 $|F(u^*)| \le 5 \implies |X(u^*)| \le 2$。
    1. 若 $q_2 \ge 1$，取 $y \in Q \setminus I_1$，它必有前驱在 $\{a_1, a_2\}$ 中（不妨 $a_1 \to y$），则 $A(a_1) = P \cup \{y\} \subseteq F(u^*)$（大小 3）且 $b_1 = 0$；由事实 1 得 $S(a_1) \subseteq X(u^*)$（大小至多 2），$L^*(a_1) \ge 1$，矛盾。
    2. 故 $q_2 = 0$，从而 $|F(u^*)| = 2 + q_1 \le 4 \implies |X(u^*)| \le 1$。若 $b_1 = b_2 = 1$，则 $A(a_1) = P \cup \{u^*\}$（大小 3），删去 $a_1$ 得 $S(a_1) \subseteq \{a_2, a_3\} \cup X(u^*)$（大小至多 3）。由 $L^*(a_1) \le 0$ 迫使 $|X(u^*)| = 1$（从而 $q_1 = 2, |Q| = 2$）、$F(a_1) = \{a_2, a_3, x\}$ 且 $N^+(a_3) \subseteq P \cup \{u^*\}$，但 $Q \subseteq N^+(a_3)$ 与 $P \cup \{u^*\}$ 不交且 $|Q| = 2$，矛盾。
    3. 故至少一者为 0（不妨 $b_1 = 0$），事实 1 对 $a_1$ 成立。若 $d^+(a_1) = 2$，则 $A(a_1) = P \implies S(a_1) \subseteq X(u^*)$（大小至多 1），$L^*(a_1) \ge 1$，矛盾。若 $d^+(a_1) = 3$（$A(a_1) = P \cup \{r_1\}$），由事实 1 得 $F(a_1) \setminus X(u^*) \subseteq A(r_1) \cap (I_1 \cap Z)$（大小至多 2）。联立 $|A(a_1)| = 3$ 与 $|X(u^*)| \le 1$ 迫使 $|X(u^*)| = 1$、$|F(a_1)| = 3$、$F(a_1) \setminus X(u^*) = \{w_1, w_2\} \subseteq A(r_1)$ 且 $N^+(w_1), N^+(w_2) \subseteq P \cup \{r_1\}$。由事实 1，$w_i \in S(a_1)$ 不在 $A(u^*) \supseteq \{a_1, a_2\} = N^-(P)$ 中，故 $N^+(w_1), N^+(w_2) \subseteq \{r_1\}$。现考察 $r_1$（必非汇点）：$w_1, w_2 \in A(r_1)$ 的出边全指向已删的 $r_1$，不向 $S(r_1)$ 射出任何弧。故 $d^+(r_1) = 2$ 时 $S(r_1) = \emptyset$（$L^*(r_1) = 2$），$d^+(r_1) = 3$（$A(r_1) = \{w_1, w_2, z_0\}$）时 $F(r_1) \subseteq A(z_0) \cap (I_1 \cap Z)$（大小至多 2，$L^*(r_1) \ge 1$），均矛盾。

---

### 情形 $M = 1$

此时对所有 $u \in C$ 均有 $c_1^0(u) \le 1$。

1. **无汇点（$K = \emptyset$）**：若存在汇点，取指向它的核心点 $w$ 及该汇点 $z_w \in A(w)$，因 $N^+(z_w) = \emptyset$，直接矛盾于引理 3。
2. **最小出度至少 2（$\delta^+(D) \ge 2$）**：若某点 $v$ 满足 $d^+(v) = 1$（$A(v) = \{a\}$），则 $F(v) \subseteq A(a) \cap (I_1 \cap Z)$ 大小至多 1，迫使 $|F(v)| = 1$（记 $F(v) = \{t\}$）且 $|X(v)| = 0$。于是 $N^+(t) \subseteq \{a\} \subseteq N^+[a]$，即 $N^+(t) \cap S(a) = \emptyset$，对 $a$ 应用引理 3 即矛盾。
3. **满子集障碍**：对任意 $v \in V(D)$ 与 $a_1 \in A(v)$，断言 $A(a_1) \not\subseteq T(v)$。反设 $A(a_1) \subseteq T(v)$：因 $v \notin T(v)$，有 $a_1 \not\to v$，故事实 1 得 $S(a_1) \subseteq X(v)$；又 $A(a_1) \subseteq T(v) \subseteq S(v)$ 的全部前驱在 $A(v)$ 中，与 $X(v)$ 不交，故对每个 $w \in S(a_1)$ 有 $N^+(w) \cap A(a_1) = \emptyset$。结合 $\delta^+(D) \ge 2$ 得 $|X(v)| \ge |S(a_1)| \ge d^+(a_1) + 2$。
   * 若 $d^+(v) = 2$，则 $d^+(a_1) + 4 \le 2 + |X(v)| \le |T(v)| \le d^+(a_1) + d^+(a_2) \le d^+(a_1) + 3$，矛盾。
   * 若 $d^+(v) = 3$（$A(v) = \{a_1, a_2, a_3\}$），则 $d^+(a_1) + 5 \le |T(v)| \le d^+(a_1) + 6$ 且 $|X(v)| \le d^+(a_1) + 3$。统计出弧盈余：
     $$\sum_{i=1}^3 |A(a_i) \setminus T(v)| + \Bigl(\sum_{i=1}^3 |A(a_i) \cap T(v)| - |T(v)|\Bigr) + (3 - d^+(a_2)) + (3 - d^+(a_3)) \le 1.$$
     无论漏出 $T(v)$ 的弧数为 1（此时重叠数为 0，且 $a_2, a_3$ 中必有一者全入 $T(v)$）还是 0（此时三者全入 $T(v)$ 且重叠数至多 1），均存在 $j \in \{2, 3\}$ 使 $A(a_j) \subseteq T(v)$ 且 $A(a_1) \cap A(a_j) = \emptyset$。同理 $a_j \not\to v$ 且 $S(a_j) \subseteq X(v)$，又 $S(a_1) \cap S(a_j) = \emptyset$，故 $|X(v)| \ge (d^+(a_1) + 2) + (d^+(a_j) + 2) \ge d^+(a_1) + 6 > d^+(a_1) + 3$，矛盾。
4. **排除出度 2**：反设 $d^+(v) = 2$（$A(v) = \{a_1, a_2\}$）。记 $t_j = |\{t \in T(v) : d^-(t) = j\}|$。由步骤 3，$t_1 + 2t_2 \le (d^+(a_1) - 1) + (d^+(a_2) - 1) \le 4$，且 $t_1 \le 2M = 2$，$t_1 + t_2 \ge 2 + |X(v)|$。穷举全部整数解：
   * $(t_1, t_2) = (2, 0)$：$|T(v)| = 2, |X(v)| = 0$，记 $T(v) = \{s_1, s_2\}$（$a_1 \to s_1, a_2 \to s_2$），则 $N^+(s_1) = N^+(s_2) = \{a_1, a_2\}$。若 $a_1 \not\to v$，由事实 1 得 $N^+(s_1) \cap S(a_1) = \emptyset$，对 $a_1$ 应用引理 3 即矛盾。若 $a_1 \to v$，则 $\{s_1, v\} \subseteq A(a_1)$ 且两者出邻集均为 $\{a_1, a_2\}$：$d^+(a_1) = 2$ 时 $S(a_1) \subseteq \{a_2\}$（$L^*(a_1) \ge 1$）；$d^+(a_1) = 3$（$A(a_1) = \{s_1, v, r_1\}$）时 $F(a_1) \setminus \{a_2\} \subseteq A(r_1) \cap (I_1 \cap Z)$（大小至多 1），得 $|F(a_1)| \le 2 < 3$（$L^*(a_1) \ge 1$），矛盾。
   * $(t_1, t_2) \in \{(1, 1), (0, 2)\}$：$|T(v)| = 2, |X(v)| = 0$，$N^+(T(v)) = \{a_1, a_2\}$，且不妨 $T(v) \subseteq A(a_1)$。若 $a_1 \not\to v$，由事实 1 知 $T(v)$ 不射入 $S(a_1)$，故 $d^+(a_1) = 2$ 时 $S(a_1) = \emptyset$，$d^+(a_1) = 3$（$A(a_1) = T(v) \cup \{r_1\}$）时 $F(a_1) \subseteq A(r_1) \cap (I_1 \cap Z)$（大小至多 1 $< 3$）；若 $a_1 \to v$，则 $A(a_1) = T(v) \cup \{v\}$（大小 3），$N^+(A(a_1)) = \{a_1, a_2\}$，删去 $a_1$ 得 $S(a_1) \subseteq \{a_2\}$（大小至多 1 $< 3$），均矛盾。
   * $(t_1, t_2) = (2, 1)$：$t_1 + 2t_2 = 4$，$|T(v)| = 3$，$|X(v)| \le 1$，迫使 $d^+(a_1) = 3$ 且 $A(a_1) = \{s_1, p, r_1\}$（$s_1, p \in T(v)$）。若 $r_1 \neq v$（即 $a_1 \not\to v$），由事实 1 知 $N^+(\{s_1, p\}) \cap S(a_1) \subseteq X(v)$（大小至多 1），且 $F(a_1) \setminus X(v) \subseteq A(r_1) \cap (I_1 \cap Z)$（大小至多 1），故 $|F(a_1)| \le 2 < 3$；若 $r_1 = v$，则 $A(a_1) = \{s_1, p, v\}$，$N^+(A(a_1)) \subseteq \{a_1, a_2\} \cup X(v)$，删去 $a_1$ 得 $S(a_1) \subseteq \{a_2\} \cup X(v)$（大小至多 2 $< 3$），均矛盾。
5. **3-出正则收尾**：故全图为 3-出正则。对任意 $u \in V(D)$，由步骤 3 得 $t_1 + 2t_2 + 3t_3 \le 6$，且 $t_1 \le 3M = 3$，$t_1 + t_2 + t_3 \ge 3 + |X(u)|$。
   * 若 $|X(u)| \ge 2$，则 $t_1 + t_2 + t_3 \ge 5$，与 $t_1 + 2t_2 + 3t_3 \le 6$ 相减得 $t_2 + 2t_3 \le 1$，从而 $t_1 \ge 4 > 3$，矛盾。
   * 若 $|X(u)| = 1$，则 $t_1 + t_2 + t_3 \ge 4$；因 $t_1 \le 3$ 故 $t_2 + t_3 \ge 1$，从而 $t_1 + 2t_2 + 3t_3 \ge 5$。每个 $a \in A(u)$ 至多送 2 条弧进 $T(u)$，故必有 $a_1 \in A(u)$ 恰送 2 条弧进 $T(u)$，记 $A(a_1) = \{y_1, y_2, r_1\}$（$y_1, y_2 \in T(u)$）。若 $r_1 \neq u$（$a_1 \not\to u$），由事实 1 得 $N^+(\{y_1, y_2\}) \cap S(a_1) \subseteq X(u)$（大小 1），且 $F(a_1) \setminus X(u) \subseteq A(r_1) \cap (I_1 \cap Z)$（大小至多 1），故 $|F(a_1)| \le 2 < 3$，矛盾。若 $r_1 = u$，则 $A(a_1) = \{y_1, y_2, u\}$，删去 $a_1$ 得 $S(a_1) \subseteq \{a_2, a_3\} \cup X(u)$（大小至多 3）；由 $L^*(a_1) \le 0$ 迫使 $F(a_1) = \{a_2, a_3, x\}$ 且 $N^+(\{a_2, a_3\}) \subseteq A(a_1)$，从而 $A(a_2) = A(a_3) = A(a_1) = \{y_1, y_2, u\}$，于是 $T(u) \subseteq (A(a_1) \cup A(a_2) \cup A(a_3)) \setminus \{u\} = \{y_1, y_2\}$（大小 2），矛盾于 $|T(u)| \ge 4$。
   * 于是所有 $u \in V(D)$ 均有 $|X(u)| = 0$，矛盾于引理 2。

定理 1 证毕。$\blacksquare$

---

## 定理 2 的证明（小准核猜想）

对 $|V(H)|$ 施强归纳，证明如下带预覆盖集 $P$ 的命题 $\mathcal{P}(H, P)$：设 $H$ 是任意有限简单有向图（允许有源点、允许双向边，无自环，且 $\Delta^+(H) \le 3$），$P \subseteq V(H)$ 包含 $H$ 的全部源点（$R(H) \subseteq P$）。则 $H$ 存在独立集 $Q \subseteq V(H)$，使 $2|Q| \le |V(H)|$ 且 $V(H) \setminus P \subseteq Q \cup N_H^+(Q) \cup N_H^{++}(Q)$。

$|V(H)| = 0$ 时取 $Q = \emptyset$ 成立。下设 $|V(H)| \ge 1$。

1. **情形 1：$H$ 含有源点 $r \in R(H) \subseteq P$。**
   * 若 $d_H^+(r) = 0$，令 $H' = H - \{r\}, P' = P \setminus \{r\}$。删去孤立点不产生新源，故 $R(H') \subseteq P'$；对 $(H', P')$ 用归纳假设所得的 $Q$ 即满足 $2|Q| \le |V(H')| < |V(H)|$ 并覆盖 $V(H) \setminus P$。
   * 若 $d_H^+(r) \ge 1$，令 $H' = H - N_H^+[r]$，$P' = (P \cap V(H')) \cup R(H')$。对 $(H', P')$ 用归纳假设得独立集 $Q'$，置 $Q = \{r\} \cup Q'$。因 $r$ 在 $H$ 中无入边且 $N_H^+(r)$ 已删，故 $Q$ 独立；任何 $u \in R(H') \setminus R(H)$ 在 $H$ 中必有前驱落在 $N_H^+(r)$ 中，从 $r$ 两步可达；又 $|V(H')| = |V(H)| - 1 - d_H^+(r) \le |V(H)| - 2$，故 $2|Q| = 2 + 2|Q'| \le 2 + |V(H')| \le |V(H)|$。

2. **情形 2：$H$ 无源（$R(H) = \emptyset$）。**
   由定理 1 取 $v \in V(H)$ 满足 $|E| \ge |S| + 1$，其中 $S = S_H(v) = R(H - N_H^+[v])$，$E = N_H^+(v) \cup N_H^+(S)$。注意 $S$ 独立且与 $E$ 不交（均不依赖无双向边）。令
   $$U = \{v\} \cup S \cup E, \qquad H' = H - U, \qquad P' = (P \cap V(H')) \cup R(H').$$
   对 $(H', P')$ 用归纳假设得独立集 $Q' \subseteq V(H')$，满足 $2|Q'| \le |V(H')|$。检查弧的关系：
   * $N_H^+(v) \cup N_H^+(S) = E \subseteq U$，故无弧从 $\{v\} \cup S$ 射入 $V(H')$；
   * $S$ 的全部前驱在 $N_H^+[v] \subseteq U$ 中，故无弧从 $V(H')$ 射入 $S$；
   * 对任一 $u \in R(H')$，因 $H$ 无源，$u$ 在 $H$ 中的全部前驱都在 $U$ 中，且不可能全在 $N_H^+[v]$ 中（否则 $u \in S \subseteq U$），也不可能是 $v$ 或 $S$ 中的点（其出邻集在 $U$ 中），故 $u$ 必有前驱落在 $N_H^+(S)$ 中，从而 $u$ 从 $S$ 沿两步可达。

   分两种子情形构造 $Q$：
   * 若 $v \in N_H^+(S) \cup N_H^+(Q')$，令 $Q = S \cup Q'$。则 $Q$ 独立；$v$ 从 $Q$ 一步可达，$N_H^+(v)$ 从 $Q$ 两步可达，其余由 $S$ 和 $Q'$ 两步覆盖。又 $|U| \ge |S| + |E| \ge 2|S| + 1$，故 $2|Q| = 2|S| + 2|Q'| \le 2|S| + |V(H)| - |U| \le |V(H)| - 1$。
   * 否则 $v \notin N_H^+(S) \cup N_H^+(Q')$，令 $Q = \{v\} \cup S \cup Q'$。此时 $\{v\}, S, Q'$ 之间无弧（双向均无），故 $Q$ 独立且两步覆盖 $V(H) \setminus P$。又无自环且 $v \notin N_H^+(S)$，故 $v \notin E$，从而 $\{v\}, S, E$ 两两不交，$|U| = 1 + |S| + |E| \ge 2(|S| + 1)$，于是 $2|Q| = 2(|S| + 1) + 2|Q'| \le |U| + |V(H')| = |V(H)|$。

取 $H = D, P = \emptyset$ 即得定理 2。$\blacksquare$

---

## 边界说明与复核

* **度上界 3 是紧的**：[第一轮实验](Clow-5.1-构造.md)已重放最大出度 4 的 24 点定向图，其每一点均满足 $g(v) = 0$。在定理 1 证明中，事实 2、情形 $M = 0$ 的 $2|F| \le 3d$ 计数与情形 $M = 1$ 的出弧盈余计数都在 $\Delta^+ = 3$ 处恰好绷紧，在 $\Delta^+ = 4$ 处自然失效。
* **允许双向边后的局部半径**：定向图上见证点总在某个显式根 $r$ 的 1 步邻域 $\{r\} \cup A_C(r)$（至多 4 点）内找到；允许双向边后，因引理 2（3-出正则双生）、引理 3（虚汇点）与情形 $M = 2$ 的 $w_1, w_2 \leftrightarrow r_1$ 分支，见证点总在 $r$ 的 2 步核心邻域（至多 13 点）内找到。
* **文献优先权**：以上定理 1 与定理 2 为本轮独立推导，文献优先权尚待核实。

在仓库根目录运行以下命令复核：

```powershell
node clow-proof-verify.mjs
node clow-proof-verify.mjs --full
```

[验证与构造程序](clow-proof-verify.mjs)同时检验定向图（1 步选点规则）和一般有向图（允许双向边，2 步选点规则）：
* 默认模式覆盖 11 个紧边界实例（含定向图 $M=3, 2, 1$ 移至子点例、双向 $K_{2,3}$、双向 $K_{3,3}$、双向 $K_{3,4}$ 双生例与双向虚汇点例）、全部 2–4 点一般有向核心（含双向边与每点至多 2 个汇点，15,105 张图）、全部 3–5 点定向核心（1,067,916 张图）以及 5,000 张至多 60 点的随机有向图（含双向边、双汇点与不连通图）；
* 加上 `--full` 后进一步穷举全部 6 点定向核心（932,286 张图）和全部 5 点一般双向核心（3,381 个同构类，163,841 张图），均用穷举全部 $2^{|S(v)|}$ 子集的独立程序核对 $L^*(v) \ge 1$，并对定理 2 构造出的准核 $Q$ 独立核对独立性、两步可达性与 $2|Q| \le |V(D)|$。
