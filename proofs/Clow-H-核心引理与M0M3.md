# §1　定理 1 证明：核心引理与 M = 0、3

[总览和定理陈述](Clow-统一极大局部定理与反例边界.md) · [下一节](Clow-H-M1.md)

### 定理 1 的完整证明

反证。假设对所有 $v \in C$ 均有 $L^*(v) \le 0$。沿用记号 $I_1 = \{x \in V(D) : d^-(x) = 1\}$，$Z = \{u \in V(D) : A(u) \cap I_1 = \emptyset\}$，$c_1^0(u) = |A(u) \cap (I_1 \cap Z)|$，$M = \max_{u \in C} c_1^0(u)$。对每个 $v \in C$，取使 $|A(v) \cup N^+(F)| - |F| = L^*(v)$ 且 $|F|$ 极小的 $F(v) \subseteq S(v)$。由与度数无关的基础工具（[Clow-5.1-证明](Clow-5.1-证明.md)事实 1 与引理 1）：
* **事实 1（单向父点排斥）**：若 $a \in A_C(v)$ 且 $a \not\to v$，则 $S(a) \cap A(v) = \emptyset$。
* **引理 1（入度 1 子点剪枝）**：$F(v) \subseteq S(v) \cap Z$。

记 $X(v) = N^+(F(v)) \setminus A(v)$，$T(v) = F(v) \cap C$，$H(v) = F(v) \cap K$，$F_1(v) = F(v) \cap I_1$（大小 $f_1(v)$），$F_{\ge 2}(v) = F(v) \setminus I_1$（大小 $f_{\ge 2}(v)$），$m_v(a) = |A(a) \cap F(v)|$（上下文清楚时简记 $m_a$）。恒有 $|F(v)| \ge d^+(v) + |X(v)|$，$m_a \le \alpha(a) \le 3$，且因 $A(u) \cap (I_1 \cap Z)$ 独立，有 $c_1^0(u) \le \alpha(u) \le 3$，从而 $M \in \{0, 1, 2, 3\}$。

#### 四个通用核心引理

**引理 H1（通用满扇出刚性，任意简单有向图成立）.** 对任意 $v \in C$ 与 $a \in A_C(v)$，令 $R = A(a) \cap F(v)$。若 $|R| = \alpha(a)$，则
$$A(a) \setminus R \subseteq N^-(R) \cup N^+(R) \subseteq A_C(v) \cup N^+(R) \subseteq A(v) \cup X(v),$$
且若 $a \to v$，必有 $v \in N^+(R) \subseteq X(v)$。

*证明.* 因 $R \subseteq S(v)$ 独立且 $|R| = \alpha(a)$，每个 $w \in A(a) \setminus R$ 必与某 $s \in R$ 相邻（否则 $R \cup \{w\} \subseteq A(a)$ 为大小 $\alpha(a) + 1$ 的独立集）。若 $w \to s$，因 $s \in S(v)$ 与 $N^+[v]$ 不交故 $w \neq v$ 且 $w \in N^-(s) \subseteq A_C(v)$；若 $s \to w$，则 $w \in N^+(R) \subseteq A(v) \cup X(v)$。特别地，$v \notin N^-(R)$，故 $v \in A(a) \setminus R$ 迫使 $v \in N^+(R) \subseteq X(v)$。$\square$

**引理 H2（$\mathcal{H}$ 中的汇点约简）.** 对每个 $v \in C$，必有 $c(v) \ge 1$ 且 $k(v) \le 1$。

*证明.* 若 $c(v) = 0$ 则 $S(v) = \emptyset$，$L^*(v) = d^+(v) \ge 1$ 矛盾。若 $k(v) \ge 3$，因 $K$ 独立且 $c(v) \ge 1$，有 $\alpha(v) \ge 3$ 且 $d^+(v) \ge 4$，违反 $D \in \mathcal{H}$。故只需排除 $k(v) = 2$。此时 $\alpha(v) \ge 2 \implies d^+(v) \in \{3, 4\}$：
* **$d^+(v) = 3$**（$A(v) = \{z_1, z_2, w\}$，$z_1, z_2 \in K, w \in C$）：$F(v) \subseteq A(w)$ 致 $3 \le |F(v)| \le \alpha(w) \implies \alpha(w) = 3 \implies d^+(w) = 3$，故 $A(w) = F(v)$、$|X(v)| = 0$ 且 $N^+(A(w)) \subseteq \{z_1, z_2, w\}$；删去 $N^+[w]$ 得 $S(w) \subseteq \{z_1, z_2\}$，$L^*(w) \ge 3 - 2 = 1$，矛盾。
* **$d^+(v) = 4$**（$\alpha(v) = 2$，$A(v) = \{z_1, z_2, w_1, w_2\}$，$z_1, z_2 \in K, w_1, w_2 \in C$）：因 $\{z_1, z_2\}$ 独立且汇点无出边，由 $\alpha(v) = 2$ 知每个 $w_i$ 至少指向 $z_1, z_2$ 之一。故无论 $w_i$ 属 I、II 还是 III 型（III 型时 $d^+(w_i) = 3$ 且有一出邻点为汇点 $\notin F(v)$），恒有 $m_{w_i} \le 2$。于是 $4 + |X(v)| \le |F(v)| \le m_{w_1} + m_{w_2} \le 4$，迫使 $|F(v)| = 4, |X(v)| = 0, m_{w_1} = m_{w_2} = 2$ 且 $Q_1 := A(w_1) \cap F(v)$ 与 $Q_2 := A(w_2) \cap F(v)$ 不交（各为 $w_i$ 的两个入度 1 子点）。考察 $w_1$：记 $w_1 \to z_a$（$a \in \{1, 2\}$），因 $Q_1 \cup \{z_a\} \subseteq A(w_1)$ 且 $Q_1$ 独立，有 $\alpha(w_1) \ge 2 \implies d^+(w_1) \in \{3, 4\}$。
  * 若 $d^+(w_1) = 3$，则 $A(w_1) = Q_1 \cup \{z_a\}$，$N^+(A(w_1)) \subseteq A(v)$，删去 $w_1, z_a$ 后 $S(w_1) \subseteq \{z_{3-a}, w_2\}$（大小至多 2），$L^*(w_1) \ge 1$，矛盾。
  * 若 $d^+(w_1) = 4$（$\alpha(w_1) = 2$），因 $|X(v)| = 0$ 故 $v \notin N^+(Q_1)$，由引理 H1 得 $w_1 \not\to v$ 且 $A(w_1) \setminus Q_1 \subseteq \{z_1, z_2, w_2\}$。若 $A(w_1) = Q_1 \cup \{z_1, z_2\}$，则 $S(w_1) \subseteq \{w_2\}$（$L^*(w_1) \ge 3$）；若 $A(w_1) = Q_1 \cup \{z_a, w_2\}$，由事实 1 得 $S(w_1) \cap A(v) = \emptyset$，故 $Q_1$ 与 $z_a$ 均不向 $S(w_1)$ 射弧，从而 $F(w_1) \subseteq A(w_2)$，$|F(w_1)| \le \alpha(w_2) \le 3 < 4$，均矛盾。$\square$

**引理 H3（通用无 $B_3$ 障碍引理）.** 对任意 $v \in C$，记 $B_3(v) := \{x \in A_C(v) : m_v(x) = 3\}$。则：
1. $B_3(v)$ 是 $D[A(v)]$ 中的独立集，故 $|B_3(v)| \le \alpha(v) \le 3$；
2. 若 $x \in B_3(v)$，则 $d^+(x) = 3$、$A(x) \subseteq F(v) \subseteq S(v) \cap Z$，且必有
   $$|X(v)| \ge |S(x)| \ge |F(x)| \ge 3 + |X(x)| \ge 4.$$
   若进一步 $K = \emptyset$ 且全图最小出度 $\delta^+(D) \ge 2$，则对任意满足 $A(x) \subseteq F(v)$ 的 $x \in A(v)$ 均有 $|X(v)| \ge d^+(x) + \delta^+(D)$（特别地，$x \in B_3(v) \implies |X(v)| \ge 5$）。

*证明.* 对任意 $x \in B_3(v)$，有 $\alpha(x) = 3 \implies d^+(x) = 3 \implies A(x) \subseteq F(v)$ 与 $A(v)$ 不交，故 $B_3(v)$ 内任意两点无弧，(1) 得证。再证 (2)：由 $v \notin S(v) \supseteq A(x)$ 得 $x \not\to v$，由事实 1 与 $N^+(A(x)) \subseteq A(v) \cup X(v)$ 得 $S(x) \subseteq X(v)$。因 $A(x) \subseteq Z$，故 $f_1(x) = 0$（每个 $w \in F(x)$ 在 $A(x)$ 中有至少 2 个前驱）；由引理 H2 知 $2|H(x)| \le \sum_{a \in A(x)} k(a) \le 3 \implies |H(x)| \le 1$，结合 $|F(x)| \ge 3$ 得 $|T(x)| \ge 2$。任取 $t \in T(x) \subseteq X(v)$：因 $A(x) \subseteq S(v)$ 的全部前驱落在 $A(v)$ 中，而 $X(v)$ 与 $A(v)$ 不交（且即使 $t = v$ 亦有 $A(x) \subseteq S(v)$ 与 $A(v)$ 不交，故 $v \not\to A(x)$），恒有 $N^+(t) \cap A(x) = \emptyset$。因此 $N^+(t) \subseteq X(x)$，$|X(x)| \ge d^+(t) \ge 1$，得 $|X(v)| \ge |F(x)| \ge 3 + 1 = 4$。当 $K = \emptyset$ 且 $\delta^+(D) \ge 2$ 时，对任意满足 $A(x) \subseteq F(v)$ 的 $x$，同样有 $S(x) \subseteq X(v)$ 及 $N^+(t) \cap A(x) = \emptyset$，从而 $|X(x)| \ge \delta^+(D)$ 且 $|X(v)| \ge d^+(x) + \delta^+(D)$。$\square$

**引理 H4（带 $B_3$ 修正的主恒等式与半完全度界）.** 对任意 $v \in C$，记 $n_1(v) = |\{a \in A_C(v) : \alpha(a) = 1\}|$。双向统计 $A_C(v)$ 到 $F(v)$ 的弧数得
$$2k(v) + 2|X(v)| + n_1(v) + 2\bigl(|F(v)| - d^+(v) - |X(v)|\bigr) + \sum_{a \in A_C(v)} \bigl(\tilde{\alpha}(a) - m_a\bigr) + \sum_{s \in F_{\ge 2}(v)} (d^-(s) - 2) = f_1(v) + |B_3(v)|, \tag{$\dagger$}$$
其中 $\tilde{\alpha}(a) = 1$（$a$ 为 I 型）、$2$（$a$ 属 II/III 型且 $a \notin B_3(v)$）或 $3$（$a \in B_3(v)$），且左端各项均非负。此外，若 $v$ 为 I 型（$\alpha(v) = 1$），记 $W(v) := \{a \in A_C(v) : \alpha(a) \ge 2\}$（大小 $w$），则 $D[W(v)]$ 为半完全有向图且对每个 $a \in W(v)$ 有 $d_{D[W(v)]}^+(a) + m_a \le d^+(a) \le 4$，从而
$$\sum_{a \in W(v)} (m_a - 1) \le 3w - \binom{w}{2} = \frac{w(7 - w)}{2} \le 6. \tag{$\ddagger$}$$

*证明.* 弧数 $e(A_C(v), F(v))$ 一方面等于 $\sum_{a \in A_C(v)} m_a = 2(d^+(v) - k(v)) - n_1(v) + |B_3(v)| - \sum (\tilde{\alpha}(a) - m_a)$，另一方面等于 $2|F(v)| - f_1(v) + \sum_{s \in F_{\ge 2}(v)} (d^-(s) - 2)$，联立移项即得 $(\dagger)$。当 $\alpha(v) = 1$ 时，$W(v) \subseteq A(v)$ 诱导半完全有向图，内部出度之和至少 $\binom{w}{2}$，又 $F(v) \cap W(v) = \emptyset$ 且每个 $a \in W(v)$ 满足 $d^+(a) \le 4$，求和即得 $(\ddagger)$。$\square$

以下按 $M \in \{3, 0, 1, 2\}$ 逐一推出矛盾。

---

#### 情形 $M = 3$

取 $u^* \in C$ 使 $c_1^0(u^*) = 3$。则 $\alpha(u^*) = 3 \implies d^+(u^*) = 3$，且 $A(u^*) \subseteq I_1 \cap Z \subseteq Z \implies f_1(u^*) = 0$。
* 若 $k(u^*) = 1$：记 $A_C(u^*) = \{a_1, a_2\}$，则 $F(u^*) \subseteq A(a_1) \cap A(a_2)$ 且 $|F(u^*)| \ge 3$，故 $a_1 \in B_3(u^*)$；由引理 H3 得 $|X(u^*)| \ge 4 \implies |F(u^*)| \ge 7 > 3$，矛盾。
* 若 $k(u^*) = 0$：由 $2|F(u^*)| \le 9$ 得 $|F(u^*)| \le 4 \implies |X(u^*)| \le 1$，故由引理 H3 知 $B_3(u^*) = \emptyset$。从而 $m_a \le 2$ 对所有 $a \in A(u^*)$ 成立，得 $2|F(u^*)| \le 6 \implies |F(u^*)| = 3, |X(u^*)| = 0$。但由引理 H2 知 $2|H(u^*)| \le 3 \implies |H(u^*)| \le 1 \implies |T(u^*)| \ge 2$，而 $A(u^*) \subseteq I_1$ 仅有前驱 $u^*$，故 $N^+(T(u^*)) \cap A(u^*) = \emptyset \implies |X(u^*)| \ge 1$，矛盾。

---

#### 情形 $M = 0$

此时对所有 $v \in C$ 有 $f_1(v) = 0$。由 $(\dagger)$ 得 $2k(v) + 2|X(v)| + n_1(v) \le |B_3(v)| \le 3$。若 $B_3(v) \neq \emptyset$，由引理 H3 得 $|X(v)| \ge 4 \implies 8 \le 2|X(v)| \le 3$，矛盾。故对每个 $v \in C$ 均有 $B_3(v) = \emptyset$，代入 $(\dagger)$ 迫使：
$$k(v) = 0,\quad |X(v)| = 0,\quad n_1(v) = 0,\quad |F(v)| = d^+(v),\quad m_a = 2 \;(\forall a \in A(v)),\quad d^-(s) = 2 \;(\forall s \in F(v)).$$
因图无源且处处 $n_1(v) = 0$，全图不含 I 型点，故所有顶点均满足 $d^+(u) \in \{2, 3, 4\}$（$d^+(v) = 1$ 时 $F(v)$ 无法在 $A(v)$ 中有 2 个前驱）。取最小出度点 $r \in V(D)$，令 $\delta = d^+(r) \in \{2, 3, 4\}$。因 $|X(r)| = 0$ 且对所有 $s \in F(r)$ 有 $d^+(s) \ge \delta = |A(r)|$，恒有 $N^+(s) = A(r)$（从而 $s \not\to r$）。
* **$\delta = 2$**（$A(r) = \{a_1, a_2\}, F(r) = \{s_1, s_2\} \subseteq A(a_1)$）：若 $d^+(a_1) = 4$（$\alpha(a_1) = 2$），由引理 H1 得 $A(a_1) \setminus F(r) \subseteq \{a_2\}$（大小至多 1），矛盾。故 $d^+(a_1) \in \{2, 3\}$：若 $a_1 \not\to r$，由事实 1 知 $F(r)$ 不射入 $S(a_1)$，余下至多 1 个出邻点无法供给 $d^-(s) = 2$；若 $a_1 \to r$，则 $A(a_1) = \{s_1, s_2, r\} \implies S(a_1) \subseteq \{a_2\}$（大小至多 $1 < 3$），均矛盾。
* **$\delta = 3$**：任取 $a \in A(r)$，设 $R = A(a) \cap F(r)$（大小 2）。若 $d^+(a) = 4$（$\alpha(a) = 2$），由引理 H1 得 $a \not\to r$ 且 $A(a) = R \cup (A(r) \setminus \{a\})$；由事实 1 知 $R$ 不射入 $S(a)$，故 $2|F(a)| \le \sum_{b \in A(r) \setminus \{a\}} m_a(b) \le 4 \implies |F(a)| \le 2 < 4$，矛盾。因此所有 $a \in A(r)$ 均满足 $d^+(a) = 3$ 与 $|X(a)| = 0$。任取 $t \in F(r)$ 及 $a \in N^-(t) \subseteq A(r)$：每个 $a' \in F(a)$ 满足 $d^+(a') \ge 3 = |A(a)|$ 与 $|X(a)| = 0$，故 $A(a') = A(a) \ni t$，即 $\{a\} \cup F(a) \subseteq N^-(t) \subseteq A(r)$，得 $4 \le 1 + 3 \le |A(r)| = 3$，矛盾。
* **$\delta = 4$**：全图 4-出正则，从而 $\alpha^+(D) \le 2$，直接由[禁出星图笔记](Clow-禁出星图与相图.md)定理 2 矛盾（自洽短证：任取 $a_1 \in A(r)$，设 $R = A(a_1) \cap F(r)$ 大小 2，由引理 H1 得 $a_1 \not\to r$ 且 $A(a_1) \setminus R \subseteq A(r)$；同理每个 $a_j \in A(a_1) \cap A(r)$ 有 $A(a_j) \subseteq F(r) \cup A(r)$，结合事实 1 得 $S(a_1) \subseteq F(r) \setminus R$ 且 $2|S(a_1)| \le 2|A(a_1) \cap A(r)| = 4 \implies |S(a_1)| \le 2 < 4$，矛盾）。

---
