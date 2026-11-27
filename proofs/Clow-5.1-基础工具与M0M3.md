# 定理 1　四个基础工具与 M = 0、3

[总览和定理陈述](Clow-5.1-证明.md) · [下一节](Clow-5.1-M2M1.md)

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
