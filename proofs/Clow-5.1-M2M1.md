# 定理 1　M = 2、1

[总览和定理陈述](Clow-5.1-证明.md) · [上一节](Clow-5.1-基础工具与M0M3.md) · [下一节](Clow-5.1-准核归纳与复核.md)

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
