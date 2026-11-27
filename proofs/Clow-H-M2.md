# §1　定理 1 证明：M = 2

[总览和定理陈述](Clow-统一极大局部定理与反例边界.md) · [上一节](Clow-H-M1.md) · [下一节](Clow-H-定向反例.md)

#### 情形 $M = 2$

记 $U_2 := \{u \in C : c_1^0(u) = 2\} \neq \emptyset$。对任意 $u \in U_2$，因 $A(u) \cap (I_1 \cap Z)$ 独立且大小为 2，有 $\alpha(u) \ge 2 \implies d^+(u) \in \{2, 3, 4\}$。我们逐次排除 $U_2$ 中可能出现的构型，逐步收紧对全体 $u \in U_2$ 均成立的**全局结构不变量**。

**步骤 1（排除 $d^+(u^*) \in \{2, 3\}$）.**
* 若 $d^+(u^*) = 2$：$A(u^*) = \{a_1, a_2\} \subseteq I_1 \cap Z \implies f_1(u^*) = 0$。若 $k(u^*) = 1$ 则 $F(u^*) = \emptyset$ 矛盾；若 $k(u^*) = 0$，由引理 H2 得 $|H(u^*)| \le 1 \implies |T(u^*)| \ge 1$，又 $a_1, a_2 \in I_1$ 仅有前驱 $u^*$，得 $|X(u^*)| \ge 1 \implies |F(u^*)| \ge 3$，从而 $a_1 \in B_3(u^*)$，由引理 H3 得 $|X(u^*)| \ge 4 \implies |F(u^*)| \ge 6 > 3$，矛盾。
* 若 $d^+(u^*) = 3$ 且 $k(u^*) = 1$：若汇点 $z^* \notin I_1$，则两核心后继全在 $I_1 \cap Z$ 中，$f_1(u^*) = 0$ 致 $a_1 \in B_3(u^*)$，引理 H3 矛盾；若 $z^* \in I_1$，记 $A(u^*) = \{a_1, a_3, z^*\}$（$a_1 \in I_1 \cap Z$），则 $F(u^*) \subseteq A(a_3)$ 致 $a_3 \in B_3(u^*)$，仍由引理 H3 矛盾。
* 若 $d^+(u^*) = 3$ 且 $k(u^*) = 0$：记 $A(u^*) = \{a_1, a_2, a_3\}$（$a_1, a_2 \in I_1 \cap Z$），分划 $F(u^*) = P \sqcup Q$，其中 $P = \{x \in F(u^*) : N^-(x) = \{a_1, a_2\}\}$（大小 $p$），$Q = \{x \in F(u^*) : a_3 \to x\}$（大小 $q_1 + q_2$，$q_1 = |Q \cap I_1| \le 2$，$q_2 = |Q \setminus I_1|$）。因 $p + |Q| \ge 3 + |X(u^*)|$ 且每个 $m_x \le 3$：
  * $p = 0$：$|Q| \ge 3 \implies a_3 \in B_3(u^*)$，引理 H3 矛盾。
  * $p = 1$：若 $|Q| = 3$ 同理 $a_3 \in B_3(u^*)$ 矛盾；若 $|Q| = 2$，则 $|F(u^*)| = 3, |X(u^*)| = 0$，由 $a_1, a_2 \in I_1$ 得 $N^+(Q) \subseteq \{a_3\}$。因 $Q \subseteq A(a_3)$ 独立，有 $d^+(a_3) \in \{2, 3, 4\}$：$d^+(a_3) \le 3$ 同[Clow-5.1-证明](Clow-5.1-证明.md)情形 $M = 2$ 矛盾；若 $d^+(a_3) = 4$（$\alpha(a_3) = 2$），由引理 H1 得 $A(a_3) \setminus Q \subseteq \{a_1, a_2\}$，但 $a_1, a_2 \in I_1$ 仅有前驱 $u^* \neq a_3$，故 $a_3 \not\to a_1, a_2$，矛盾。
  * $p = 3$：$a_1 \in B_3(u^*)$，引理 H3 给 $|X(u^*)| \ge 4 \implies |F(u^*)| \ge 7$，而 $p + |Q| \le 3 + 3 = 6$，矛盾。
  * $p = 2$：若 $q_2 \ge 1$，取 $y \in Q \setminus I_1$（不妨 $a_1 \to y$），则 $a_1 \in B_3(u^*)$，引理 H3 给 $|X(u^*)| \ge 4 \implies |F(u^*)| \ge 7 > 2 + 3 = 5$，矛盾。故 $q_2 = 0$，$|F(u^*)| = 2 + q_1 \le 4 \implies |X(u^*)| \le 1$。先排除 $d^+(a_1) = 4$（$\alpha(a_1) = 2$）：因 $a_1, a_2 \in I_1$ 仅有前驱 $u^*$，引理 H1 对 $P \subseteq A(a_1)$ 给出 $A(a_1) \setminus P \subseteq \{a_3\} \cup X(u^*)$，迫使 $|X(u^*)| = 1$（记 $X(u^*) = \{x\}$，$q_1 = |Q| = 2$）且 $A(a_1) = P \cup \{a_3, x\}$。
    * 若 $x = u^*$：$N^+(P) \subseteq \{a_3, u^*\}$ 且 $N^+(u^*) = \{a_1, a_2, a_3\}$，故 $F(a_1) \setminus \{a_2\} \subseteq A(a_3) \cap (I_1 \cap Z)$（大小至多 $M = 2$），得 $|F(a_1)| \le 3 < 4$，矛盾。
    * 若 $x \neq u^*$：考察 $a_3$（含 $Q = \{q_a, q_b\} \subseteq I_1 \cap Z$，且 $N^+(Q) \subseteq \{a_3, x\}$），有 $d^+(a_3) \in \{2, 3, 4\}$。$d^+(a_3) = 2$ 时 $S(a_3) \subseteq \{x\}$（大小至多 $1 < 2$）；$d^+(a_3) = 4$（$\alpha(a_3) = 2$）时引理 H1 对 $Q \subseteq I_1$ 给 $A(a_3) \setminus Q \subseteq \{x\}$（大小至多 $1 < 2$）；$d^+(a_3) = 3$（$A(a_3) = Q \cup \{r\}$）时，因 $a_1 \notin N^+[a_3]$（$a_1 \in I_1$ 仅有前驱 $u^* \neq a_3$）且 $a_1 \to x$，故 $x \notin S(a_3)$，从而 $Q$ 不射入 $S(a_3)$：若 $r = u^*$ 则 $S(a_3) \subseteq \{a_1, a_2\}$（大小至多 $2 < 3$），若 $r \neq u^*$ 则 $F(a_3) \subseteq A(r) \cap (I_1 \cap Z)$（大小至多 $M = 2 < 3$），均矛盾。
    因此必有 $d^+(a_1), d^+(a_2) \le 3$。后续完全同[Clow-5.1-证明](Clow-5.1-证明.md)子情形 2.3（$p = 2$），直至末步出现 $r_1$ 含 $\{w_1, w_2\} \subseteq A(r_1) \cap (I_1 \cap Z)$ 且 $N^+(w_1), N^+(w_2) \subseteq \{r_1\}$：$d^+(r_1) \in \{2, 3\}$ 同原证矛盾；$d^+(r_1) = 4$（$\alpha(r_1) = 2$）时引理 H1 对 $\{w_1, w_2\} \subseteq I_1$ 给出 $A(r_1) \setminus \{w_1, w_2\} \subseteq \emptyset$，矛盾。

因此全体 $u \in U_2$ 均满足 **$d^+(u) = 4$ 且 $\alpha(u) = 2$**。记 $A(u) = \{a_1, a_2, b_1, b_2\}$（$a_1, a_2 \in I_1 \cap Z$）。因 $\{a_1, a_2\} \subseteq I_1$ 独立且无来自 $b_1, b_2$ 的入弧，由 $\alpha(u) = 2$ 必有
$$\{b_1, b_2\} \subseteq N^+(a_1) \cup N^+(a_2). \tag{$\diamond$}$$
此外对任意 $u \in U_2$ 必有 $B_3(u) = \emptyset$：若 $B_3(u) \neq \emptyset$，则引理 H3 给 $|X(u)| \ge 4 \implies |F(u)| \ge 8$，而 $f_1(u) \le c_1^0(b_1) + c_1^0(b_2) \le 4$，故 $2|F(u)| - f_1(u) \ge 12$，但 $\sum_{x \in A_C(u)} m_x \le 8 + |B_3(u)| \le 8 + \alpha(u) = 10 < 12$，矛盾。从而 $(\dagger)$ 在每个 $u \in U_2$ 处化简为
$$2k(u) + 2|X(u)| + 2\bigl(|F(u)| - 4 - |X(u)|\bigr) + \sum_{x \in A_C(u)} (2 - m_x) + \sum_{s \in F_{\ge 2}(u)} (d^-(s) - 2) = f_1(u) \le 4. \tag{$\dagger_2$}$$

**步骤 2（排除 $k(u^*) = 1$ 与 $|X(u^*)| = 0$）.**
先建立一处通用排除：若某 $u^* \in U_2$ 满足 $|X(u^*)| = 0$，且某核心点 $b \in \{b_1, b_2\}$ 满足 $m_b = 2$（记 $Q_b = A(b) \cap F(u^*)$，大小 2），则矛盾！*证*：因 $a_1, a_2 \in I_1$ 仅有前驱 $u^*$，有 $N^+(Q_b) \subseteq \{b_1, b_2\}$（不含 $u^*$），记 $b'$ 为 $\{b_1, b_2\} \setminus \{b\}$。由 $Q_b$ 独立知 $d^+(b) \in \{2, 3, 4\}$。若 $d^+(b) = 4$（$\alpha(b) = 2$），由引理 H1 得 $b \not\to u^*$ 且 $A(b) \setminus Q_b \subseteq A(u^*) \setminus \{a_1, a_2, b\} = \{b'\}$（大小 1），矛盾。若 $b \not\to u^*$ 且 $d^+(b) \le 3$，由事实 1 知 $Q_b$ 不射入 $S(b)$，故 $d^+(b) = 2$ 时 $S(b) = \emptyset$，$d^+(b) = 3$ 时 $|F(b)| \le M = 2 < 3$，均矛盾。若 $b \to u^*$（此时 $d^+(b) = 3, A(b) = Q_b \cup \{u^*\}$），删去 $N^+[b]$ 后 $a_1, a_2$ 均存活，而由 $(\diamond)$ 知 $a_1, a_2$ 中至少一者指向 $b'$，故 $b' \notin S(b)$，从而 $S(b) \subseteq \{a_1, a_2\}$（大小至多 $2 < 3$），矛盾！$\square$

由此立即排除：
* **$k(u^*) = 1$**：由 $(\dagger_2)$ 得 $2 + 2|X(u^*)| \le f_1(u^*) \le 4$。
  * 若汇点在 $\{b_1, b_2\}$ 中（不妨 $b_2 \in K$），则 $f_1(u^*) \le c_1^0(b_1) \le 2$，迫使 $|X(u^*)| = 0, f_1(u^*) = 2, m_{b_1} = 2$，直接由上述通用排除矛盾。
  * 若汇点在 $\{a_1, a_2\}$ 中（不妨 $a_2 \in K$），则 $F_1(u^*)$ 与 $F_{\ge 2}(u^*)$ 满足 $f_1(u^*) + 2f_{\ge 2}(u^*) \le m_{a_1} + m_{b_1} + m_{b_2} \le 6$，结合 $|F(u^*)| \ge 4 + |X(u^*)|$ 得 $f_1(u^*) \ge 2 + 2|X(u^*)|$。若 $|X(u^*)| = 1$，迫使 $f_1(u^*) = 4$，则 $b_1, b_2$ 已用尽 $m_{b_1} = m_{b_2} = 2$ 射入 $F_1(u^*)$，无力供给 $F_{\ge 2}(u^*)$，从而 $f_{\ge 2}(u^*) = 0$，矛盾于 $|F(u^*)| \ge 5$。故 $|X(u^*)| = 0, |F(u^*)| = 4$；若 $m_{b_1}, m_{b_2} \le 1$，则 $f_1(u^*) \le 2$ 且 $f_1(u^*) + 2f_{\ge 2}(u^*) \le m_{a_1} + m_{b_1} + m_{b_2} \le 4 \implies |F(u^*)| \le 3 < 4$ 矛盾，故必有 $m_{b_1} = 2$ 或 $m_{b_2} = 2$，仍由上述通用排除矛盾。
* **$k(u^*) = 0$ 且 $|X(u^*)| = 0$**：若 $m_{b_1} = 2$ 或 $m_{b_2} = 2$，直接由上述通用排除矛盾。否则 $m_{b_1}, m_{b_2} \le 1$，则 $f_1(u^*) \le 2$ 且 $\sum (2 - m_x) \ge 2$，代入 $(\dagger_2)$ 迫使 $f_1(u^*) = 2$、$m_{b_1} = m_{b_2} = 1$、$m_{a_1} = m_{a_2} = 2$、$|F(u^*)| = 4$（$L^*(u^*) = 0$），记 $P := F_{\ge 2}(u^*) = \{p_1, p_2\} \subseteq A(a_1) \cap A(a_2)$。由 $(\diamond)$ 不妨 $a_1 \to b_1$，则 $d^+(a_1) \in \{3, 4\}$。若 $d^+(a_1) = 3$（$A(a_1) = P \cup \{b_1\}$），由事实 1 知 $P$ 不射入 $S(a_1)$，得 $|F(a_1)| \le M = 2 < 3$ 矛盾。故 $d^+(a_1) = 4$（$\alpha(a_1) = 2$），由引理 H1（$|X(u^*)| = 0$ 且 $a_1, a_2 \in I_1$）得 $a_1 \not\to u^*$ 且 $A(a_1) = P \cup \{b_1, b_2\}$。于是 $S(a_1) \cap A(u^*) = \emptyset$ 且 $N^+(P) \subseteq \{b_1, b_2\} \subseteq N^+[a_1]$，故每个 $w \in F(a_1)$ 的全部前驱落在 $\{b_1, b_2\} \subseteq A(u^*)$ 中，从而 $F_0 := F(a_1) \setminus \{u^*\} \subseteq S(u^*)$ 且与 $P$ 不交。对任意 $w \in F_0$ 及 $y \in N^+(w) \setminus A(u^*)$，因 $S(u^*)$ 独立故 $y \notin P$，从而 $y \notin A(a_1)$，即 $N^+(F_0) \setminus A(u^*) \subseteq X(a_1)$。令 $F_{\text{new}} := P \cup F_0 \subseteq S(u^*)$，则 $|F_{\text{new}}| = 2 + |F_0| \ge 2 + (|F(a_1)| - 1) \ge 5 + |X(a_1)|$ 而 $|A(u^*) \cup N^+(F_{\text{new}})| \le 4 + |X(a_1)|$，给出 $L^*(u^*) \le -1 < 0$，矛盾于 $L^*(u^*) = 0$！

因此全体 $u \in U_2$ 均满足 **$d^+(u) = 4, \alpha(u) = 2, k(u) = 0, |X(u)| \in \{1, 2\}$**。

**步骤 3（排除 $|X(u^*)| = 2$）.**
设某 $u^* \in U_2$ 满足 $|X(u^*)| = 2$。由 $(\dagger_2)$ 迫使 $f_1(u^*) = 4, |F(u^*)| = 6, m_{a_1} = m_{a_2} = m_{b_1} = m_{b_2} = 2$，记 $Q_1 = A(b_1) \cap F_1(u^*), Q_2 = A(b_2) \cap F_1(u^*)$（各大小 2），$P = F_{\ge 2}(u^*) = \{p_1, p_2\} \subseteq A(a_1) \cap A(a_2)$。于是 $b_1, b_2 \in U_2$！由步骤 2 知 $d^+(b_1) = 4, |X(b_1)| \ge 1$，且由 $(\diamond)$ 对 $b_1$ 得 $A(b_1) \setminus Q_1 \subseteq N^+(Q_1) \setminus \{b_1\} \subseteq \{b_2\} \cup X(u^*)$。
* 若 $b_1 \not\to u^*$：由事实 1 知 $S(b_1) \cap A(u^*) = \emptyset$。
  * 若 $A(b_1) = Q_1 \cup X(u^*)$，则 $N^+(Q_1) \subseteq N^+[b_1] \cup \{b_2\}$ 不射入 $S(b_1)$，即 $m_{b_1}(q) = 0$（$\forall q \in Q_1$）；代入 $b_1$ 的 $(\dagger_2)$ 得 $2|X(b_1)| + 4 \le 4$，矛盾于 $|X(b_1)| \ge 1$。
  * 若 $A(b_1) = Q_1 \cup \{b_2, x_1\}$（$X(u^*) = \{x_1, x_2\}$），则 $Q_1$ 在 $S(b_1)$ 中至多射向唯一点 $x_2$，故 $m_{b_1}(q) \le 1$（$\forall q \in Q_1$）。代入 $b_1$ 的 $(\dagger_2)$ 迫使 $|X(b_1)| = 1, |F(b_1)| = 5, f_1(b_1) = 4, m_{b_1}(b_2) = m_{b_1}(x_1) = 2, m_{b_1}(q) = 1$（即 $F(b_1) = Q_2 \sqcup W_{x_1} \sqcup \{x_2\}$）。记 $X(b_1) = \{z_0\}$：因 $Q_2 \subseteq F(b_1)$ 且 $Q_1 \subseteq I_1$ 仅有前驱 $b_1$，有 $N^+(Q_2) \setminus \{b_2\} \subseteq \{x_1, z_0\}$；由 $b_2 \in U_2$ 的 $(\diamond)$ 迫使 $A(b_2) = Q_2 \cup \{x_1, z_0\}$ 且 $z_0 \in \{b_1, x_2\}$。但 $x_2 \in F(b_1) \subseteq S(b_1)$ 独立于 $Q_2 \subseteq F(b_1)$，故 $z_0 \neq x_2$，得 $z_0 = b_1$ 且 $A(b_2) = Q_2 \cup \{x_1, b_1\}$！于是 $N^+(Q_2) \subseteq \{b_1, b_2, x_1\} \subseteq N^+[b_2]$ 不射入 $S(b_2)$，代入 $b_2 \in U_2$ 的 $(\dagger_2)$ 得 $2|X(b_2)| + 4 \le 4$，矛盾！
* 若 $b_1 \to u^*$：则 $u^* \in X(u^*)$，记 $X(u^*) = \{u^*, x_2\}$，$A(b_1) = Q_1 \cup \{u^*, r_2\}$（$r_2 \in \{b_2, x_2\}$）。
  * 若 $r_2 = x_2$：删去 $N^+[b_1]$ 后 $a_1, a_2$ 存活，由 $(\diamond)$ 知 $b_2 \notin S(b_1)$，故 $Q_1$ 不射入 $S(b_1)$，$b_1$ 的 $(\dagger_2)$ 给 $2|X(b_1)| + 4 \le 4$ 矛盾。
  * 若 $r_2 = b_2$：$Q_1$ 在 $S(b_1)$ 中至多射向 $x_2$，同上由 $b_1$ 的 $(\dagger_2)$ 迫使 $|X(b_1)| = 1, f_1(b_1) = 4, F(b_1) = \{a_1, a_2\} \sqcup Q_2 \sqcup \{x_2\}$。但 $P = \{p_1, p_2\} \subseteq N^+(a_1)$ 与 $A(b_1) = Q_1 \cup \{u^*, b_2\}$ 不交，故 $\{p_1, p_2\} \subseteq X(b_1)$ 致 $|X(b_1)| \ge 2$，矛盾！

因此全体 $u \in U_2$ 均满足升级后的全局不变量：**$d^+(u) = 4, \alpha(u) = 2, k(u) = 0, |X(u)| = 1$**。

**步骤 4（排除全体 $|X(u)| = 1$，证毕）.**
任取 $u^* \in U_2$，记 $X(u^*) = \{x_0\}$。由 $(\dagger_2)$ 得 $2 + 2(|F(u^*)| - 5) + \sum (2 - m_x) + \sum (d^-(s) - 2) = f_1(u^*) \in \{2, 3, 4\}$。
* **若 $b_1$ 或 $b_2$ 向 $F_1(u^*)$ 送出 2 条弧**（不妨 $b_1$ 送出 $Q_1 = \{q_{11}, q_{12}\} \subseteq F_1(u^*)$）：则 $b_1 \in U_2$！由升级全局不变量对 $b_1$ 应用 $(\diamond)$ 得 $A(b_1) \setminus Q_1 \subseteq N^+(Q_1) \setminus \{b_1\} \subseteq \{b_2, x_0\}$。因左右大小均为 2，迫使 $A(b_1) = Q_1 \cup \{b_2, x_0\}$！于是 $N^+(Q_1) \subseteq \{b_1, b_2, x_0\} \subseteq N^+[b_1]$，即 $Q_1$ 不射入 $S(b_1)$；代入 $b_1$ 的 $(\dagger_2)$ 得 $2|X(b_1)| + 4 = 6 \le f_1(b_1) \le 4$，矛盾！
* **否则必为 $f_1(u^*) = 2$ 且 $b_1, b_2$ 各向 $F_1(u^*)$ 送 1 条弧**（$b_1 \to q_1, b_2 \to q_2$）：代入 $(\dagger_2)$ 迫使 $|F(u^*)| = 5$（$F_{\ge 2}(u^*) = \{p_1, p_2, p_3\}$），$m_{a_1} = m_{a_2} = m_{b_1} = m_{b_2} = 2$，且每个 $p_j$ 有 $d^-(p_j) = 2$。记 $Q_{b_1} := A(b_1) \cap F(u^*) = \{q_1, p_1\}$（大小 2，独立），有 $N^+(Q_{b_1}) \subseteq \{b_1, b_2, x_0\}$ 与 $d^+(b_1) \in \{2, 3, 4\}$：
  * **$d^+(b_1) = 2$**：$b_1 \not\to u^*$，由事实 1 得 $S(b_1) \subseteq \{x_0\}$（大小至多 $1 < 2$），矛盾。
  * **$d^+(b_1) = 4$（$\alpha(b_1) = 2$）**：对 $Q_{b_1} \subseteq A(b_1)$ 应用引理 H1，注意 $a_1, a_2 \in I_1$ 仅有前驱 $u^* \neq b_1$，故 $A(b_1) \setminus Q_{b_1} \subseteq \{b_2, x_0\}$，迫使 $A(b_1) = \{q_1, p_1, b_2, x_0\}$，从而 $Q_{b_1}$ 不射入 $S(b_1)$。同前易验 $B_3(b_1) = \emptyset$（否则 $|X(b_1)| \ge 4 \implies 2|F(b_1)| - f_1(b_1) \ge 12 > 6$），代入 $b_1$ 的 $(\dagger)$ 迫使 $|X(b_1)| = 0, |F(b_1)| = 4, f_1(b_1) = 4$，从而 $b_2 \in U_2$（设 $W_b = A(b_2) \cap F_1(b_1)$，大小 2）。因 $|X(b_1)| = 0$，有 $N^+(W_b) \subseteq A(b_1) = \{q_1, p_1, b_2, x_0\}$；但 $q_1 \in I_1$ 仅有前驱 $b_1$，且 $W_b \subseteq I_1$ 仅有前驱 $b_2 \neq u^*$（故 $W_b \cap A(u^*) = \emptyset$），而 $N^-(p_1) \subseteq A(u^*)$，故 $W_b \not\to q_1, p_1$！于是 $N^+(W_b) \setminus \{b_2\} \subseteq \{x_0\}$ 大小至多 $1 < 2$，矛盾于 $b_2 \in U_2$ 的 $(\diamond)$！
  * **$d^+(b_1) = 3$**（$A(b_1) = \{q_1, p_1, r_1\}$）：
    * 若 $r_1 = u^*$：删去 $N^+[b_1]$ 后 $a_1, a_2$ 存活，由 $(\diamond)$ 知 $b_2 \notin S(b_1)$，故 $S(b_1) \subseteq \{a_1, a_2, x_0\}$（大小至多 3），迫使 $F(b_1) = \{a_1, a_2, x_0\}$ 且 $|X(b_1)| = 0$。但 $\{p_2, p_3\} \subseteq N^+(a_1) \cup N^+(a_2)$ 与 $A(b_1)$ 不交，矛盾！
    * 若 $r_1 \neq u^*$：由事实 1 知 $S(b_1) \cap A(u^*) = \emptyset$，故 $Q_{b_1}$ 在 $S(b_1)$ 中至多射向 $x_0$。若 $r_1 = x_0$ 则 $F(b_1) \subseteq A(x_0) \cap (I_1 \cap Z)$ 大小至多 $2 < 3$ 矛盾；若 $r_1 \neq x_0$，则 $|F(b_1) \setminus \{x_0\}| \le M = 2$ 迫使 $|X(b_1)| = 0, |F(b_1)| = 3, x_0 \in F(b_1)$ 且 $W := F(b_1) \setminus \{x_0\} \subseteq A(r_1) \cap (I_1 \cap Z)$ 大小 2，从而 $r_1 \in U_2$！但由 $|X(b_1)| = 0$、$q_1 \in I_1$ 与 $W \cap A(u^*) = \emptyset$ 知 $N^+(W) \subseteq \{r_1\}$，即 $N^+(W) \setminus \{r_1\} = \emptyset$，矛盾于 $r_1 \in U_2$ 的 $(\diamond)$！

定理 1 证毕。$\blacksquare$

---
