# The small quasi-kernel conjecture

[简体中文](README.zh-CN.md)

A **quasi-kernel** is an independent set $Q$ from which every vertex is reachable along at most two directed arcs. The Erdős–Székely conjecture asks whether every finite source-free digraph on $n$ vertices has a quasi-kernel of size at most $n/2$. We work with simple digraphs and allow opposite arcs.

## Main results

These results are presented as hand-written proofs awaiting independent review. Literature priority for the degree-four and O1-R results is still to be checked.

### Maximum in-degree four · `Q-4` and `Q-4-ALG`

Ai, Gerke, Gutin, Yeo and Zhou conjectured after Theorem 3 of their 2023 paper that every sink-free digraph of maximum in-degree at most four has a small quasi-kernel. Reversing all arcs gives source-free digraphs of maximum out-degree at most four in our convention. `Q-4` proves the half-order bound for that class, and `Q-4-ALG` gives a polynomial-time construction using a fractional vertex cover. The 2023 paper already establishes the degree-three existence bound. [Ai et al., §2](https://doi.org/10.1016/j.disc.2023.113435) · [Degree-four proof in English](proofs/degree-four.md) · [Chinese proof](proofs/匹配降度与出度四的小准核.md) · [Polynomial-time construction](proofs/出度四的多项式构造.md)

### Clow’s Conjecture 5.1 · `Q-CLOW`

Let $S(v)$ be the sources left after deleting $v$ and its out-neighbours, and set $E(v)=N^+(v)\cup N^+(S(v))$. Clow asks for a vertex with $|E(v)|\ge |S(v)|+1$ in every nonempty source-free oriented graph of maximum out-degree at most three. The draft finds a single vertex $v$ satisfying $|N^+(v)\cup N^+(F)|\ge |F|+1$ for every $F\subseteq S(v)$, even when opposite arcs are allowed. [Clow, §5](https://arxiv.org/html/2601.11847v1#S5) · [Theorem 1](proofs/Clow-5.1-证明.md#主要结果)

### Clow’s Problems 5.2 and 5.3

**Problem 5.2, second question.** Let $f(d)$ be the least factor that guarantees $f(d)|E(v)|\ge |S(v)|+1$ at some vertex in every nonempty source-free oriented graph of maximum out-degree at most $d$. `Q-CLOW` and the directed four-cycle give $f(2)=f(3)=1$. A publicly available 24-vertex construction gives $f(4)\ge 5/4$. Together they determine the first degree with $f(d)>1$ to be **four**. The exact value of $f(4)$ remains open. [Clow, §5](https://arxiv.org/html/2601.11847v1#S5) · [24-vertex construction](https://rainwangphy.github.io/aftd-platform/blog/2026-11-03-arxiv-2601-11847/) · [Derivation](proofs/Clow-5.1-证明.md#对-clow-问题-52-和-53-的推论)

**Problem 5.3.** The draft gives a necessary condition for the local inequality to fail at every vertex of a nonempty source-free digraph. Every directed cycle must be able to reach a vertex of out-degree at least four. [Structural consequence](proofs/Clow-5.1-证明.md#对-clow-问题-52-和-53-的推论)

### An unbounded-out-degree case of Nguyen–Scott–Seymour’s Conjecture 3.1 · `Q-O1-BIP`, Theorem O1-R

Nguyen, Scott and Seymour’s Theorem 3.2 gives weighted half coverage for an oriented graph partitioned into a tournament and an acyclic part. O1-R allows a semicomplete core, with at least one arc between each pair, and an outer induced subgraph with no odd directed cycle. The outer part can contain directed even cycles and arbitrarily large strongly connected bipartite components, and arcs between the two parts are unrestricted. For every nonnegative vertex weighting, some quasi-kernel covers at least half the total weight within one step, counting the quasi-kernel itself. Weighted transfer gives the half-order bound when the graph is source-free. Ai et al. already obtained that bound for ordinary source-free break digraphs. [Nguyen–Scott–Seymour, §3](https://www.combinatorics.org/ojs/index.php/eljc/article/download/v33i1p32/pdf/) · [Weighted transfer](https://arxiv.org/abs/2610.23487) · [O1-R proof draft](proofs/半完全核心与二分外图的加权半支配定理.md)

## Further results and verification

The theorem index also covers the half-order bound through 24 vertices at arbitrary out-degree, the extension formula for sinks, and the strong local inequality and polynomial-time construction on class $\mathcal{H}$. The general small quasi-kernel conjecture remains open. [Theorem index](THEOREMS.md) · [Research status](STATE.md)

The Node.js checks for both degree-four partitions cover all 761,804 labelled source-free digraphs on two through five vertices. Lean checks finite instances, including the 24-vertex local obstruction. Run the commands from this repository root. [Computational checks](experiments/README.md) · [Lean verification](lean/README.md) · [Research index](INDEX.md)
