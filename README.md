# The small quasi-kernel conjecture

[简体中文](README.zh-CN.md)

A **quasi-kernel** is an independent set $Q$ from which every vertex is reachable in at most two steps along directed arcs. The Erdős–Székely conjecture asks whether every finite source-free digraph has such a set of size at most half its order. We work with simple digraphs, allowing opposite arcs between distinct vertices. We use $\Delta^+$ for maximum out-degree. Some papers take paths towards $Q$ and assume the digraph is sink-free. Reversing all arcs converts between the two conventions. [Clow, *Greedily Constructing Small Quasi-Kernels*](https://arxiv.org/html/2601.11847v1#S1)

## The degree-four proof draft

The main proof draft establishes the half-order bound for $\Delta^+\le 4$, including graphs with sinks and graphs with no sinks. Among maximum matchings, it chooses one with the most matched pairs carrying a forward arc. As a result, the vertices that carry positive weight induce a digraph of maximum out-degree two. A quasi-kernel that covers at least half that weight within one step then yields a half-order quasi-kernel by matching counts. [Full proof in English](docs/degree-four.md) · [Chinese original](匹配降度与出度四的小准核.md)

The argument adapts the matching count of Ai, Gutin, Liu and Meng. Ai, Gerke, Gutin, Yeo and Zhou established the degree-three half-order bound and asked about degree four in their reversed-arc convention. The general small quasi-kernel conjecture remains open. The degree-four argument is available for independent review, and priority in the literature remains to be checked. [Results on the small quasi-kernel conjecture](https://doi.org/10.1016/j.disc.2023.113435) · [Weighted transfer theorem](https://arxiv.org/html/2610.23487v1#S3)

## Related results and experiments

| Topic | Result |
| --- | --- |
| Clow's local inequality at degree three | Delete $v$ and its out-neighbours and let $S(v)$ be the sources of the remaining digraph. The proof draft finds a single $v$ such that $\lvert N^+(v)\cup N^+(F)\rvert\ge \lvert F\rvert+1$ for every $F\subseteq S(v)$, including in digraphs with opposite arcs. [Proof draft in Chinese](Clow-5.1-证明.md) |
| Extending across sinks | After choosing a quasi-kernel of the non-sink core, add exactly the sinks that it cannot reach in two steps. This gives an exact minimization formula and lets a search for counterexamples restrict sinks to in-degree one. The note also derives a $\lfloor n/4\rfloor$ bound for finite covers of a particular eight-vertex core with arbitrary sinks attached. [Proof and examples in Chinese](小准核的汇点延拓与独立根归纳.md) |
| Local out-neighbourhood structure | The proof draft establishes the strong local inequality when every out-neighbourhood is semicomplete, even at unbounded out-degree. The verification scripts also check mixed degree and independence conditions and exhibit a 19-vertex oriented graph where the strengthened local gap is zero everywhere. That graph has a quasi-kernel of size two. [Structural results in Chinese](Clow-禁出星图与相图.md) · [Boundary examples and verifier](clow-classH-verify.mjs) |
| Covers and arc subdivision | There are arbitrarily large examples with exactly one vertex witnessing Clow's inequality. Cover experiments compare how two roots behave under the same choice of lift. A separate note proves that inserting two vertices on an arc can extend a fixed quasi-kernel and gives a one-vertex failure example. [Unique witness](Clow-5.1-构造.md) · [Cover construction](Clow-5.1-覆盖与选点.md) · [Cover compatibility](Clow-5.1-覆盖的相容性.md) · [Arc subdivision](细分一条弧.md) (Chinese) |

Clow's Conjecture 5.1 concerns the local inequality at degree three. Problem 5.2 asks about the local inequality at higher degrees. [Clow, Section 5](https://arxiv.org/html/2601.11847v1#S5)

## Reproduce the finite checks

Run these commands from the repository root. The JavaScript scripts use only the Node.js standard library and were checked with Node.js 24.

| Command | What it checks |
| --- | --- |
| `node degree-four-verify.mjs` | Replays the degree-four construction and checks the resulting quasi-kernel on every labelled source-free simple digraph on two to five vertices. The 761,804 graphs include 268,721 of maximum out-degree exactly four. |
| `node clow-proof-verify.mjs --full` | Checks degree-three witnesses, examples with opposite arcs, finite core enumerations, and the quasi-kernel construction. |
| `node sink-extension-verify.mjs` | Compares the sink extension formula with directly enumerated minima and replays the independent-root induction examples. |
| `node clow-k1d-verify.mjs` | Checks out-neighbourhood independence restrictions, local gaps, reductions, and finite examples. |
| `node clow-classH-verify.mjs` | Checks local witnesses and quasi-kernels under mixed degree and independence conditions and replays explicit counterexamples to the local criteria. |
| `node verify.mjs` | Checks 67,600 quasi-kernel extensions under arc subdivision. This experiment uses paths towards the quasi-kernel. |
| `lean lean/Clow51.lean` | Uses Lean 4's core library to check the finite family with cycle lengths 3 through 40, a 24-vertex local obstruction, and the three-vertex core enumeration. [Lean source](lean/Clow51.lean) |

## Open questions from the proof draft

- At degree four, can the half-order bound be made constructive in polynomial time? The proof uses a maximum independent set to define the matching.
- At degree five, can a quasi-kernel cover at least half the matching weight within one step? Only weight-one vertices can have three out-neighbours in the positive-weight support. The seven-vertex Paley tournament shows that the two-part kernel-perfect partition from the degree-four proof cannot cover every such support. [Degree-five obstacle](docs/degree-four.md#sharpness-the-degree-five-obstacle-and-verification)
