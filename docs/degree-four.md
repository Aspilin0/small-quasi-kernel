# Small quasi-kernels in digraphs of maximum out-degree four

[Research index](../README.md) · [Chinese proof draft](../匹配降度与出度四的小准核.md)

**Theorem.** Every finite source-free simple digraph $D$ with $\Delta^+(D)\le 4$ has an independent set $Q$ from which every vertex is reachable by a directed path of length at most two, with $2|Q|\le |V(D)|$. Opposite arcs are allowed. For the empty graph, take $Q=\varnothing$.

Reversing all arcs gives the sink-free, maximum-in-degree-four formulation. Ai, Gerke, Gutin, Yeo and Zhou ask about that case in the discussion following Theorem 3, which implies the bound at maximum in-degree three. [Results on the small quasi-kernel conjecture](https://doi.org/10.1016/j.disc.2023.113435)

The proof uses the alternating-path decomposition and matching count of Ai, Gutin, Liu and Meng. The matching is chosen to maximize the number of pairs with a forward arc among all maximum matchings. This choice puts all the weight needed for the count on an induced subdigraph of maximum out-degree two. [Small and large quasi-kernels, Lemmas 2.1, 3.1 and 3.2](https://arxiv.org/html/2610.23487v1#S3)

## One-step coverage of a prescribed vertex set

Write $N^+(K)$ for the union of the out-neighbourhoods of the vertices of $K$, and $N^+[K]=K\cup N^+(K)$. In this proof a **kernel** is an independent set $K$ with $N^+[K]=V(D)$. A digraph is **kernel-perfect** if all its induced subdigraphs have kernels.

**Lemma 1.** If $D[T]$ is kernel-perfect, $D$ has a quasi-kernel $K$ with $T\subseteq N^+[K]$.

Start with $A=T$. Whenever a vertex $x\notin A$ receives no arc from $A$, add it to $A$. The added vertex is a source in $D[A\cup\{x\}]$. To find a kernel in any induced subdigraph containing this source, select the source and take a kernel of the subdigraph left after deleting it and its out-neighbours. Thus each addition preserves kernel-perfectness. At termination, every vertex outside $A$ receives an arc from $A$. A kernel $K$ of $D[A]$ reaches every vertex of $A$ in at most one step and every vertex of $D$ in at most two.

**Lemma 2.** The vertices of a simple digraph of maximum out-degree at most two can be partitioned into two sets, each inducing a kernel-perfect digraph.

Repeatedly delete any vertex whose current in-degree or out-degree is at most one. Once the remaining graph is partitioned, reinsert the deleted vertices in reverse order. A vertex with at most one in-neighbour can be assigned to a part in which it is a source. A vertex with at most one out-neighbour can be assigned to a part in which it is a sink. Adding a sink also preserves kernel-perfectness. Take a kernel of the induced subdigraph without the sink and add the sink if it is outside the kernel's closed out-neighbourhood.

In the remaining graph, every in-degree and out-degree is exactly two, since every in-degree is at least two, every out-degree is at most two, and their sums agree. Its underlying graph has maximum degree at most four. By Brooks' theorem every connected component other than $K_5$ admits a proper four-colouring. Group the first two colours and the last two colours. Each group has bipartite underlying graph, so each of its induced subdigraphs has no odd directed cycle and has a kernel by Richardson's theorem, with arcs reversed for our convention. If the underlying component is $K_5$, its ten arcs lie on ten distinct pairs, so it is a tournament. Put one vertex and its two out-neighbours in one part and the remaining two vertices in the other. Both induced subdigraphs are acyclic and therefore kernel-perfect. [Brooks' theorem](https://doi.org/10.1002/jgt.21847) · [Richardson's theorem in the out-neighbourhood convention](https://arxiv.org/html/2601.11847v1#S1)

For a nonnegative vertex weighting $f$, write $f(X)=\sum_{x\in X}f(x)$ and let $T$ be the set of vertices with positive weight. If $D[T]$ has maximum out-degree at most two, apply Lemma 1 to the heavier of the two parts given by Lemma 2. The resulting quasi-kernel $K$ of $D$ satisfies

$$f(N^+[K])\ge f(T)/2. \tag{1}$$

## Choosing a matching to lower the degree on the weight support

Take a maximum independent set $I_0$ of the underlying graph and set $C_0=V(D)\setminus I_0$. In the undirected bipartite graph of edges between $C_0$ and $I_0$, choose a maximum-cardinality matching $M$. Subject to that choice, maximize the number of matched pairs $ci$ with the arc $c\to i$, where $c\in C_0$ and $i\in I_0$. A pair carrying both arcs counts as forward.

Starting from every unmatched vertex of $C_0$, follow nonmatching edges from $C_0$ to $I_0$ and matching edges in the reverse direction. Let $A\subseteq C_0$ and $B\subseteq I_0$ be the sets reached. Put $H=A\cup B$, $C=C_0\setminus A$ and $I=I_0\setminus B$.

- There is no edge between $H$ and $I$. A nonmatching edge from $A$ leads to a vertex in $B$. The matching partner of any matched vertex in $A$ is the vertex in $B$ from which it was reached. There are no edges between $B$ and $I$ since both lie in $I_0$.
- Every vertex in $B$ is matched, since reaching an unmatched vertex there would give an augmenting path. The matching pairs those vertices with the matched vertices of $A$, and pairs every vertex in $C$ with a vertex in $I$.
- $\alpha(D[H])=|B|\le |H|/2$. The set $B$ is independent and matched into $A$. Any independent set in $H$ can be combined with $I$, so its size is at most $|I_0|-|I|=|B|$.

Let $U$ be the unmatched vertices in $I$. Every $x\in U$ has an in-neighbour because $D$ is source-free. All its in-neighbours lie in $C$, so choose one, denoted $p(x)$. Give each $c\in C$ weight $f(c)=|\{x\in U:p(x)=c\}|$ and every other vertex weight zero. Let $T=\{c:f(c)>0\}$.

For any $c\in T$, choose an $x\in U$ with $p(x)=c$, and let $m(c)\in I$ be the matching partner of $c$. If the arc $c\to m(c)$ were absent, replacing $cm(c)$ with $cx$ would preserve the cardinality of the matching while increasing the number of forward pairs. Thus $c\to m(c)$ and $c\to x$ are arcs to two distinct vertices outside $T$. It follows that

$$d^+_{D[T]}(c)\le d^+_D(c)-2\le 2. \tag{2}$$

By (1), there is a quasi-kernel $K$ of $D$ with $t=f(N^+[K])\ge |U|/2$. When $U=\varnothing$, Lemma 1 with $T=\varnothing$ gives a quasi-kernel and $t=0$.

## Converting coverage into a size bound

Let $C_+=\{c\in C:c\to m(c)\}$ and $C_-=C\setminus C_+$. Denote their respective sets of matching partners by $I_+$ and $I_-$. For $c\in C_-$ the arc $m(c)\to c$ exists. Set $b=|C_-|$, $c_+=|C_+\cap N^+[K]|$ and $c_-=|C_-\cap N^+[K]|$.

Keep all vertices of $K\setminus I$ and $K\cap I_-$. From the rest of $K$, add an inclusion-minimal set of vertices so that the resulting set $R\subseteq K$ satisfies $N^+(R)=N^+(K)$. Each added vertex has an out-neighbour reached by no other vertex of $R$, since otherwise that added vertex could be dropped. These out-neighbours are distinct and lie in $C$, since $I$ is independent and has no edges to $H$.

Each vertex of $K\cap I_-$ also has its matching partner as an out-neighbour in $C$. Those partners are distinct and cannot be the out-neighbours reserved for the added vertices. By independence, none of these out-neighbours are in $K\cap C$. We can therefore charge each vertex of $R\cap(C\cup I)$ to a distinct vertex in $C\cap N^+[K]$, using itself, its matching partner, or its reserved out-neighbour. Thus

$$|R|\le |K\cap H|+c_++c_-.$$

Let $Z=V(D)\setminus N^{\le 2}[R]$, where $N^{\le 2}[R]$ includes $R$ and all vertices reachable from it in at most two steps. All vertices outside $K$ are still covered, since $R$ has the same out-neighbours as $K$. Also $K\setminus I\subseteq R$. Hence $Z\subseteq K\cap I$ and $P=R\cup Z\subseteq K$ is a quasi-kernel. Three disjoint sets of vertices in $I$ are already covered by $R$ within two steps.

1. All $b$ vertices of $I_-$. Those in $K$ were kept in $R$, and the others lie outside $K$.
2. The $c_+$ matching partners of $C_+\cap N^+[K]$. Their matched vertices are still covered within one step from $R$ and have forward arcs to those partners.
3. The $t$ vertices $x\in U$ with $p(x)\in N^+[K]$. Each is reached via its assigned in-neighbour, which is still covered within one step from $R$.

Consequently $|Z|\le |I|-b-c_+-t$. Adding the bound for $|R|$ and using $c_-\le b$ and $|U|=|I|-|C|$ yields

$$
|P|\le |K\cap H|+|I|-t
\le \frac{|H|}{2}+|I|-\frac{|I|-|C|}{2}
=\frac{|V(D)|}{2}.
$$

This proves the theorem. The argument uses a maximum independent set. A polynomial-time construction at maximum out-degree four remains a separate question in this project.

## Corollary for weighted sink extensions

Let $G$ be a source-free core and let $0\le w_v\le 4-d_G^+(v)$ be integers. Attach $w_v$ private sinks to each $v$, each with $v$ as its sole in-neighbour. The resulting digraph is source-free with maximum out-degree at most four. Take a small quasi-kernel $P$ of this digraph and set $J=P\cap V(G)$. Since sinks have no outgoing arcs, $J$ is a quasi-kernel of $G$. For each $v\notin N_G^+[J]$, every private sink at $v$ must belong to $P$. Therefore

$$
2\left(|J|+\sum_{v\notin N_G^+[J]} w_v\right)
\le 2|P|\le |V(G)|+\sum_v w_v.
$$

## Sharpness, the degree-five obstacle, and verification

- The directed four-cycle has minimum quasi-kernel size two, so the factor $1/2$ is sharp.
- At maximum out-degree five, (2) only bounds the out-degree on $T$ by three. In the seven-vertex Paley tournament, each vertex has three out-neighbours that form a directed triangle. A transitive subtournament on four vertices would have a source with three transitively ordered out-neighbours, so none exists. Every kernel-perfect part must be transitive, since an induced directed triangle has no kernel. Thus two kernel-perfect parts cannot cover the tournament. To realize it as the weight support at degree five, attach two private sinks to each vertex, take all sinks as $I_0$ and match each tournament vertex to one of its private sinks. The unmatched sinks give every tournament vertex weight one. The resulting graph has a seven-vertex quasi-kernel.
- Run `node degree-four-verify.mjs` from the repository root. It replays the matching choice, one-step weight coverage and final quasi-kernel construction for 761,804 labelled source-free simple digraphs on two to five vertices. Of these, 268,721 have maximum out-degree exactly four. The program checks the resulting set against the definition on the full graph and independently computes the optimum on graphs of order at most four. It also replays the 15-vertex example whose weight support has underlying graph $K_5$ and a 24-vertex local obstruction. [Verification script](../degree-four-verify.mjs)
