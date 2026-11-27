/-!
# Clow 猜想 5.1：Lean 4 复核（仅用核心库，无需 Mathlib）

对应 `../history/Clow-5.1-构造.md`：
* 定义 S(v)、E(v)、g(v)，与 `../experiments/shared/clow-check.mjs` 的定义逐行对应；
* 合格图条件（非空、无源、无自环、无双向边、出度上界）；
* 环族（m = 3..40）中恰有一个点 g > 0，且全图差值之和为 3 - m；
* 最大出度 4 的 24 点图每点 g = 0；
* 全部 3 点核心上的接法穷举；其中正值点数最小值为 2。

所有定理由内核求值 (`decide +kernel`) 证明，不依赖 `native_decide`。
任意 m 的结论仍由 Markdown 中的手工论证给出，此处只覆盖有限范围。
-/

namespace Clow51

/-- 邻接表：`g[v]` 是 v 的出邻点表。 -/
abbrev Graph := Array (List Nat)

def out (g : Graph) (v : Nat) : List Nat := g.getD v []

def arc (g : Graph) (u v : Nat) : Bool := (out g u).contains v

def verts (g : Graph) : List Nat := List.range g.size

def noDup (l : List Nat) : Bool := l.eraseDups.length == l.length

/-- 合格图：非空、出度至多 `limit`、无重弧、无自环、无双向边、无源点。 -/
def wellFormed (limit : Nat) (g : Graph) : Bool :=
  0 < g.size &&
  (verts g).all fun v =>
    (out g v).length ≤ limit && noDup (out g v) &&
    (out g v).all (fun w => w < g.size && w != v && !arc g w v) &&
    (verts g).any (fun u => arc g u v)

/-- 删去 v 及其出邻点后，余图的源点集 S(v)。 -/
def srcs (g : Graph) (v : Nat) : List Nat :=
  let rest := (verts g).filter fun w => w != v && !arc g v w
  rest.filter fun w => !rest.any fun u => arc g u w

/-- E(v) = N⁺(v) ∪ N⁺(S(v))。 -/
def expand (g : Graph) (v : Nat) : List Nat :=
  (out g v ++ (srcs g v).flatMap (out g)).eraseDups

def gap (g : Graph) (v : Nat) : Int :=
  ((expand g v).length : Int) - ((srcs g v).length : Int)

def gaps (g : Graph) : List Int := (verts g).map (gap g)

def positives (g : Graph) : Nat := ((gaps g).filter (· > 0)).length

/-! ## 环族 -/

/-- 顶点 0=a, 1=b, 2,3,4=t₁,t₂,t₃, 5=z，环 r₀..r_{m-1} 从 6 开始。 -/
def cycleGraph (m : Nat) : Graph :=
  #[[1, 5], [2, 3, 4], [0], [0], [0], []] ++
    ((List.range m).map fun i => [0, 1, 6 + (i + 1) % m]).toArray

def cycleGaps (m : Nat) : List Int :=
  [0, 3, 0, 0, 0, 0] ++ List.replicate m (-1)

def cycleOk (m : Nat) : Bool :=
  wellFormed 3 (cycleGraph m) && gaps (cycleGraph m) == cycleGaps m &&
    positives (cycleGraph m) == 1 && (gaps (cycleGraph m)).sum == 3 - (m : Int)

/-- m = 3..40 全部通过（与 `clow-cycle.mjs` 范围一致）。 -/
theorem cycle_family_3_to_40 : ((List.range 38).all fun i => cycleOk (i + 3)) = true := by
  decide +kernel

theorem cycle_9 : gaps (cycleGraph 3) = [0, 3, 0, 0, 0, 0, -1, -1, -1] := by
  decide +kernel

/-- m = 3 时的 S、E 与文档表格一致（顶点 b=1）。 -/
theorem cycle_9_b : srcs (cycleGraph 3) 1 = [] ∧ expand (cycleGraph 3) 1 = [2, 3, 4] := by
  decide +kernel

theorem cycle_9_r : srcs (cycleGraph 3) 6 = [2, 3, 4, 5, 8] ∧
    expand (cycleGraph 3) 6 = [0, 1, 7, 6] := by
  decide +kernel

/-! ## 最大出度 4 的 24 点图 -/

def reference : List (List Nat) :=
  [[4,5],[3,7],[0,6],[2,4],[2,7],[1,6],[0,1],[3,5]]

def degreeFour : Graph :=
  ((reference.zipIdx.map fun (row, i) => row ++ [8 + 2 * i, 9 + 2 * i]) ++
    List.replicate 16 []).toArray

theorem degreeFour_wellFormed : wellFormed 4 degreeFour = true := by decide +kernel

theorem degreeFour_all_zero : gaps degreeFour = List.replicate 24 0 := by decide +kernel


/-! ## 3 点核心上的穷举

核心点之间每个无序点对取 缺边 / 单向 / 反向；保留每点入出度皆正者。
每个核心点至多带一条汇弧，标签 0 表示无，标签 k>0 表示汇点 `2+k`（同标签共用汇点）。
已用标签须构成 {1..k}，保证没有孤立汇点。 -/

def coreRows (k : Nat) : List (List Nat) :=
  let c := [k % 3, (k / 3) % 3, k / 9]
  let pairs : List (Nat × Nat) := [(0,1),(0,2),(1,2)]
  (List.range 3).map fun u =>
    (List.range 3).filter fun w =>
      (pairs.zip c).any fun ((a, b), t) =>
        (t == 1 && a == u && b == w) || (t == 2 && b == u && a == w)

def isCore (rows : List (List Nat)) : Bool :=
  (List.range 3).all fun v =>
    !(rows.getD v []).isEmpty && rows.any fun r => r.contains v

/-- 标签向量 `l`（每点 0..3）。 -/
def labels (j : Nat) : List Nat := [j % 4, (j / 4) % 4, j / 16]

def prefixUsed (l : List Nat) : Bool :=
  let top := l.foldl max 0
  (List.range top).all fun i => l.contains (i + 1)

def attach (rows : List (List Nat)) (l : List Nat) : Graph :=
  let top := l.foldl max 0
  let core := (List.range 3).map fun v =>
    rows.getD v [] ++ (if l.getD v 0 == 0 then [] else [2 + l.getD v 0])
  core.toArray ++ (List.replicate top ([] : List Nat)).toArray

/-- 全部合格接法下的最少正值点数。 -/
def coreMin : Nat :=
  let all := (List.range 27).flatMap fun k =>
    let rows := coreRows k
    if isCore rows then
      (List.range 64).filterMap fun j =>
        let l := labels j
        if prefixUsed l && wellFormed 3 (attach rows l) then
          some (positives (attach rows l))
        else none
    else []
  all.foldl min 100

def coreCount : Nat := ((List.range 27).filter fun k => isCore (coreRows k)).length

theorem core3_count : coreCount = 2 := by decide +kernel

theorem core3_min_two : coreMin = 2 := by decide +kernel

end Clow51
