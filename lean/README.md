# Lean 形式化复核

从小准核仓库根目录运行 `lean lean/Clow51.lean`。仓库通过 [lean-toolchain](../lean-toolchain) 固定 Lean 4.29.0，使用 Elan 时会自动选择该版本。文件只用 Lean 核心库，使用 `decide +kernel`。

| Lean 声明 | 精确范围 |
| --- | --- |
| `cycle_family_3_to_40` | 环长 3–40 的唯一正值顶点与全图差值和 |
| `cycle_9`、`cycle_9_b`、`cycle_9_r` | 九点环例的差值与指定顶点的邻域数据 |
| `degreeFour_wellFormed`、`degreeFour_all_zero` | 一张 24 点出度四局部障碍的合格性及全部 $g=0$ |
| `core3_count`、`core3_min_two` | 文件所定义的三点核心枚举与最小正值点数 |

[Lean 源码](Clow51.lean)对应[唯一见证点构造](../history/Clow-5.1-构造.md)。任意环长、一般 Clow 5.1 和出度四半数界属于手工证明稿。
