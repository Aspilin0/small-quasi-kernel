# 小准核计算复核

从 `small-quasi-kernel/` 的 Git 根目录运行。脚本仅用 Node.js 标准库，迁移复核使用 Node.js 24.17.0。

| ID | 命令 | 已覆盖的输入 |
| --- | --- | --- |
| Q-SUB | `node experiments/verify.mjs` | 67,600 次弧细分延拓及单点反例 |
| Q-4 | `node experiments/degree-four-verify.mjs` | 2–5 点共 761,804 张无源图，其中 268,721 张最大出度 4。2–4 点另枚举最小值 |
| Q-4-ALG | `node experiments/degree-four-verify.mjs --fractional` | 同一批图改用二部双覆盖分划，独立检查半权块的独立数上界和最终准核，含 15 点和 24 点指定例 |
| Q-WEIGHT | `node experiments/weighted-transfer-verify.mjs` | 32,768 张六点及 2,097,152 张七点带标号锦标赛，30,720 张相关八点延拓、多父点附接和 23 点实例 |
| Q-LB | `node experiments/layer-balance-verify.mjs` | 4 点全量 4,096 张有向图，8,200 张 $\Delta(\overline{G})\le 2$、6,050 张星林/混合补图，`Monster4` 与 7 点反例，6,400 张 $\alpha\le 2$ 极小极大抽检 |
| Q-CONFLUENT | `node experiments/confluent-reduction-verify.mjs` | 300 双向非邻核图（引理 A/B、定理 U1）、120 R6-约简 $\mathcal{C}_{\mathrm{SKP}}$（定理 U3）、23–29 点 Paley/$C_4$ 与含 $C_3$ 外图（定理 U4/U4$^*$）、300 $\mathrm{kp\text{-}del}\le 3$ 图（定理 U2$^*$）及显式边界与 $11/23$ 对偶证明 |
| Q-O1-BIP | `node experiments/semicomplete-bipartite-verify.mjs` | 200 双向分裂图、500 非二分无奇有向圈 $C_4/C_6$ 外图（`Ka_bipSCC` 分支）、300 双向团+$C_4$ 混拼图（`Ka_strictFree` 与 `Ka_bipSCC`）、30 张 23–29 点跨部 R6+$C_4$ 匹配支集图及 23/17/5 点边界例 |
| Q-CL-OBS | `node experiments/cl-peel-obstruction-verify.mjs` | `G_stair`、`AsymTrap`、双向 `Portal`、`BackupTournamentPortal(M=5,6)` 及纯竞赛图 `BackupPowerSetPortal(QR_7,QR_11)` 的独立准核与退化复核 |
| Q-CLOW / Q-IND | `node experiments/clow-proof-verify.mjs --full` | 2,000,202 个定向枚举实例、178,946 个允许双向边的枚举实例、5,000 个样本。省略 `--full` 可快速检查 |
| Q-SINK | `node experiments/sink-extension-verify.mjs` | 2,429 张图的直接最小值对照，15,289 次独立根延拓及显式边界 |
| Q-STAR | `node experiments/clow-k1d-verify.mjs` | 局部评分、约减及显式反例 |
| Q-H / Q-H-BOUND / Q-ALPHA | `node experiments/clow-classH-verify.mjs` | 图类 H 的局部见证、有限枚举与样本，18 点例的 $g$ 和 $L^*$，19/20/22 点例的 $g^+$，以及约简 |
| Q-UNIQUE | `node experiments/search/clow-cycle.mjs` | 环长 3–40。带参数 `3` 可输出邻接表并传给 `node experiments/shared/clow-check.mjs` |
| Q-COVER | `node experiments/search/clow-lifts.mjs`、`node experiments/search/clow-cover-search.mjs --six` | 特定提升、双根匹配与二重覆盖。省略 `--six` 时到五个非汇点 |
| 早期搜索 | `node experiments/search/clow-search.mjs`、`node experiments/search/clow-private-search.mjs --eight` | 小核心、有条件的私有汇点枚举。范围见[原笔记](../history/Clow-5.1-构造.md)及脚本 |

[check.mjs](shared/check.mjs) 按定义检查准核，[clow-check.mjs](shared/clow-check.mjs) 检查局部差值，[clow-local.mjs](shared/clow-local.mjs) 提供共享局部评估器。独立定义检查和构造保留不同入口。[Lean 复核](../lean/README.md) 单独运行。
