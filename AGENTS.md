# 小准核研究

1. 先读 [STATE](STATE.md) 和 [INDEX](INDEX.md)，按 [定理依赖索引](THEOREMS.md) 只加载目标结果及直接前提。
2. 查 [定义与符号](theory/README.md) 确认可达方向、图类和符号，再打开对应证明分节。多数结果从准核沿出弧走，弧细分采用走向准核的约定。
3. 复核时先查 [计算入口](experiments/README.md) 或 [Lean 范围](lean/README.md)，然后运行与任务相关的命令。独立定义检查保持与构造程序分离。
4. 搜索新路线前查 [研究记录](history/README.md)。记录负结果的假设、适用范围、反例或搜索上限，并给出复核入口。

手工证明稿、有限计算、Lean 验证与开放问题分别标注。新增函数、规则或引理前先搜索。共享局部评估在 `experiments/shared/clow-local.mjs`。命令从本仓库根目录运行。

已配置的暂存文件大小钩子位于 `.githooks`。如需在新克隆中启用，运行 `git config core.hooksPath .githooks`。钩子拒绝文件时按主题或功能拆分。
