# Small quasi-kernel research

Use the [research index and verification commands](README.md) to find the relevant proof or experiment. The [Chinese index](README.zh-CN.md) links the original notes.

- Check each note's arc convention. Most results use paths from the quasi-kernel. `check.mjs` also provides a checker for paths towards it, used directly by the subdivision experiment.
- Keep finite enumeration and definition checks independent of the construction they are checking. Describe general results as proof drafts and state what the finite replays cover.
- Search the repository before adding a function or a graph rule. The shared Clow evaluators are in `clow-local.mjs`.
- Enable the staged-file size hook with `git config core.hooksPath .githooks`. If it rejects a file, split that file by topic or function and stage the parts before retrying.
