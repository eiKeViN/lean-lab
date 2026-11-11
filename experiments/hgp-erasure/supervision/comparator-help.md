# Local Lean 4.33.1 comparator

The optional comparator compares declarations with a previously frozen Lean
challenge. Within the Lake project, use `lake env comparator <config.json>`.
This version expects an explicit `"enable_nanoda": false`. A minimal config is

```json
{"challenge_module":"Challenge","solution_module":"Solution","theorem_names":["theoremName"],"permitted_axioms":["propext","Classical.choice","Quot.sound"],"enable_nanoda":false}
```

Keep Challenge and Solution in separate modules accessible to Lake. This
runtime's inner Landlock is unavailable; the comparison is a functional check
inside the outer offline filesystem isolation. The toolchain also includes
leanchecker. Model sessions access the prepared binaries on PATH.
