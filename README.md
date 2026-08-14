# TrustworthyKedlaya

Formalize the three target theorems in
`TrustworthyKedlaya/Kedlaya.lean` (task statement: `prompt.md`, frozen):

- `kedlaya_2001a_theorem15_half` — integral over F̄_p((t)) ⇔ S_{a,b,c}
  support + eventually periodic twist sequences ([Kedlaya2001a] Thm 15).
  **Fully proved** (upgraded from ⇒ to ⇔ with owner approval, I-0024).
- `kedlaya_2017_theorem13_4` — completed integral closure statement
  ([Kedlaya2017] Thm 13.4, part).
- `kedlaya_2001b_ordinal_bound` — support order type of a ℚ_p-algebraic p-adic
  Hahn series is ≤ ω^ω ([Kedlaya2001b] §4). **Fully proved.**

Everything is specialized to K = F̄_p; per [Kedlaya2017, §2] the 2001a theory
is valid in that case. The three target statements are protected (inbox
I-0001): never alter them, only replace `by admit` with kernel-checked proofs.
Target 2 (`kedlaya_2017_theorem13_4`) is the only remaining intentional
`admit`.

## Layout

- `TrustworthyKedlaya/` — Lean sources. Proof machinery sits below
  `Kedlaya.lean` in the import graph; `DefeqGuards.lean` pins restated
  definitions to the originals by `rfl` so drift breaks the build.
  `PAdicHahnSeries.lean`, `WittVector.lean`, `Miscellaneous.lean` are
  human-provided infrastructure.
- `blueprint/main.tex` — the math blueprint; `hgraph/` — the dependency graph.
- `scratch/` — committed numeric-evidence scripts and outputs from the target-2
  route-decision phase (numerics closed per I-0042); evidence, not library code.
- `prompt.md`, `refs/` — frozen task statement and source papers (read-only).
  The shared reference library is at the workspace root `references/`.

## Build

`lake build` from this directory. The library root `TrustworthyKedlaya.lean`
must import every module — a bare build only checks what the root reaches.
