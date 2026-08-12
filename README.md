# TrustworthyKedlaya

Formalize the three admitted theorems in
`TrustworthyKedlaya/Kedlaya.lean` (task statement: `prompt.md`, frozen):

- `kedlaya_2001a_theorem15_half` — integral over F̄_p((t)) ⇒ S_{a,b,c}
  support + eventually periodic twist sequences ([Kedlaya2001a] Thm 15, one half).
- `kedlaya_2017_theorem13_4` — completed integral closure statement
  ([Kedlaya2017] Thm 13.4, part).
- `kedlaya_2001b_ordinal_bound` — support order type of a ℚ-algebraic Hahn
  series is ≤ ω^ω ([Kedlaya2001b] §4).

Everything is specialized to K = F̄_p; per [Kedlaya2017, §2] the 2001a theory
is valid in that case. The three target statements are protected (inbox
I-0001): never alter them, only replace `by admit` with kernel-checked proofs.

## Layout

- `TrustworthyKedlaya/` — Lean sources. Proof machinery sits below
  `Kedlaya.lean` in the import graph; `DefeqGuards.lean` pins restated
  definitions to the originals by `rfl` so drift breaks the build.
  `PAdicHahnSeries.lean`, `WittVector.lean`, `Miscellaneous.lean` are
  human-provided infrastructure.
- `blueprint/main.tex` — the math blueprint; `hgraph/` — the dependency graph.
- `prompt.md`, `refs/` — frozen task statement and source papers (read-only).
  The shared reference library is at the workspace root `references/`.

## Build

`lake build` from this directory. The library root `TrustworthyKedlaya.lean`
must import every module — a bare build only checks what the root reaches.
