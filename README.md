# TrustworthyKedlaya

Formalize the three target theorems in
`TrustworthyKedlaya/Kedlaya.lean`:

- `kedlaya_2001a_theorem15` — integral over F̄_p((t)) ⇔ S_{a,b,c}
  support + eventually periodic twist sequences ([Kedlaya2001a] Thm 15).
  **Fully proved.**
- `kedlaya_2017_theorem13_4` — completed integral closure statement
  ([Kedlaya2017] Thm 13.4, part). **Fully proved.**
- `kedlaya_2001b_ordinal_bound` — support order type of a ℚ_p-algebraic p-adic
  Hahn series is ≤ ω^ω ([Kedlaya2001b] §4). **Fully proved.**

Everything is specialized to K = F̄_p; per [Kedlaya2017, §2] the 2001a theory
is valid in that case.

**Status (2026-08-14): COMPLETE.** All three targets are kernel-checked with
no `admit`/`sorry` and `lake build` is green. The target-2 reverse inclusion
follows the published proof of [Kedlaya2001b] Thm 7 part 2 (pp. 335–336):
p^k-th-root descaling plus Frobenius congruence amplification.

## Layout

- `TrustworthyKedlaya/` — Lean sources. Proof machinery sits below
  `Kedlaya.lean` in the import graph; `DefeqGuards.lean` pins restated
  definitions to the originals by `rfl` so drift breaks the build.
  `PAdicHahnSeries.lean`, `WittVector.lean`, `Miscellaneous.lean` are
  human-provided infrastructure.

## Build

`lake build` from this directory. The library root `TrustworthyKedlaya.lean`
must import every module — a bare build only checks what the root reaches.
