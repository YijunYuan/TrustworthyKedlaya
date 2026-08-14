# TrustworthyKedlaya

![CI](https://github.com/YijunYuan/TrustworthyKedlaya/actions/workflows/lean_action_ci.yml/badge.svg)
[![Lean](https://img.shields.io/badge/Lean-4.33.0-5C2D91)](https://leanprover.github.io)
[![mathlib](https://img.shields.io/badge/mathlib-db584cd6d46c92f209a44c0f1c829460d327499d-5C2D91)](https://github.com/leanprover-community/mathlib4)

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

## Layout

- `TrustworthyKedlaya/` — Lean sources. Proof machinery sits below
  `Kedlaya.lean` in the import graph; `DefeqGuards.lean` pins restated
  definitions to the originals by `rfl` so drift breaks the build.
  `PAdicHahnSeries.lean`, `WittVector.lean`, `Miscellaneous.lean` are
  human-provided infrastructure.

## Build

`lake build` from this directory. The library root `TrustworthyKedlaya.lean`
must import every module — a bare build only checks what the root reaches.

## References
- K. S. Kedlaya, *Power series and p-adic algebraic closures*, J. Number Theory 89 (2001)
  [Ked01a].
- K. S. Kedlaya, *The algebraic closure of the power series field in positive characteristic*,
  Proc. Amer. Math. Soc. 129 (2001) [Ked01b].
- K. S. Kedlaya, *On the algebraicity of generalized power series*, Beiträge Algebra Geom. 58
  (2017) [Ked17].

## Author
- Yijun Yuan (human)
- [Archon-Horizen](https://github.com/frenzymath/Archon-Horizon) (Agentic system of [FrenzyMath](https://github.com/frenzymath))
- Claude Fable 5 (LLM of Anthropic, Inc.)