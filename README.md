# TrustworthyKedlaya

![CI](https://github.com/YijunYuan/TrustworthyKedlaya/actions/workflows/lean_action_ci.yml/badge.svg)
[![Lean](https://img.shields.io/badge/Lean-4.33.0-5C2D91)](https://leanprover.github.io)
[![mathlib](https://img.shields.io/badge/mathlib-db584cd6d46c92f209a44c0f1c829460d327499d-5C2D91)](https://github.com/leanprover-community/mathlib4)

Formalize the three target theorems in
`TrustworthyKedlaya/MainResults.lean`:

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

- `TrustworthyKedlaya/MainResults.lean` — the three target theorems above,
  together with the definitions they are stated in terms of (`Sabc`, `Tc`,
  `twistSeq`, …).
- `TrustworthyKedlaya/Lp/` — the base fields and the field `𝕃_[p]` of `p`-adic
  Hahn series with its basic theory (module prefix `TrustworthyKedlaya.Lp`).
  Base fields: `Miscellaneous.lean` (the `ℝ≥0`-valued absolute value used
  throughout), `QpCUn.lean` (the Witt-vector model of `ℤᶜᵘⁿ_[p]` / `ℚᶜᵘⁿ_[p]`),
  `QpUn.lean` (the maximal unramified extension `ℚᵘⁿ_[p] ⊆ ℚᶜᵘⁿ_[p]` and its
  maximality), `QpUnEmbedding.lean` (the tower
  `ℚ_[p] ⊆ ℚᵘⁿ_[p] ⊆ ℚᶜᵘⁿ_[p] ⊆ ℂ_[p]`, `ℚᵘⁿ_[p] → PadicAlgCl p ⊆ ℂ_[p]`,
  with all its compatibilities).
  `𝕃_[p]`: `Basic.lean` (definition, valuation, canonical expansion),
  `Coeff.lean` (coefficient calculus), `NewtonSlope.lean` (last Newton slope),
  `AlgClosed.lean` (algebraic closedness via the transfinite Newton algorithm),
  `Valued.lean` (complete valued/normed field), `Embedding.lean` (the isometric
  embedding `ℂ_[p] → 𝕃_[p]`, compatible with the structure map
  `ℚᶜᵘⁿ_[p] → 𝕃_[p]`). Nothing in `Lp/` imports `Kedlaya/`.
- `TrustworthyKedlaya/Kedlaya/` — the proof machinery for the main theorems
  (module prefix `TrustworthyKedlaya.Kedlaya`): UP series, Artin–Schreier and
  Galois towers, the Witt-carry/truncation engine, the steered Newton
  iteration, and the ordinal bound. Everything here sits below
  `MainResults.lean` in the import graph.

`Lp/Basic.lean`, `Lp/QpCUn.lean`, `Lp/QpUn.lean` and `Lp/Miscellaneous.lean`
are human-provided infrastructure.

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