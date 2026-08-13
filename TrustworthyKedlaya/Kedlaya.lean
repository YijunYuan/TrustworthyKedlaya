/-
Copyright (c) 2026 Shanwen Wang, Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import TrustworthyKedlaya.PAdicHahnSeries
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.LaurentSeries
public import Mathlib.Topology.Defs.Basic
import TrustworthyKedlaya.SeparableUP
import TrustworthyKedlaya.UPAlgebraic
import TrustworthyKedlaya.AlgSupportBound

/-!
## Main statements

- `TrustworthyKedlaya.kedlaya_2001a_theorem15_half`: the integrality criterion for Hahn series
  over `𝔽̄_p((t))`, i.e. Kedlaya (2017), Theorem 11.11 (equivalently Kedlaya (2001a), Theorem 15).
- `TrustworthyKedlaya.kedlaya_2017_theorem13_4`: the description of the completed integral
  closure of `ℚᵘⁿ_[p]` in `𝕃_[p]`, i.e. Kedlaya (2017), Theorem 13.5.
- `TrustworthyKedlaya.kedlaya_2001b_ordinal_bound`: the ordinal bound `ω^ω` on the order type
  of the support of a `ℚ_[p]`-algebraic `p`-adic Hahn series, from Kedlaya (2001b), Section 4.

## Implementation notes

The statements still ending in `admit` are deliberately admitted; these are the only intentional
`admit`s in the project. They are external inputs, not gaps in our own arguments.
`kedlaya_2001a_theorem15_half` is fully proved, in both directions: its right-hand side is
definitionally `TrustworthyKedlaya.UP.IsUP` (pinned in `DefeqGuards.lean`), established for
integral elements in `TrustworthyKedlaya.SeparableUP` and, conversely, integral whenever it
holds by `TrustworthyKedlaya.UPAlgebraic`.

## References

- K. S. Kedlaya, *Power series and p-adic algebraic closures*, J. Number Theory 89 (2001)
  [Ked01a].
- K. S. Kedlaya, *The algebraic closure of the power series field in positive characteristic*,
  Proc. Amer. Math. Soc. 129 (2001) [Ked01b].
- K. S. Kedlaya, *On the algebraicity of generalized power series*, Beiträge Algebra Geom. 58
  (2017) [Ked17].
-/

@[expose] public section

namespace TrustworthyKedlaya

variable (p : ℕ) [Fact (Nat.Prime p)]

/-- The support set `S_{a,b,c}` of Kedlaya (2017), Definition 2.1.

For a positive integer `a`, an integer `b` and a nonnegative integer `c`,
`S_{a,b,c} = { (1/a) (n - ∑_{i≥1} bᵢ p^{-i}) : n ∈ ℤ, n ≥ -b, bᵢ ∈ {0,…,p-1}, ∑ bᵢ ≤ c }`.

The base-`p` digit sequence `(bᵢ)_{i≥1}` is modelled as a finitely-supported
`d : ℕ →₀ ℕ` (with `d i` the digit `b_{i+1}`), so the value
`∑ i, d i * p^{-(i+1)}` is a finite rational; the digit bound is `∑ i, d i ≤ c` and
each digit satisfies `d i < p`. Positivity of `a` is carried as a hypothesis where
needed (e.g. in `kedlaya_2001a_theorem15_half`). -/
def Sabc (a : ℕ+) (b c : ℕ) : Set ℚ :=
  { s : ℚ | ∃ (n : ℤ) (d : ℕ →₀ ℕ),
      -b ≤ n ∧ (∀ i, d i < p) ∧ (d.sum fun _ v => v) ≤ c ∧
      s = (1 / (a : ℚ)) *
        ((n : ℚ) - d.sum fun i v => (v : ℚ) * (p : ℚ) ^ (-(i + 1 : ℤ))) }

/-- The slice `T_c = S_{1,0,c} ∩ (-1, 0)` of Kedlaya (2017), Definition 2.3: the negative
rationals in `(-1, 0)` whose base-`p` expansion has digit sum at most `c`. These index
the twist inputs of the recurrence functions below. -/
def Tc (c : ℕ) : Set ℚ := Sabc p 1 0 c ∩ Set.Ioo (-1) 0

/-- The twist-input sequence `(cₙ)` of Kedlaya (2017), Definition 2.3, eq. (2.2).

For `f : ℚ → 𝔽̄_p`, a positive integer `j` and base-`p` digits `b : ℕ →₀ ℕ` (with
`b i` the digit `b_{i+1}`),
`cₙ = f( -∑_{i < j-1} bᵢ p^{-(i+1)}  −  p^{-n} · ∑_{i ≥ j-1} bᵢ p^{-(i+1)} )`.

The sign in front of the second sum is a **minus**: the published eq. (2.2) prints a plus, but
that is a typo, as corroborated by the paper's own Remark 2.7. We take `f : ℚ → 𝔽̄_p` rather than
`f : Tc p c → 𝔽̄_p` so that the theorem can compose it directly with the coefficient function
`f_m`; faithfulness of the domain `T_c` is part of the informal content and is recovered in
`kedlaya_2001a_theorem15_half` by restricting the digits via `c`. -/
def twistSeq (f : ℚ → 𝔽ᵃ_[p]) (j : ℕ) (b : ℕ →₀ ℕ) (n : ℕ) : 𝔽ᵃ_[p] :=
  f (-(∑ i ∈ Finset.range (j - 1), (b i : ℚ) * (p : ℚ) ^ (-(i + 1 : ℤ)))
     - (p : ℚ) ^ (-(n : ℤ)) *
        ∑ i ∈ b.support.filter (fun i => j - 1 ≤ i), (b i : ℚ) * (p : ℚ) ^ (-(i + 1 : ℤ)))

open LaurentSeries in
/-- The order-embedding `ℤ ↪ ℚ` of value groups induces the ring inclusion of the
integer-supported Hahn series `𝔽̄_p((t))` into `𝔽̄_p((t^ℚ))`. Its range is the subring
over which integrality is asserted in `kedlaya_2001a_theorem15_half`. -/
noncomputable def intHahnEmbedding :
    (𝔽ᵃ_[p])⸨X⸩ →+* HahnSeries ℚ (𝔽ᵃ_[p]) :=
  HahnSeries.embDomainRingHom (Int.castAddHom ℚ) Rat.intCast_injective
    (fun _ _ => by exact_mod_cast Int.cast_le)

open LaurentSeries in
/-- The `𝔽̄_p((t))`-algebra structure on `𝔽̄_p((t^ℚ))` induced by `intHahnEmbedding`. -/
noncomputable instance : Algebra (𝔽ᵃ_[p])⸨X⸩ (HahnSeries ℚ (𝔽ᵃ_[p])) :=
  (intHahnEmbedding p).toAlgebra

open LaurentSeries in
/-- **Kedlaya (2017), Theorem 11.11 = Kedlaya (2001a), Theorem 15** (named `_half` for
historical reasons; upgraded to the full equivalence per the owner's ruling in inbox
I-0024).

A series `x = ∑ᵢ xᵢ tⁱ ∈ 𝔽̄_p((t^ℚ))` is integral over `𝔽̄_p((t))` if and only if:

* (a) there exist `a, b, c` (with `a` a positive integer) such that the support of `x` is
  contained in `S_{a,b,c}`; and
* (b) for some (equivalently, any) such `a, b, c`, there exist `M, N` (with `N` a positive
  period) so that for every integer `m ≥ -b`, the function `f_m : T_c → 𝔽̄_p`,
  `f_m(z) = x_{(m+z)/a}`, has the property that every sequence `(cₙ)` of the form in
  `twistSeq` (built from `f_m`, with digit sum `≤ c`) becomes periodic of period `N` after
  at most `M` terms.

The forward direction is `TrustworthyKedlaya.UP.isUP_of_isIntegral`; the converse
(blueprint node `lem:up-algebraic`, needed for `kedlaya_2017_theorem13_4`) is
`TrustworthyKedlaya.UP.IsUP.isIntegral`.
-/
theorem kedlaya_2001a_theorem15_half (x : HahnSeries ℚ (𝔽ᵃ_[p])) :
    IsIntegral (𝔽ᵃ_[p])⸨X⸩ x
    ↔ ∃ a : ℕ+, ∃ b c : ℕ,
    ( -- (a) `x` is supported on some `S_{a,b,c}`.
      (x.support ⊆ Sabc p a b c) ∧
      -- (b) for any such `a,b,c`, the twist functions `f_m` are eventually periodic.
      (∃ M N : ℕ+ , ∀ m : ℤ, m ≥ - (b : ℤ) →
          let fm : ℚ → 𝔽ᵃ_[p] := fun z => x.coeff (((m : ℚ) + z) / (a : ℚ))
          ∀ (j : ℕ) (dig : ℕ →₀ ℕ), 0 < j → (∀ i, dig i < p) →
            (dig.sum fun _ v => v) ≤ c →
            ∀ n : ℕ, M ≤ n →
              twistSeq p fm j dig (n + N) = twistSeq p fm j dig n) ) :=
  ⟨fun hx => UP.isUP_of_isIntegral hx, fun hx => UP.IsUP.isIntegral hx⟩

open LaurentSeries in
/-- **Kedlaya (2017), Theorem 13.4.** The completion of the integral closure of `ℚᵘⁿ_[p]` in
`𝕃_[p]` coincides with the completion of the set of `p`-adic Hahn series whose coefficient function
arises from an algebraic element of `𝔽̄_p((t^ℚ))`. -/
theorem kedlaya_2017_theorem13_4 :
    closure (integralClosure ℚᵘⁿ_[p] 𝕃_[p]).carrier =
    closure { f : 𝕃_[p] | ∃ f' : HahnSeries ℚ (𝔽ᵃ_[p]), IsAlgebraic (𝔽ᵃ_[p])⸨X⸩ f' ∧
      (exists_canonical_expansion f).choose.val = f'.coeff }
    := by admit

open Ordinal in
/-- **Kedlaya (2001b), Section 4.** The order type of the support of a `ℚ_[p]`-algebraic `p`-adic
Hahn series is at most `ω^ω`. -/
theorem kedlaya_2001b_ordinal_bound (f : 𝕃_[p]) (hp : IsAlgebraic ℚ_[p] f) :
    typeLT f.support ≤ omega0 ^ omega0 :=
  pAdicHahnSeries.typeLT_support_le_of_isIntegral
    (pAdicHahnSeries.alg_QpUn_of_alg_Qp p f hp).isIntegral

end TrustworthyKedlaya
