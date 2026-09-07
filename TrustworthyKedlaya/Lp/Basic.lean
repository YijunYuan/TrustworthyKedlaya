/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import TrustworthyKedlaya.Lp.QpCUn
public import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.RingTheory.HahnSeries.Multiplication
public import Mathlib.RingTheory.HahnSeries.Summable
public import Mathlib.RingTheory.WittVector.TeichmullerSeries

/-!
# The field `𝕃_[p]` of `p`-adic Hahn series

This file defines the field `𝕃_[p]` of `p`-adic Hahn series and develops its basic theory. Following
the paper, `𝕃_[p]` is realized as a quotient of the ring `W(𝔽ᵃ_[p])((t^ℚ))` of "lifted" Hahn series
by the ideal of **null series**, together with the resulting valuation, coefficient function, and
Teichmüller-style canonical expansion.

## Main definitions

- `TrustworthyKedlaya.LiftedPAdicHahnSeries` (`W(𝔽ᵃ_[p])((t^ℚ))`): Hahn series over `ℤᶜᵘⁿ_[p]` with
  value group `ℚ`.
- `TrustworthyKedlaya.LiftedPAdicHahnSeries.fromCoeff`: build a lifted Hahn series from a
  well-ordered-support coefficient function via `f ↦ ∑ₖ [f(k)] tᵏ`.
- `TrustworthyKedlaya.IsNullSeries`: the null-series condition `∀ g, ∑ₙ a_{g+n} pⁿ = 0`.
- `TrustworthyKedlaya.PAdicHahnSeries` (`𝕃_[p]`): the field of `p`-adic Hahn series, the quotient by
  the null-series ideal.

## Implementation notes

Since `WithVal` is a structure in this mathlib version, `𝕃_[p]` is no longer definitionally equal to
its underlying quotient; the bridge lemmas in this file mediate between the two representations.

## References

- S. Wang, Y. Yuan, *p-adic Hahn series with sparse support*.

## Tags

p-adic, Hahn series, null series, valuation, Teichmüller lift
-/

@[expose] public section

namespace TrustworthyKedlaya

open WittVector

/-- The ring `W(𝔽ᵃ_[p])((t^ℚ))` of "lifted" `p`-adic Hahn series: Hahn series over `ℤᶜᵘⁿ_[p]` with
value group `ℚ`. The field `𝕃_[p]` is a quotient of this ring by the null-series ideal. -/
abbrev LiftedPAdicHahnSeries (p : ℕ) [Fact (Nat.Prime p)] := HahnSeries ℚ (ℤᶜᵘⁿ_[p])
namespace LiftedPAdicHahnSeries
/-- Build a lifted Hahn series from a coefficient function `s : ℚ → 𝔽ᵃ_[p]` with well-ordered
support, via the Teichmüller lift `f ↦ ∑ₖ [f(k)] tᵏ`. -/
noncomputable def fromCoeff {p : ℕ} [Fact (Nat.Prime p)]
(s : ℚ → Fpbar p) (hspwo : (Function.support s).IsPWO) :
LiftedPAdicHahnSeries p where
  coeff := fun n => teichmuller p (s n)
  isPWO_support' := by
    suffices h : (Function.support fun n ↦ (teichmuller p) (s n)) = Function.support s by rwa [h]
    ext z
    simp only [Function.mem_support]
    refine Function.Injective.ne_iff' ?_ ?_
    · exact injective_teichmuller p
    · simp
end LiftedPAdicHahnSeries

/-- The set of integer shifts `n` with `g + n ≤ N` at which `x` has a nonzero coefficient is finite.
This finiteness witness indexes the partial sums appearing in the null-series condition. -/
abbrev finiteBelow {p : ℕ} [Fact (Nat.Prime p)] (x : LiftedPAdicHahnSeries p) (g : ℚ) (N : ℕ) :
  Set.Finite {n : ℤ | g + n ≤ N ∧ x.coeff (g + n) ≠ 0} := by
  by_cases hs : Set.Nonempty x.support
  · let m : ℚ := x.isWF_support.min hs
    have hsubset :
        {n : ℤ | g + n ≤ N ∧ x.coeff (g + n) ≠ 0} ⊆
          Set.Icc (⌈m - g⌉ : ℤ) ⌊(N : ℚ) - g⌋ := by
      intro n hn
      have hm_le : m ≤ g + n :=
        x.isWF_support.min_le hs <| (HahnSeries.mem_support x (g + n)).2 hn.2
      have hlower : (⌈m - g⌉ : ℤ) ≤ n := by
        apply Int.ceil_le.mpr
        rw [sub_le_iff_le_add]
        simpa [add_comm, add_left_comm, add_assoc] using hm_le
      have hupper : n ≤ ⌊(N : ℚ) - g⌋ := by
        apply Int.le_floor.mpr
        rw [le_sub_iff_add_le]
        simpa [add_comm, add_left_comm, add_assoc] using hn.1
      exact ⟨hlower, hupper⟩
    exact ((Set.finite_Icc (⌈m - g⌉ : ℤ) ⌊(N : ℚ) - g⌋).subset hsubset)
  · have hcoeff : ∀ q : ℚ, x.coeff q = 0 := by
      intro q
      by_contra hq
      exact hs ⟨q, (HahnSeries.mem_support x q).2 hq⟩
    have hset : {n : ℤ | g + n ≤ N ∧ x.coeff (g + n) ≠ 0} = ∅ := by
      ext n
      simp [hcoeff (g + n)]
    simp [hset]

open Topology Filter in
/-- An element `∑ₖ aₖ tᵏ` of `W(𝔽ᵃ_[p])((t^ℚ))` is a **null series** if for every `g : ℚ` the
partial sums `∑ₙ a_{g+n} pⁿ` converge to `0`. Null series form the ideal whose quotient is
`𝕃_[p]`. -/
def IsNullSeries {p : ℕ} [Fact (Nat.Prime p)] (x : LiftedPAdicHahnSeries p) : Prop :=
  ∀ g : ℚ, Filter.Tendsto (fun M => (∑ n : Set.Finite.toFinset (finiteBelow x g M),
      (p : QpCUn p) ^ n.val * algebraMap (OQpCUn p) (QpCUn p) (x.coeff (g + n)))) atTop (𝓝 0)

/-- The integer-bounded variant of `finiteBelow`: the set of shifts `n ≤ K` at which `x` has a
nonzero coefficient at `g + n` is finite. -/
abbrev finiteBelowInt {p : ℕ} [Fact (Nat.Prime p)]
    (x : LiftedPAdicHahnSeries p) (g : ℚ) (K : ℤ) :
    Set.Finite {n : ℤ | n ≤ K ∧ x.coeff (g + n) ≠ 0} := by
  by_cases hs : Set.Nonempty x.support
  · let m : ℚ := x.isWF_support.min hs
    have hsubset : {n : ℤ | n ≤ K ∧ x.coeff (g + n) ≠ 0} ⊆ Set.Icc (⌈m - g⌉ : ℤ) K := by
      intro n hn
      have hm_le : m ≤ g + n :=
        x.isWF_support.min_le hs <| (HahnSeries.mem_support x (g + n)).2 hn.2
      have hlower : (⌈m - g⌉ : ℤ) ≤ n := by
        apply Int.ceil_le.mpr
        rw [sub_le_iff_le_add]
        simpa [add_comm, add_left_comm, add_assoc] using hm_le
      exact ⟨hlower, hn.1⟩
    exact ((Set.finite_Icc (⌈m - g⌉ : ℤ) K).subset hsubset)
  · have hcoeff : ∀ q : ℚ, x.coeff q = 0 := by
      intro q
      by_contra hq
      exact hs ⟨q, (HahnSeries.mem_support x q).2 hq⟩
    have hset : {n : ℤ | n ≤ K ∧ x.coeff (g + n) ≠ 0} = ∅ := by
      ext n
      simp [hcoeff (g + n)]
    simp [hset]

/-- The partial sum `∑_{n ≤ K} a_{g+n} pⁿ` in `ℚᶜᵘⁿ_[p]` of the coefficients of `x` at shifts
`n ≤ K` above `g`. These partial sums are the finite truncations whose limit defines the
coefficient function on `𝕃_[p]`. -/
noncomputable def intPartial {p : ℕ} [Fact (Nat.Prime p)]
    (x : LiftedPAdicHahnSeries p) (g : ℚ) (K : ℤ) : QpCUn p :=
  ∑ n : Set.Finite.toFinset (finiteBelowInt x g K),
    (p : QpCUn p) ^ n.1 * algebraMap (OQpCUn p) (QpCUn p) (x.coeff (g + n))

-- The valuation of `p : QpCUn p` is `ofAdd(-1)`; a uniformizer fact reused throughout.
private lemma valued_v_p {p : ℕ} [Fact (Nat.Prime p)] :
    Valued.v ((p : QpCUn p)) =
      ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero _) := by
  rw [show ((p : QpCUn p)) = algebraMap (OQpCUn p) (QpCUn p) (p : OQpCUn p) from by
    push_cast; rfl]
  rw [QpCUn.valued_algebraMap]
  have hirr : Irreducible (p : OQpCUn p) := WittVector.irreducible p
  have hpe : (IsDiscreteValuationRing.maximalIdeal (OQpCUn p)).asIdeal =
      Ideal.span {(p : OQpCUn p)} := hirr.maximalIdeal_eq
  rw [IsDedekindDomain.HeightOneSpectrum.intValuation_singleton _
    (WittVector.p_nonzero p _) hpe]
  rfl

/-- The valuation of `(p : ℚᶜᵘⁿ_[p])^n` is `ofAdd(-n)` for integer `n`. -/
lemma valued_v_p_zpow {p : ℕ} [Fact (Nat.Prime p)] (n : ℤ) :
    Valued.v ((p : QpCUn p)^n) =
      ((Multiplicative.ofAdd (-n : ℤ) : Multiplicative ℤ) : WithZero _) := by
  have hzpow : Valued.v ((p : QpCUn p)^n) = (Valued.v ((p : QpCUn p)))^n :=
    map_zpow₀ Valued.v _ _
  rw [hzpow, valued_v_p, ← WithZero.coe_zpow]
  congr 1
  rw [← ofAdd_zsmul n (-1 : ℤ)]
  congr 1
  ring

-- A basic neighborhood of `0`: `{y | Valued.v y < c}` for `c ≠ 0`. In v4.31 the valued nhds
-- basis is phrased via the value group `ValueGroup₀`, so we exhibit the value-group class of
-- `(p : QpCUn p) ^ (-log c)`, whose valuation is `c`.
/-- The open ball `{y | v(y) < c}` around `0` is a neighbourhood of `0` in `ℚᶜᵘⁿ_[p]`, for any
nonzero threshold `c`. This packages the valuation topology's basic neighbourhood filter for use in
the null-series convergence arguments. -/
lemma mem_nhds_zero_v_lt {p : ℕ} [Fact (Nat.Prime p)]
    {c : WithZero (Multiplicative ℤ)} (hc : c ≠ 0) :
    {y : QpCUn p | Valued.v y < c} ∈ nhds (0 : QpCUn p) := by
  rw [Valued.mem_nhds]
  have hva : Valued.v ((p : QpCUn p) ^ (-(WithZero.log c))) = c := by
    rw [valued_v_p_zpow, neg_neg, ← WithZero.exp_eq_coe_ofAdd, WithZero.exp_log hc]
  have hane : Valued.v.restrict ((p : QpCUn p) ^ (-(WithZero.log c))) ≠ 0 := by
    rw [ne_eq, Valuation.restrict_eq_zero_iff, hva]; exact hc
  refine ⟨Units.mk0 (Valued.v.restrict ((p : QpCUn p) ^ (-(WithZero.log c)))) hane, ?_⟩
  intro y hy
  simp only [Set.mem_ofPred_eq] at hy ⊢
  rw [Valuation.restrict_lt_iff_lt_embedding, sub_zero, Units.val_mk0,
    Valuation.embedding_restrict, hva] at hy
  exact hy

-- Extraction counterpart of `mem_nhds_zero_v_lt`: from `U ∈ nhds 0` recover a valuation bound
-- `c ≠ 0` with `{y | Valued.v y < c} ⊆ U`.
private lemma exists_v_lt_subset {p : ℕ} [Fact (Nat.Prime p)] {U : Set (QpCUn p)}
    (hU : U ∈ nhds (0 : QpCUn p)) :
    ∃ c : WithZero (Multiplicative ℤ), c ≠ 0 ∧ {y : QpCUn p | Valued.v y < c} ⊆ U := by
  rw [Valued.mem_nhds] at hU
  obtain ⟨γ, hγ⟩ := hU
  refine ⟨MonoidWithZeroHom.ValueGroup₀.embedding γ.1,
    MonoidWithZeroHom.ValueGroup₀.embedding_unit_ne_zero γ, ?_⟩
  intro y hy
  apply hγ
  simp only [Set.mem_ofPred_eq] at hy ⊢
  rw [Valuation.restrict_lt_iff_lt_embedding, sub_zero]
  exact hy

-- Point version of `exists_v_lt_subset`: from `U ∈ nhds x` recover `c ≠ 0` with
-- `{y | Valued.v (y - x) < c} ⊆ U`.
private lemma exists_v_sub_lt_subset {p : ℕ} [Fact (Nat.Prime p)] {U : Set (QpCUn p)} {x : QpCUn p}
    (hU : U ∈ nhds x) :
    ∃ c : WithZero (Multiplicative ℤ), c ≠ 0 ∧ {y : QpCUn p | Valued.v (y - x) < c} ⊆ U := by
  rw [Valued.mem_nhds] at hU
  obtain ⟨γ, hγ⟩ := hU
  refine ⟨MonoidWithZeroHom.ValueGroup₀.embedding γ.1,
    MonoidWithZeroHom.ValueGroup₀.embedding_unit_ne_zero γ, ?_⟩
  intro y hy
  apply hγ
  simp only [Set.mem_ofPred_eq] at hy ⊢
  rw [Valuation.restrict_lt_iff_lt_embedding]
  exact hy

-- Construction counterpart of `exists_v_sub_lt_subset` from a witness: for `x w : QpCUn p` with
-- `Valued.v w = c ≠ 0`, the ball `{y | Valued.v (y - x) < c}` is a neighborhood of `x`. In v4.31
-- the nhds basis is phrased via `ValueGroup₀`, so we exhibit the value-group class of `w`.
private lemma mem_nhds_v_sub_lt {p : ℕ} [Fact (Nat.Prime p)] {x w : QpCUn p}
    {c : WithZero (Multiplicative ℤ)} (hc : c ≠ 0) (hw : Valued.v w = c) :
    {y : QpCUn p | Valued.v (y - x) < c} ∈ nhds x := by
  rw [Valued.mem_nhds]
  have hane : Valued.v.restrict w ≠ 0 := by
    rw [ne_eq, Valuation.restrict_eq_zero_iff, hw]; exact hc
  refine ⟨Units.mk0 (Valued.v.restrict w) hane, ?_⟩
  intro y hy
  simp only [Set.mem_ofPred_eq] at hy ⊢
  rw [Valuation.restrict_lt_iff_lt_embedding, Units.val_mk0,
    Valuation.embedding_restrict, hw] at hy
  exact hy

-- Per-term bound: for `a : OQpCUn p` and `n : ℤ`, `Valued.v (p^n · algMap a) ≤ ofAdd(-n)`.
private lemma valued_v_term_le {p : ℕ} [Fact (Nat.Prime p)] (a : OQpCUn p) (n : ℤ) :
    Valued.v ((p : QpCUn p)^n * algebraMap (OQpCUn p) (QpCUn p) a) ≤
      ((Multiplicative.ofAdd (-n : ℤ) : Multiplicative ℤ) : WithZero _) := by
  rw [Valuation.map_mul, valued_v_p_zpow]
  have h_alg : Valued.v (algebraMap (OQpCUn p) (QpCUn p) a) ≤ 1 :=
    (IsDiscreteValuationRing.maximalIdeal (OQpCUn p)).valuation_le_one a
  calc ((Multiplicative.ofAdd (-n : ℤ) : Multiplicative ℤ) : WithZero _) *
          Valued.v (algebraMap (OQpCUn p) (QpCUn p) a)
      ≤ ((Multiplicative.ofAdd (-n : ℤ) : Multiplicative ℤ) : WithZero _) * 1 :=
        mul_le_mul' (le_refl _) h_alg
    _ = ((Multiplicative.ofAdd (-n : ℤ) : Multiplicative ℤ) : WithZero _) := mul_one _

/-- For a unit `u : (ℤᶜᵘⁿ_[p])ˣ`, its image in `ℚᶜᵘⁿ_[p]` has valuation `1`. -/
lemma valued_v_algebraMap_unit_one {p : ℕ} [Fact (Nat.Prime p)] (u : (OQpCUn p)ˣ) :
    Valued.v (algebraMap (OQpCUn p) (QpCUn p) u.val) = 1 := by
  have h1 : Valued.v (algebraMap (OQpCUn p) (QpCUn p) u.val) ≤ 1 :=
    (IsDiscreteValuationRing.maximalIdeal (OQpCUn p)).valuation_le_one u.val
  have h2 : Valued.v (algebraMap (OQpCUn p) (QpCUn p) u.inv) ≤ 1 :=
    (IsDiscreteValuationRing.maximalIdeal (OQpCUn p)).valuation_le_one u.inv
  have h3 : Valued.v (algebraMap (OQpCUn p) (QpCUn p) u.val) *
            Valued.v (algebraMap (OQpCUn p) (QpCUn p) u.inv) = 1 := by
    rw [← Valuation.map_mul, ← map_mul, u.val_inv]; simp
  by_contra h_ne_one
  have h1_lt : Valued.v (algebraMap (OQpCUn p) (QpCUn p) u.val) < 1 :=
    lt_of_le_of_ne h1 h_ne_one
  have h_lt : Valued.v (algebraMap (OQpCUn p) (QpCUn p) u.val) *
            Valued.v (algebraMap (OQpCUn p) (QpCUn p) u.inv) < 1 := by
    calc
      Valued.v (algebraMap (OQpCUn p) (QpCUn p) u.val) *
          Valued.v (algebraMap (OQpCUn p) (QpCUn p) u.inv) ≤
          Valued.v (algebraMap (OQpCUn p) (QpCUn p) u.val) * 1 := mul_le_mul' (le_refl _) h2
      _ = Valued.v (algebraMap (OQpCUn p) (QpCUn p) u.val) := mul_one _
      _ < 1 := h1_lt
  rw [h3] at h_lt
  exact lt_irrefl _ h_lt

-- For `K ≤ K'`, the difference `intPartial K' - intPartial K` equals the sum over the
-- set-difference of the finiteBelowInt index sets.
private lemma intPartial_diff_eq_sdiff_sum {p : ℕ} [Fact (Nat.Prime p)]
    (x : LiftedPAdicHahnSeries p) (g : ℚ) (K K' : ℤ) (h : K ≤ K') :
    intPartial x g K' - intPartial x g K =
      ∑ n ∈ (Set.Finite.toFinset (finiteBelowInt x g K') \
              Set.Finite.toFinset (finiteBelowInt x g K)),
        (p : QpCUn p) ^ n * algebraMap (OQpCUn p) (QpCUn p) (x.coeff (g + n)) := by
  have hsub : Set.Finite.toFinset (finiteBelowInt x g K) ⊆
      Set.Finite.toFinset (finiteBelowInt x g K') := by
    intro n hn
    have hn_mem : n ∈ {n : ℤ | n ≤ K ∧ x.coeff (g + n) ≠ 0} :=
      (Set.Finite.mem_toFinset _).mp hn
    exact (Set.Finite.mem_toFinset _).mpr ⟨le_trans hn_mem.1 h, hn_mem.2⟩
  have e1 : intPartial x g K' = ∑ n ∈ Set.Finite.toFinset (finiteBelowInt x g K'),
      (p : QpCUn p) ^ n * algebraMap (OQpCUn p) (QpCUn p) (x.coeff (g + n)) :=
    Finset.sum_attach (s := Set.Finite.toFinset (finiteBelowInt x g K'))
      (f := fun m : ℤ => (p : QpCUn p) ^ m * algebraMap (OQpCUn p) (QpCUn p) (x.coeff (g + m)))
  have e2 : intPartial x g K = ∑ n ∈ Set.Finite.toFinset (finiteBelowInt x g K),
      (p : QpCUn p) ^ n * algebraMap (OQpCUn p) (QpCUn p) (x.coeff (g + n)) :=
    Finset.sum_attach (s := Set.Finite.toFinset (finiteBelowInt x g K))
      (f := fun m : ℤ => (p : QpCUn p) ^ m * algebraMap (OQpCUn p) (QpCUn p) (x.coeff (g + m)))
  rw [e1, e2, ← Finset.sum_sdiff hsub, add_sub_cancel_right]

-- **Helper 1** (partial_sum_cauchy): For `K₁ ≤ K₂`, the difference
-- `intPartial x g' K₂ - intPartial x g' K₁` has valuation `≤ ofAdd(-(K₁ + 1))`.
-- This is the "tail below K₁ is small" strict-ultrametric bound.
private lemma partial_sum_valuation_cauchy {p : ℕ} [Fact (Nat.Prime p)]
    (x : LiftedPAdicHahnSeries p) (g' : ℚ) (K₁ K₂ : ℤ) (h : K₁ ≤ K₂) :
    Valued.v (intPartial x g' K₂ - intPartial x g' K₁) ≤
      ((Multiplicative.ofAdd (-(K₁ + 1) : ℤ) : Multiplicative ℤ) : WithZero _) := by
  rw [intPartial_diff_eq_sdiff_sum x g' K₁ K₂ h]
  apply Valuation.map_sum_le
  intro n hn
  have hn_mem : n ∈ Set.Finite.toFinset (finiteBelowInt x g' K₂) ∧
      n ∉ Set.Finite.toFinset (finiteBelowInt x g' K₁) := Finset.mem_sdiff.mp hn
  have hn1 : n ≤ K₂ ∧ x.coeff (g' + n) ≠ 0 :=
    (Set.Finite.mem_toFinset (hs := finiteBelowInt x g' K₂)).mp hn_mem.1
  have hn2 : ¬ (n ≤ K₁ ∧ x.coeff (g' + n) ≠ 0) := by
    intro h'
    exact hn_mem.2 ((Set.Finite.mem_toFinset (hs := finiteBelowInt x g' K₁)).mpr h')
  have hn_gt : K₁ < n := by
    by_contra hle
    push Not at hle
    exact hn2 ⟨hle, hn1.2⟩
  have h1 := valued_v_term_le (x.coeff (g' + n)) n
  have h2 : ((Multiplicative.ofAdd (-n : ℤ) : Multiplicative ℤ) :
        WithZero (Multiplicative ℤ)) ≤
      ((Multiplicative.ofAdd (-(K₁ + 1) : ℤ) : Multiplicative ℤ) :
        WithZero (Multiplicative ℤ)) := by
    rw [WithZero.coe_le_coe]
    exact Multiplicative.ofAdd_le.mpr (by omega)
  exact h1.trans h2

-- The `IsNullSeries` partial sum at `(g, M)` (over `ℕ`) equals the `intPartial` at
-- `(g, ⌊M - g⌋)` (over `ℤ`). This is the key index-set realignment for translating
-- between the `ℕ`-atTop and `ℤ`-atTop framings.
private lemma partialSum_eq_intPartial {p : ℕ} [Fact (Nat.Prime p)]
    (x : LiftedPAdicHahnSeries p) (g : ℚ) (M : ℕ) :
    (∑ n : Set.Finite.toFinset (finiteBelow x g M),
        (p : QpCUn p) ^ n.val * algebraMap (OQpCUn p) (QpCUn p) (x.coeff (g + n))) =
      intPartial x g ⌊(M : ℚ) - g⌋ := by
  have hset_eq : Set.Finite.toFinset (finiteBelow x g M) =
      Set.Finite.toFinset (finiteBelowInt x g ⌊(M : ℚ) - g⌋) := by
    ext n
    simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hle, hne⟩
      refine ⟨?_, hne⟩
      have hcast : (n : ℚ) ≤ (M : ℚ) - g := by linarith
      exact Int.le_floor.mpr hcast
    · rintro ⟨hle, hne⟩
      refine ⟨?_, hne⟩
      have hfloor : ((⌊(M : ℚ) - g⌋ : ℤ) : ℚ) ≤ (M : ℚ) - g := Int.floor_le _
      have hcast : (n : ℚ) ≤ (⌊(M : ℚ) - g⌋ : ℤ) := by exact_mod_cast hle
      linarith
  unfold intPartial
  -- Both sides sum the same function over the same Finset (after rewriting).
  rw [show (∑ n : Set.Finite.toFinset (finiteBelow x g M),
        (p : QpCUn p) ^ n.val * algebraMap (OQpCUn p) (QpCUn p) (x.coeff (g + n))) =
      ∑ n ∈ Set.Finite.toFinset (finiteBelow x g M),
        (p : QpCUn p) ^ n * algebraMap (OQpCUn p) (QpCUn p) (x.coeff (g + n)) from
      Finset.sum_attach (s := Set.Finite.toFinset (finiteBelow x g M))
        (f := fun n : ℤ => (p : QpCUn p) ^ n *
          algebraMap (OQpCUn p) (QpCUn p) (x.coeff (g + n)))]
  rw [show (∑ n : Set.Finite.toFinset (finiteBelowInt x g ⌊(M : ℚ) - g⌋),
        (p : QpCUn p) ^ n.1 * algebraMap (OQpCUn p) (QpCUn p) (x.coeff (g + n))) =
      ∑ n ∈ Set.Finite.toFinset (finiteBelowInt x g ⌊(M : ℚ) - g⌋),
        (p : QpCUn p) ^ n * algebraMap (OQpCUn p) (QpCUn p) (x.coeff (g + n)) from
      Finset.sum_attach (s := Set.Finite.toFinset (finiteBelowInt x g ⌊(M : ℚ) - g⌋))
        (f := fun n : ℤ => (p : QpCUn p) ^ n *
          algebraMap (OQpCUn p) (QpCUn p) (x.coeff (g + n)))]
  rw [hset_eq]

-- **Helper 3** (null_series_tail_bound): for a null series `x`, the integer-cutoff
-- partial sum `intPartial x g K` has valuation `≤ ofAdd(-(K + 1))`. Proof: from
-- `IsNullSeries x` (via cofinality of `⌊M - g⌋` in `ℤ` as `M : ℕ → ∞`), pick `K' ≥ K`
-- with `Valued.v (intPartial x g K') < ofAdd(-(K + 2))`. Then by Helper 1 + ultrametric,
-- `Valued.v (intPartial x g K) ≤ ofAdd(-(K + 1))`.
private lemma null_series_tail_bound {p : ℕ} [Fact (Nat.Prime p)]
    {x : LiftedPAdicHahnSeries p} (hx : IsNullSeries x) (g : ℚ) (K : ℤ) :
    Valued.v (intPartial x g K) ≤
      ((Multiplicative.ofAdd (-(K + 1) : ℤ) : Multiplicative ℤ) : WithZero _) := by
  -- Step 1: from `IsNullSeries x` at `g`, take the basic neighborhood `Valued.v · < ofAdd(-(K+2))`
  -- and find an `M₀` with `Valued.v (partialSum x g M) < ofAdd(-(K+2))` for `M ≥ M₀`.
  have hnhds :
      {y : QpCUn p | Valued.v y <
          ((Multiplicative.ofAdd (-(K + 2) : ℤ) : Multiplicative ℤ) : WithZero _)} ∈
        nhds (0 : QpCUn p) :=
    mem_nhds_zero_v_lt WithZero.coe_ne_zero
  have hev_close : ∀ᶠ M : ℕ in Filter.atTop,
      Valued.v (∑ n : Set.Finite.toFinset (finiteBelow x g M),
          (p : QpCUn p) ^ n.val * algebraMap (OQpCUn p) (QpCUn p) (x.coeff (g + n))) <
        ((Multiplicative.ofAdd (-(K + 2) : ℤ) : Multiplicative ℤ) : WithZero _) :=
    hx g hnhds
  -- Step 2: also require `⌊M - g⌋ ≥ K` (so that intPartial at K' := ⌊M-g⌋ is "deeper" than K).
  have hev_floor : ∀ᶠ M : ℕ in Filter.atTop, K ≤ ⌊(M : ℚ) - g⌋ := by
    -- For M large, ⌊M - g⌋ ≥ K. Equivalent to M - g ≥ K, i.e., M ≥ K + g.
    -- Pick M ≥ ⌈K + g⌉₊ + 1 (enough that ⌊M - g⌋ ≥ K).
    have h_int : ∀ᶠ M : ℕ in Filter.atTop, ⌈(K : ℚ) + g⌉₊ ≤ M :=
      Filter.eventually_ge_atTop ⌈(K : ℚ) + g⌉₊
    filter_upwards [h_int] with M hM
    have h1 : ((K : ℚ) + g) ≤ (⌈(K : ℚ) + g⌉₊ : ℚ) := Nat.le_ceil _
    have h2 : ((⌈(K : ℚ) + g⌉₊ : ℕ) : ℚ) ≤ (M : ℚ) := by exact_mod_cast hM
    have h3 : (K : ℚ) ≤ (M : ℚ) - g := by linarith
    exact Int.le_floor.mpr h3
  obtain ⟨M, hMle, hMfloor⟩ := (hev_close.and hev_floor).exists
  -- Step 3: rewrite `partialSum x g M` as `intPartial x g ⌊M - g⌋` to get a `ℤ`-form bound.
  set K' : ℤ := ⌊(M : ℚ) - g⌋ with hK'_def
  have hK'ge : K ≤ K' := hMfloor
  have hpartial_eq := partialSum_eq_intPartial x g M
  rw [hK'_def.symm] at hpartial_eq
  rw [hpartial_eq] at hMle
  -- Now: `Valued.v (intPartial x g K') < ofAdd(-(K+2))` and `K ≤ K'`.
  -- Step 4: combine with Helper 1 via ultrametric to get bound on `intPartial x g K`.
  have hcauchy := partial_sum_valuation_cauchy x g K K' hK'ge
  -- hcauchy : Valued.v (intPartial x g K' - intPartial x g K) ≤ ofAdd(-(K+1))
  have hsplit : intPartial x g K = intPartial x g K' - (intPartial x g K' - intPartial x g K) := by
    ring
  rw [hsplit]
  -- Use ultrametric: Valued.v (a - b) ≤ max (Valued.v a) (Valued.v b)
  -- We have Valued.v (intPartial K') < ofAdd(-(K+2)) ≤ ofAdd(-(K+1))
  -- and Valued.v (intPartial K' - intPartial K) ≤ ofAdd(-(K+1)).
  have h1 : Valued.v (intPartial x g K') ≤
      ((Multiplicative.ofAdd (-(K + 1) : ℤ) : Multiplicative ℤ) : WithZero _) := by
    have h_le : ((Multiplicative.ofAdd (-(K + 2) : ℤ) : Multiplicative ℤ) :
          WithZero (Multiplicative ℤ)) ≤
        ((Multiplicative.ofAdd (-(K + 1) : ℤ) : Multiplicative ℤ) :
          WithZero (Multiplicative ℤ)) := by
      rw [WithZero.coe_le_coe]
      exact Multiplicative.ofAdd_le.mpr (by omega)
    exact le_trans (le_of_lt hMle) h_le
  -- For Valued.v (a - b), the rule is `Valuation.map_sub_le_max` or similar.
  -- Valued.v (a - b) ≤ max (Valued.v a) (Valued.v b)
  calc Valued.v (intPartial x g K' - (intPartial x g K' - intPartial x g K))
      ≤ max (Valued.v (intPartial x g K'))
            (Valued.v (intPartial x g K' - intPartial x g K)) :=
        Valuation.map_sub Valued.v _ _
    _ ≤ ((Multiplicative.ofAdd (-(K + 1) : ℤ) : Multiplicative ℤ) : WithZero _) :=
        max_le h1 hcauchy

-- The integer set `{n : ℤ | n ≤ K, g + n ∈ s}` is finite for a PWO set `s ⊆ ℚ`.
-- Argument: if `s` is empty, trivial. Else `s` has min `q_min`, so `g + n ≥ q_min`,
-- hence `n ≥ ⌈q_min - g⌉`, giving a finite integer interval.
private lemma finite_int_in_pwo_below {s : Set ℚ} (hs : s.IsPWO) (g : ℚ) (K : ℤ) :
    {n : ℤ | n ≤ K ∧ g + (n : ℚ) ∈ s}.Finite := by
  by_cases hs_ne : s.Nonempty
  · let q_min : ℚ := hs.isWF.min hs_ne
    have hbound : {n : ℤ | n ≤ K ∧ g + (n : ℚ) ∈ s} ⊆ Set.Icc ⌈q_min - g⌉ K := by
      intro n hn
      have hge : q_min ≤ g + (n : ℚ) := hs.isWF.min_le hs_ne hn.2
      have hncast : (q_min - g : ℚ) ≤ (n : ℚ) := by linarith
      refine ⟨?_, hn.1⟩
      exact Int.ceil_le.mpr hncast
    exact (Set.finite_Icc _ _).subset hbound
  · have hempty : {n : ℤ | n ≤ K ∧ g + (n : ℚ) ∈ s} = ∅ := by
      ext n
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
      intro _ hg
      exact (hs_ne ⟨g + n, hg⟩).elim
    rw [hempty]
    exact Set.finite_empty

-- **Bound for `intPartial (c*x) g K`** — the key lemma feeding the main proof.
-- Strategy: expand `(c*x).coeff(g+n)` via `HahnSeries.coeff_mul`, reindex by
-- `(a, n)` instead of `(n, (a, b))` (with `b = g - a + n` implicit), group by `a`,
-- recognize the inner sum as `intPartial x (g - a) K`, apply ultrametric + Helper 3.
private lemma intPartial_mul_valuation_bound {p : ℕ} [Fact (Nat.Prime p)]
    (c x : LiftedPAdicHahnSeries p) (hx : IsNullSeries x) (g : ℚ) (K : ℤ) :
    Valued.v (intPartial (c * x) g K) ≤
      ((Multiplicative.ofAdd (-(K + 1) : ℤ) : Multiplicative ℤ) : WithZero _) := by
  open Pointwise in
  -- Step 1: extended outer index set `OuterExt = {n ≤ K : antidiag(g+n) ≠ ∅}`,
  -- equivalently `{n ≤ K : g + n ∈ c.supp + x.supp}`.
  have h_sum_pwo : (c.support + x.support).IsPWO := c.isPWO_support.add x.isPWO_support
  have h_outer_ext_finite :
      {n : ℤ | n ≤ K ∧ g + (n : ℚ) ∈ c.support + x.support}.Finite :=
    finite_int_in_pwo_below h_sum_pwo g K
  let OuterExt : Finset ℤ := h_outer_ext_finite.toFinset
  have hOuterExt_mem : ∀ n : ℤ, n ∈ OuterExt ↔
      n ≤ K ∧ g + (n : ℚ) ∈ c.support + x.support := by
    intro n
    exact Set.Finite.mem_toFinset _
  -- Step 2: rewrite `intPartial (c*x) g K` as a sum over `OuterExt`.
  have h_outer_sub : Set.Finite.toFinset (finiteBelowInt (c * x) g K) ⊆ OuterExt := by
    intro n hn
    have hn_data : n ≤ K ∧ (c * x).coeff (g + n) ≠ 0 :=
      (Set.Finite.mem_toFinset (hs := finiteBelowInt (c * x) g K)).mp hn
    have hcoeff_ne := hn_data.2
    have hsupp : g + (n : ℚ) ∈ (c * x).support := (HahnSeries.mem_support _ _).mpr hcoeff_ne
    have hsubset : (c * x).support ⊆ c.support + x.support := HahnSeries.support_mul_subset
    exact (hOuterExt_mem n).mpr ⟨hn_data.1, hsubset hsupp⟩
  have h_intPartial_attach : intPartial (c * x) g K =
      ∑ n ∈ Set.Finite.toFinset (finiteBelowInt (c * x) g K),
        (p : QpCUn p) ^ n * algebraMap (OQpCUn p) (QpCUn p) ((c * x).coeff (g + n)) :=
    Finset.sum_attach (s := Set.Finite.toFinset (finiteBelowInt (c * x) g K))
      (f := fun n : ℤ => (p : QpCUn p) ^ n *
        algebraMap (OQpCUn p) (QpCUn p) ((c * x).coeff (g + n)))
  have h_extend_eq : intPartial (c * x) g K =
      ∑ n ∈ OuterExt, (p : QpCUn p) ^ n *
        algebraMap (OQpCUn p) (QpCUn p) ((c * x).coeff (g + n)) := by
    rw [h_intPartial_attach]
    apply Finset.sum_subset h_outer_sub
    intro n hn_outer hn_orig
    have h_ext_data : n ≤ K ∧ g + (n : ℚ) ∈ c.support + x.support :=
      (hOuterExt_mem n).mp hn_outer
    have h_ne_orig : ¬ (n ≤ K ∧ (c * x).coeff (g + n) ≠ 0) := by
      intro h
      exact hn_orig ((Set.Finite.mem_toFinset (hs := finiteBelowInt (c * x) g K)).mpr h)
    have hcx_zero : (c * x).coeff (g + n) = 0 := by
      by_contra hne
      exact h_ne_orig ⟨h_ext_data.1, hne⟩
    rw [hcx_zero, map_zero, mul_zero]
  -- Step 3: For each `n ∈ OuterExt`, expand `(c*x).coeff(g+n)` via `coeff_mul`.
  have h_expand : ∀ n ∈ OuterExt,
      (p : QpCUn p) ^ n * algebraMap (OQpCUn p) (QpCUn p) ((c * x).coeff (g + n)) =
        ∑ ab ∈ Finset.antidiagonal c.isPWO_support x.isPWO_support (g + (n : ℚ)),
          (p : QpCUn p) ^ n *
            (algebraMap (OQpCUn p) (QpCUn p) (c.coeff ab.1) *
              algebraMap (OQpCUn p) (QpCUn p) (x.coeff ab.2)) := by
    intro n _
    rw [HahnSeries.coeff_mul, map_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ab _
    rw [map_mul]
  rw [h_extend_eq, Finset.sum_congr rfl h_expand]
  -- Step 4: convert the double sum to a single sum over a sigma type, then reindex.
  have h_sigma_eq := Finset.sum_sigma (s := OuterExt)
        (t := fun n => Finset.antidiagonal c.isPWO_support x.isPWO_support (g + (n : ℚ)))
        (f := fun p_sig : Sigma (fun _ : ℤ => ℚ × ℚ) => (p : QpCUn p) ^ p_sig.1 *
          (algebraMap (OQpCUn p) (QpCUn p) (c.coeff p_sig.2.1) *
            algebraMap (OQpCUn p) (QpCUn p) (x.coeff p_sig.2.2)))
  rw [← h_sigma_eq]
  -- Step 5: reindex via the bijection `(n, (a, b)) ↦ (a, n)` (b = g - a + n implicit).
  let Triples : Finset (Sigma (fun _ : ℤ => ℚ × ℚ)) :=
    OuterExt.sigma (fun n => Finset.antidiagonal c.isPWO_support x.isPWO_support
      (g + (n : ℚ)))
  let AOf : Finset ℚ := Triples.image (fun s => s.2.1)
  have h_fubini : (∑ p_sig ∈ Triples,
        (p : QpCUn p) ^ p_sig.1 *
          (algebraMap (OQpCUn p) (QpCUn p) (c.coeff p_sig.2.1) *
            algebraMap (OQpCUn p) (QpCUn p) (x.coeff p_sig.2.2))) =
      ∑ a ∈ AOf, algebraMap (OQpCUn p) (QpCUn p) (c.coeff a) *
        intPartial x (g - a) K := by
    rw [show (∑ a ∈ AOf, algebraMap (OQpCUn p) (QpCUn p) (c.coeff a) *
          intPartial x (g - a) K) =
        ∑ a ∈ AOf, algebraMap (OQpCUn p) (QpCUn p) (c.coeff a) *
          ∑ n ∈ Set.Finite.toFinset (finiteBelowInt x (g - a) K),
            (p : QpCUn p) ^ n * algebraMap (OQpCUn p) (QpCUn p) (x.coeff (g - a + n)) from by
      apply Finset.sum_congr rfl
      intro a _
      congr 1
      exact Finset.sum_attach (s := Set.Finite.toFinset (finiteBelowInt x (g - a) K))
        (f := fun n : ℤ => (p : QpCUn p) ^ n *
          algebraMap (OQpCUn p) (QpCUn p) (x.coeff (g - a + n)))]
    rw [show (∑ a ∈ AOf, algebraMap (OQpCUn p) (QpCUn p) (c.coeff a) *
          ∑ n ∈ Set.Finite.toFinset (finiteBelowInt x (g - a) K),
            (p : QpCUn p) ^ n * algebraMap (OQpCUn p) (QpCUn p) (x.coeff (g - a + n))) =
        ∑ a ∈ AOf, ∑ n ∈ Set.Finite.toFinset (finiteBelowInt x (g - a) K),
            (p : QpCUn p) ^ n * (algebraMap (OQpCUn p) (QpCUn p) (c.coeff a) *
              algebraMap (OQpCUn p) (QpCUn p) (x.coeff (g - a + n))) from by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _
      ring]
    have h_sigma_eq2 := Finset.sum_sigma (s := AOf)
      (t := fun a => Set.Finite.toFinset (finiteBelowInt x (g - a) K))
      (f := fun p_sig : Sigma (fun _ : ℚ => ℤ) =>
        (p : QpCUn p) ^ p_sig.2 *
          (algebraMap (OQpCUn p) (QpCUn p) (c.coeff p_sig.1) *
            algebraMap (OQpCUn p) (QpCUn p) (x.coeff (g - p_sig.1 + p_sig.2))))
    rw [← h_sigma_eq2]
    refine Finset.sum_bij
      (fun s _ => ⟨s.2.1, s.1⟩)
      ?_ ?_ ?_ ?_
    · intro s hs
      have hs_data := Finset.mem_sigma.mp hs
      have h_outer_data : s.1 ≤ K ∧ g + (s.1 : ℚ) ∈ c.support + x.support :=
        (hOuterExt_mem s.1).mp hs_data.1
      have h_anti_data : s.2.1 ∈ c.support ∧ s.2.2 ∈ x.support ∧ s.2.1 + s.2.2 = g + s.1 :=
        Finset.mem_antidiagonal.mp hs_data.2
      refine Finset.mem_sigma.mpr ⟨?_, ?_⟩
      · exact Finset.mem_image.mpr ⟨s, hs, rfl⟩
      · refine (Set.Finite.mem_toFinset (hs := finiteBelowInt x (g - s.2.1) K)).mpr
            ⟨h_outer_data.1, ?_⟩
        have hb_eq : g - s.2.1 + (s.1 : ℚ) = s.2.2 := by linarith [h_anti_data.2.2]
        rw [hb_eq]
        exact (HahnSeries.mem_support _ _).mp h_anti_data.2.1
    · intro s₁ hs₁ s₂ hs₂ h_eq
      have hs₁_data := Finset.mem_sigma.mp hs₁
      have hs₂_data := Finset.mem_sigma.mp hs₂
      have h_anti_data₁ := Finset.mem_antidiagonal.mp hs₁_data.2
      have h_anti_data₂ := Finset.mem_antidiagonal.mp hs₂_data.2
      have h_a_eq : s₁.2.1 = s₂.2.1 := (Sigma.mk.inj_iff.mp h_eq).1
      have h_n_eq : s₁.1 = s₂.1 := by
        have h := (Sigma.mk.inj_iff.mp h_eq).2
        -- h is a HEq, but the underlying types are both ℤ.
        exact eq_of_heq h
      have h_b_eq : s₁.2.2 = s₂.2.2 := by
        have h1 : s₁.2.1 + s₁.2.2 = g + s₁.1 := h_anti_data₁.2.2
        have h2 : s₂.2.1 + s₂.2.2 = g + s₂.1 := h_anti_data₂.2.2
        rw [h_a_eq, h_n_eq] at h1
        linarith
      cases s₁ with
      | mk fst snd =>
        cases s₂ with
        | mk fst' snd' =>
          cases snd with
          | mk a b =>
            cases snd' with
            | mk a' b' =>
              simp only at h_a_eq h_n_eq h_b_eq
              subst h_a_eq h_n_eq h_b_eq
              rfl
    · intro t ht
      have ht_data := Finset.mem_sigma.mp ht
      have ht_a_in : t.1 ∈ AOf := ht_data.1
      have ht_n_data : t.2 ≤ K ∧ x.coeff (g - t.1 + t.2) ≠ 0 :=
        (Set.Finite.mem_toFinset (hs := finiteBelowInt x (g - t.1) K)).mp ht_data.2
      obtain ⟨s_orig, hs_orig, hs_eq⟩ := Finset.mem_image.mp ht_a_in
      have hs_orig_data := Finset.mem_sigma.mp hs_orig
      have h_anti_orig := Finset.mem_antidiagonal.mp hs_orig_data.2
      have ha_in_supp : t.1 ∈ c.support := hs_eq ▸ h_anti_orig.1
      let b : ℚ := g - t.1 + (t.2 : ℚ)
      have hb_in_supp : b ∈ x.support := (HahnSeries.mem_support _ _).mpr ht_n_data.2
      have hab_sum : t.1 + b = g + (t.2 : ℚ) := by simp [b]; ring
      have hn_outer : t.2 ∈ OuterExt := by
        refine (hOuterExt_mem t.2).mpr ⟨ht_n_data.1, ?_⟩
        exact ⟨t.1, ha_in_supp, b, hb_in_supp, hab_sum⟩
      refine ⟨⟨t.2, t.1, b⟩, ?_, ?_⟩
      · refine Finset.mem_sigma.mpr ⟨hn_outer, ?_⟩
        exact Finset.mem_antidiagonal.mpr ⟨ha_in_supp, hb_in_supp, hab_sum⟩
      · rfl
    · intro s hs
      have hs_data := Finset.mem_sigma.mp hs
      have h_anti_data := Finset.mem_antidiagonal.mp hs_data.2
      have hb_eq : g - s.2.1 + (s.1 : ℚ) = s.2.2 := by linarith [h_anti_data.2.2]
      simp only [hb_eq]
  rw [h_fubini]
  -- Step 6: apply ultrametric and Helper 3.
  apply Valuation.map_sum_le
  intro a ha
  rw [Valuation.map_mul]
  have h_alg_le : Valued.v (algebraMap (OQpCUn p) (QpCUn p) (c.coeff a)) ≤ 1 :=
    (IsDiscreteValuationRing.maximalIdeal (OQpCUn p)).valuation_le_one (c.coeff a)
  have h_inner_le : Valued.v (intPartial x (g - a) K) ≤
      ((Multiplicative.ofAdd (-(K + 1) : ℤ) : Multiplicative ℤ) : WithZero _) :=
    null_series_tail_bound hx (g - a) K
  calc Valued.v (algebraMap (OQpCUn p) (QpCUn p) (c.coeff a)) *
          Valued.v (intPartial x (g - a) K)
      ≤ 1 * Valued.v (intPartial x (g - a) K) := mul_le_mul' h_alg_le (le_refl _)
    _ = Valued.v (intPartial x (g - a) K) := one_mul _
    _ ≤ ((Multiplicative.ofAdd (-(K + 1) : ℤ) : Multiplicative ℤ) : WithZero _) := h_inner_le

/-- The ideal of null series in `W(𝔽ᵃ_[p])((t^ℚ))`. That the null series form an ideal is
[Poonen, Proposition 3]; the field `𝕃_[p]` is the quotient by this ideal. -/
def NullSeriesIdeal (p : ℕ) [Fact (Nat.Prime p)] : Ideal (LiftedPAdicHahnSeries p) where
  carrier := {x | IsNullSeries x}
  add_mem' := by
    intro x y hx hy
    change IsNullSeries x at hx
    change IsNullSeries y at hy
    change IsNullSeries (x + y)
    intro g
    let sx : ℕ → Finset ℤ := fun M => Set.Finite.toFinset (finiteBelow x g M)
    let sy : ℕ → Finset ℤ := fun M => Set.Finite.toFinset (finiteBelow y g M)
    let sxy : ℕ → Finset ℤ := fun M => Set.Finite.toFinset (finiteBelow (x + y) g M)
    let su : ℕ → Finset ℤ := fun M => sx M ∪ sy M
    let fx : ℕ → ℤ → QpCUn p := fun M n =>
      (p : QpCUn p) ^ n * algebraMap (OQpCUn p) (QpCUn p) (x.coeff (g + n))
    let fy : ℕ → ℤ → QpCUn p := fun M n =>
      (p : QpCUn p) ^ n * algebraMap (OQpCUn p) (QpCUn p) (y.coeff (g + n))
    let fxy : ℕ → ℤ → QpCUn p := fun M n =>
      (p : QpCUn p) ^ n * algebraMap (OQpCUn p) (QpCUn p) ((x + y).coeff (g + n))
    have hsxy_sub : ∀ M, sxy M ⊆ su M := by
      intro M n hn
      have hn' : g + n ≤ M ∧ (x + y).coeff (g + n) ≠ 0 :=
        (Set.Finite.mem_toFinset (hs := finiteBelow (x + y) g M) (a := n)).1 hn
      have hmem : g + n ∈ (x + y).support := (HahnSeries.mem_support (x + y) (g + n)).2 hn'.2
      have hunion := HahnSeries.support_add_subset (x := x) (y := y) hmem
      rcases hunion with hxmem | hymem
      · exact Finset.mem_union_left _ <|
          (Set.Finite.mem_toFinset (hs := finiteBelow x g M) (a := n)).2 ⟨hn'.1, hxmem⟩
      · exact Finset.mem_union_right _ <|
          (Set.Finite.mem_toFinset (hs := finiteBelow y g M) (a := n)).2 ⟨hn'.1, hymem⟩
    have hsumx (M : ℕ) : Finset.sum (su M) (fx M) = Finset.sum (sx M) (fx M) := by
      symm
      apply Finset.sum_subset
      · intro n hn
        exact Finset.mem_union_left _ hn
      · intro n hnu hnsx
        have hny : n ∈ sy M := (Finset.mem_union.mp hnu).resolve_left hnsx
        have hmem : g + n ≤ M ∧ y.coeff (g + n) ≠ 0 :=
          (Set.Finite.mem_toFinset (hs := finiteBelow y g M) (a := n)).1 hny
        have hxzero : x.coeff (g + n) = 0 := by
          by_contra hxne
          exact hnsx <|
            (Set.Finite.mem_toFinset (hs := finiteBelow x g M) (a := n)).2 ⟨hmem.1, hxne⟩
        simp [hxzero]
    have hsumy (M : ℕ) : Finset.sum (su M) (fy M) = Finset.sum (sy M) (fy M) := by
      symm
      apply Finset.sum_subset
      · intro n hn
        exact Finset.mem_union_right _ hn
      · intro n hnu hnsy
        have hnx : n ∈ sx M := (Finset.mem_union.mp hnu).resolve_right hnsy
        have hmem : g + n ≤ M ∧ x.coeff (g + n) ≠ 0 :=
          (Set.Finite.mem_toFinset (hs := finiteBelow x g M) (a := n)).1 hnx
        have hyzero : y.coeff (g + n) = 0 := by
          by_contra hyne
          exact hnsy <|
            (Set.Finite.mem_toFinset (hs := finiteBelow y g M) (a := n)).2 ⟨hmem.1, hyne⟩
        simp [hyzero]
    have hsumxy (M : ℕ) : Finset.sum (su M) (fxy M) = Finset.sum (sxy M) (fxy M) := by
      symm
      apply Finset.sum_subset
      · exact hsxy_sub M
      · intro n hnu hnsxy
        have hcoeff : (x + y).coeff (g + n) = 0 := by
          by_contra hne
          exact hnsxy <| (Set.Finite.mem_toFinset (hs := finiteBelow (x + y) g M) (a := n)).2 ⟨by
            rcases Finset.mem_union.mp hnu with hnx | hny
            · exact (Set.Finite.mem_toFinset (hs := finiteBelow x g M) (a := n)).1 hnx |>.1
            · exact (Set.Finite.mem_toFinset (hs := finiteBelow y g M) (a := n)).1 hny |>.1, hne⟩
        simp [hcoeff]
    have hfun :
        (fun M => Finset.sum (sxy M) (fxy M)) =
          fun M => Finset.sum (sx M) (fx M) + Finset.sum (sy M) (fy M) := by
      funext M
      rw [← hsumxy M]
      calc
        Finset.sum (su M) (fxy M) = Finset.sum (su M) (fun n => fx M n + fy M n) := by
          apply Finset.sum_congr rfl
          intro n hn
          simp [fxy, fx, fy, HahnSeries.coeff_add', mul_add, map_add]
        _ = Finset.sum (su M) (fx M) + Finset.sum (su M) (fy M) := by
          rw [Finset.sum_add_distrib]
        _ = Finset.sum (sx M) (fx M) + Finset.sum (sy M) (fy M) := by
          rw [hsumx M, hsumy M]
    have hxmain :
        (fun M => ∑ n ∈ (Set.Finite.toFinset (finiteBelow x g M)).attach,
            (p : QpCUn p) ^ n.val * algebraMap (OQpCUn p) (QpCUn p) (x.coeff (g + n))) =
          fun M => Finset.sum (sx M) (fx M) := by
      funext M
      dsimp [sx, fx]
      simpa using (Finset.sum_attach (s := Set.Finite.toFinset (finiteBelow x g M))
        (f := fun n : ℤ => (p : QpCUn p) ^ n * algebraMap (OQpCUn p) (QpCUn p) (x.coeff (g + n))))
    have hymain :
        (fun M => ∑ n ∈ (Set.Finite.toFinset (finiteBelow y g M)).attach,
            (p : QpCUn p) ^ n.val * algebraMap (OQpCUn p) (QpCUn p) (y.coeff (g + n))) =
          fun M => Finset.sum (sy M) (fy M) := by
      funext M
      dsimp [sy, fy]
      simpa using (Finset.sum_attach (s := Set.Finite.toFinset (finiteBelow y g M))
        (f := fun n : ℤ => (p : QpCUn p) ^ n * algebraMap (OQpCUn p) (QpCUn p) (y.coeff (g + n))))
    have hmain :
        (fun M =>
          ∑ n : Set.Finite.toFinset (finiteBelow (x + y) g M),
            (p : QpCUn p) ^ n.val * algebraMap (OQpCUn p) (QpCUn p) ((x + y).coeff (g + n))) =
          fun M => Finset.sum (sxy M) (fxy M) := by
      funext M
      dsimp [sxy, fxy]
      simpa using (Finset.sum_attach (s := Set.Finite.toFinset (finiteBelow (x + y) g M))
        (f := fun n : ℤ =>
          (p : QpCUn p) ^ n * algebraMap (OQpCUn p) (QpCUn p) ((x + y).coeff (g + n))))
    have hx' : Filter.Tendsto (fun M => Finset.sum (sx M) (fx M)) Filter.atTop (nhds 0) := by
      rw [← hxmain]
      exact hx g
    have hy' : Filter.Tendsto (fun M => Finset.sum (sy M) (fy M)) Filter.atTop (nhds 0) := by
      rw [← hymain]
      exact hy g
    rw [hmain]
    rw [hfun]
    simpa using hx'.add hy'
  zero_mem' := by simp [IsNullSeries]
  smul_mem' := by
    intro c x hx
    change IsNullSeries (c * x)
    change IsNullSeries x at hx
    intro g
    -- Goal: Tendsto (fun M => partialSum (c*x) g M) atTop (𝓝 0).
    -- Step 1: rewrite partialSum (c*x) g M as intPartial (c*x) g ⌊M - g⌋.
    have hpartial_eq : (fun M : ℕ => ∑ n : Set.Finite.toFinset (finiteBelow (c * x) g M),
        (p : QpCUn p) ^ n.val * algebraMap (OQpCUn p) (QpCUn p) ((c * x).coeff (g + n))) =
      fun M : ℕ => intPartial (c * x) g ⌊(M : ℚ) - g⌋ := by
      funext M
      exact partialSum_eq_intPartial (c * x) g M
    rw [hpartial_eq]
    -- Step 2: setup for ε-style argument via Valued.mem_nhds.
    have hp1 : (1 : NNReal) < p := by exact_mod_cast (Fact.out : Nat.Prime p).one_lt
    have hp_pos : (0 : NNReal) < p := zero_lt_one.trans hp1
    have hsm : StrictMono (WithZeroMulInt.toNNReal (p_ne_zero p)) :=
      WithZeroMulInt.toNNReal_strictMono hp1
    have hpinv_lt : (p : NNReal)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp1
    have hpinv_nn : 0 ≤ ((p : NNReal)⁻¹ : NNReal) := zero_le
    rw [Filter.tendsto_iff_forall_eventually_mem]
    intro U hU
    obtain ⟨γ, hγ_ne, hγ⟩ := exists_v_lt_subset hU
    set ε : NNReal :=
      WithZeroMulInt.toNNReal (p_ne_zero p) (γ : WithZero (Multiplicative ℤ)) with hε_def
    have hε_pos : (0 : NNReal) < ε := by
      rw [hε_def]
      rw [show ((WithZeroMulInt.toNNReal (p_ne_zero p)) (γ : WithZero (Multiplicative ℤ)) =
        if h : (γ : WithZero (Multiplicative ℤ)) = 0 then 0
        else (p : NNReal) ^ ((WithZero.unzero h).toAdd : ℤ)) from rfl]
      rw [dif_neg hγ_ne]
      exact zpow_pos hp_pos _
    have htendsto : Filter.Tendsto (fun n : ℕ => ((p : NNReal)⁻¹)^n) Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one hpinv_nn hpinv_lt
    obtain ⟨N, hN⟩ : ∃ N : ℕ, ((p : NNReal)⁻¹)^N < ε := by
      have h_eventually : ∀ᶠ n : ℕ in Filter.atTop, ((p : NNReal)⁻¹)^n < ε :=
        htendsto.eventually (eventually_lt_nhds hε_pos)
      exact h_eventually.exists
    -- Step 3: pick M₀ so that for M ≥ M₀, ⌊M - g⌋ + 1 ≥ N.
    rw [Filter.eventually_atTop]
    refine ⟨⌈((N : ℚ) - 1 + g)⌉₊, ?_⟩
    intro M hM
    set K : ℤ := ⌊(M : ℚ) - g⌋ with hK_def
    have hK_ge : (N : ℤ) - 1 ≤ K := by
      rw [hK_def]
      apply Int.le_floor.mpr
      have h1 : ((N : ℚ) - 1 + g) ≤ (⌈((N : ℚ) - 1 + g)⌉₊ : ℚ) := Nat.le_ceil _
      have h2 : ((⌈((N : ℚ) - 1 + g)⌉₊ : ℕ) : ℚ) ≤ (M : ℚ) := by exact_mod_cast hM
      push_cast
      linarith
    have hK_plus_1 : (N : ℤ) ≤ K + 1 := by linarith
    -- Step 4: apply the bound and convert to ε-form.
    apply hγ
    change Valued.v (intPartial (c * x) g K) < γ
    have hbound := intPartial_mul_valuation_bound c x hx g K
    -- hbound : Valued.v (intPartial (c * x) g K) ≤ ofAdd(-(K+1))
    have h_nnreal_le : WithZeroMulInt.toNNReal (p_ne_zero p)
        (Valued.v (intPartial (c * x) g K)) ≤
        WithZeroMulInt.toNNReal (p_ne_zero p)
          (((Multiplicative.ofAdd (-(K + 1) : ℤ) : Multiplicative ℤ) : WithZero _)) :=
      hsm.monotone hbound
    have htoNN : WithZeroMulInt.toNNReal (p_ne_zero p)
        (((Multiplicative.ofAdd (-(K + 1) : ℤ) : Multiplicative ℤ) : WithZero _)) =
        (p : NNReal) ^ (-(K + 1)) := by
      rw [WithZeroMulInt.toNNReal_neg_apply (p_ne_zero p) WithZero.coe_ne_zero, WithZero.unzero_coe]
      congr 1
    rw [htoNN] at h_nnreal_le
    -- Bound by ((p : NNReal)⁻¹)^N.
    have h_pow_le : (p : NNReal) ^ (-(K + 1)) ≤ ((p : NNReal)⁻¹)^N := by
      rw [show (p : NNReal)^(-(K + 1)) = ((p : NNReal)⁻¹)^((K : ℤ) + 1) from by
        rw [zpow_neg, ← inv_zpow]]
      rw [show ((p : NNReal)⁻¹)^((K : ℤ) + 1) = ((p : NNReal)⁻¹)^((K + 1).toNat) from by
        rw [← zpow_natCast]
        congr 1
        omega]
      apply pow_le_pow_of_le_one hpinv_nn (le_of_lt hpinv_lt)
      omega
    have h_combined : WithZeroMulInt.toNNReal (p_ne_zero p)
        (Valued.v (intPartial (c * x) g K)) < ε :=
      lt_of_le_of_lt (h_nnreal_le.trans h_pow_le) hN
    -- Convert to valuation form.
    rw [hε_def] at h_combined
    exact hsm.lt_iff_lt.mp h_combined

-- Sub-Obj 2a of `(NullSeriesIdeal p).IsMaximal` decomposition.
-- `1 ∉ NullSeriesIdeal p`. Direct route: at `g = 0`, the partial-sum sequence in
-- the definition of `IsNullSeries` is constantly `1` (only `n = 0` survives, and
-- `(1).coeff 0 = 1`), but `IsNullSeries` requires it to tend to `0`; uniqueness
-- of limits in `QpCUn p` forces `1 = 0`, contradicting `one_ne_zero`.
private lemma one_notMem_NullSeriesIdeal (p : ℕ) [Fact (Nat.Prime p)] :
    (1 : LiftedPAdicHahnSeries p) ∉ NullSeriesIdeal p := by
  classical
  intro h_null
  have h_NS : IsNullSeries (1 : LiftedPAdicHahnSeries p) := h_null
  have htend := h_NS 0
  -- The partial-sum sequence is constantly `1` for every `M : ℕ`.
  have h_partial_sum_one : ∀ M : ℕ,
      (∑ n : Set.Finite.toFinset (finiteBelow (1 : LiftedPAdicHahnSeries p) 0 M),
          (p : QpCUn p) ^ n.val *
            algebraMap (OQpCUn p) (QpCUn p)
              ((1 : LiftedPAdicHahnSeries p).coeff (0 + (n.val : ℚ))))
        = 1 := by
    intro M
    set S := Set.Finite.toFinset (finiteBelow (1 : LiftedPAdicHahnSeries p) 0 M) with hS_def
    -- The finiteBelow set at `g = 0` is `{0}` for any `M : ℕ`, since `(1).coeff q = 0`
    -- whenever `q ≠ 0` and `0 ≤ M` makes `n = 0` admissible.
    have hS_eq : S = ({0} : Finset ℤ) := by
      ext n
      simp only [hS_def, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, Finset.mem_singleton]
      constructor
      · rintro ⟨h_le, h_ne⟩
        by_contra h_n_ne_zero
        exact h_ne (by simp [HahnSeries.coeff_one, h_n_ne_zero])
      · rintro rfl
        refine ⟨?_, ?_⟩
        · have hM_nn : (0 : ℚ) ≤ (M : ℚ) := by exact_mod_cast (Nat.zero_le M)
          simp [hM_nn]
        · simp [HahnSeries.coeff_one]
    rw [show (∑ n : S, (p : QpCUn p) ^ n.val *
        algebraMap (OQpCUn p) (QpCUn p)
          ((1 : LiftedPAdicHahnSeries p).coeff (0 + (n.val : ℚ)))) =
        ∑ n ∈ S, (p : QpCUn p) ^ n *
          algebraMap (OQpCUn p) (QpCUn p)
            ((1 : LiftedPAdicHahnSeries p).coeff (0 + (n : ℚ))) from
      Finset.sum_attach (s := S) (f := fun n : ℤ =>
        (p : QpCUn p) ^ n *
          algebraMap (OQpCUn p) (QpCUn p)
            ((1 : LiftedPAdicHahnSeries p).coeff (0 + (n : ℚ))))]
    rw [hS_eq, Finset.sum_singleton]
    have h_zero_eq : (0 : ℚ) + (((0 : ℤ) : ℚ)) = 0 := by push_cast; ring
    rw [h_zero_eq, show ((1 : LiftedPAdicHahnSeries p).coeff 0) = 1 by
      rw [HahnSeries.coeff_one]; simp, map_one, mul_one]
    exact zpow_zero _
  -- The sequence is eventually `1`, so it tends to `1`. By uniqueness of limits in
  -- `QpCUn p` (which is `T2`), `1 = 0`, contradicting `one_ne_zero`.
  have h_tend_one :
      Filter.Tendsto
        (fun M : ℕ =>
          ∑ n : Set.Finite.toFinset (finiteBelow (1 : LiftedPAdicHahnSeries p) 0 M),
            (p : QpCUn p) ^ n.val *
              algebraMap (OQpCUn p) (QpCUn p)
                ((1 : LiftedPAdicHahnSeries p).coeff (0 + (n.val : ℚ))))
        Filter.atTop (nhds (1 : QpCUn p)) := by
    apply Filter.Tendsto.congr (fun M => (h_partial_sum_one M).symm)
    exact tendsto_const_nhds
  have h_eq : (1 : QpCUn p) = 0 := tendsto_nhds_unique h_tend_one htend
  exact one_ne_zero h_eq

-- Eagerly establish `Nontrivial` of the quotient from `one_notMem_NullSeriesIdeal`.
-- The full `IsMaximal` (and therefore `Field`) instance is established after
-- `canonical_leading_coeff_isUnit` and `exists_inverse_of_nonzero`. Some intermediate
-- proofs (notably `val_one_eq_zero`) need `(1 : Quot) ≠ 0` before that point, which
-- this `Nontrivial` instance supplies without circularity.
instance (p : ℕ) [Fact (Nat.Prime p)] :
    Nontrivial ((LiftedPAdicHahnSeries p) ⧸ (NullSeriesIdeal p)) :=
  Submodule.Quotient.nontrivial_iff.mpr
    ((Ideal.ne_top_iff_one _).mpr (one_notMem_NullSeriesIdeal p))

-- `(1 : Quot) ≠ 0`, proved directly from `one_notMem_NullSeriesIdeal`. (In v4.31 `one_ne_zero`
-- routes through the `NeZero (1)` class, whose synthesis does not fire here before the `Field`
-- instance is available, so we supply the fact explicitly.)
private lemma one_ne_zero_quot (p : ℕ) [Fact (Nat.Prime p)] :
    (1 : (LiftedPAdicHahnSeries p) ⧸ (NullSeriesIdeal p)) ≠ 0 := by
  intro h
  apply one_notMem_NullSeriesIdeal p
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_one]
  exact h

/-
  Auxiliary infrastructure for the proof of `exists_canonical_expansion`.

  Following `informal/exists_canonical_expansion.md`, the proof is decomposed
  into helper lemmas. The deepest step is the uniqueness of the Teichmuller series,
  paralleling the material in `Mathlib.RingTheory.WittVector.TeichmullerSeries`.
  Existence comes from `dvd_sub_sum_teichmuller_iterateFrobeniusEquiv_coeff`
  applied per coset `g ∈ Set.Ico (0:ℚ) 1`.
-/

namespace existsCanonicalExpansionAux

open scoped Pointwise

variable {p : ℕ} [Fact (Nat.Prime p)]

/--
The image of `ℕ` under the canonical embedding `ℕ → ℚ` is partially well-ordered.
This is a basic ingredient for the support-PWO bound `support s ⊆ support α + ℕ`.
-/
lemma natRange_isPWO : (Set.range ((↑) : ℕ → ℚ)).IsPWO := by
  have hUniv : (Set.univ : Set ℕ).IsPWO := Set.isPWO_of_wellQuasiOrderedLE _
  have hMono : MonotoneOn ((↑) : ℕ → ℚ) Set.univ := by
    intro a _ b _ h
    exact_mod_cast h
  simpa using hUniv.image_of_monotoneOn hMono

/--
**Support PWO bound.** If a function `s : ℚ → Fpbar p` has its support contained
in `α.support + Set.range ((↑) : ℕ → ℚ)`, then `support s` is partially
well-ordered. This is the key tool for closing the `IsPWO` obligation on `s`
in `exists_canonical_representative` once the construction yields the bound
`support s ⊆ support α + ℕ`.
-/
lemma support_isPWO_of_subset_support_add_natRange
    (α : LiftedPAdicHahnSeries p) {s : ℚ → Fpbar p}
    (h : Function.support s ⊆ α.support + Set.range ((↑) : ℕ → ℚ)) :
    (Function.support s).IsPWO :=
  (α.isPWO_support.add natRange_isPWO).mono h

/-- Lift an element of `ℚᶜᵘⁿ_[p]` with valuation `≤ 1` to `ℤᶜᵘⁿ_[p]`. In v4.31 `ℚᶜᵘⁿ_[p]` is a
`WithVal` *structure*, so `IsDiscreteValuationRing.exists_lift_of_le_one (K := ℚᶜᵘⁿ_[p])` no longer
unifies cheaply (it times out in `whnf`); we route through the underlying `FractionRing` via
`WithVal.equiv` instead. -/
lemma exists_lift_of_valued_le_one {z : ℚᶜᵘⁿ_[p]} (hz : Valued.v z ≤ 1) :
    ∃ a : ℤᶜᵘⁿ_[p], algebraMap (ℤᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p]) a = z := by
  have hz' : ((IsDiscreteValuationRing.maximalIdeal (ℤᶜᵘⁿ_[p])).valuation
      ((FractionRing (ℤᶜᵘⁿ_[p])))) (WithVal.equiv _ z) ≤ 1 := by
    rw [WithVal.val_apply_equiv]; exact hz
  obtain ⟨a, ha⟩ := IsDiscreteValuationRing.exists_lift_of_le_one
    (A := ℤᶜᵘⁿ_[p]) (K := FractionRing (ℤᶜᵘⁿ_[p])) hz'
  refine ⟨a, ?_⟩
  apply (WithVal.equiv _).injective
  rw [WithVal.algebraMap_right_apply] at *
  simpa [WithVal.equiv] using ha

/--
**Cauchy partial sums** (sub-claim of existence). For each `g : ℚ`, the
integer-cutoff partial sums `intPartial α g K` form a Cauchy sequence in
`ℚᶜᵘⁿ_[p]` as `K → ∞`. This follows because `α.coeff (g+n) p^n` has
`v(·) ≥ n` (in fact more, since `α.coeff (g+n) ∈ ℤᶜᵘⁿ_[p]`), so the tail
contribution is `≤ p^{-n} → 0`.
-/
lemma intPartial_isCauchy (α : LiftedPAdicHahnSeries p) (g : ℚ) :
    ∀ ε : NNReal, 0 < ε → ∃ K₀ : ℤ, ∀ K K' : ℤ, K₀ ≤ K → K₀ ≤ K' →
      ‖intPartial α g K - intPartial α g K'‖ < ε := by
  -- Strategy: bound `Valued.v (intPartial K - intPartial K')` by the valuation of
  -- a "tail" sum whose entries each have valuation `≤ ofAdd(-(min K K' + 1))`,
  -- then convert to norm via `WithZeroMulInt.toNNReal_strictMono`.
  intro ε hε
  -- Norm conversion: `‖a‖ = ↑(toNNReal (Valued.v a))` (see `QpCUn.norm_eq_toNNReal_valued`).
  have hnorm_eq : ∀ a : QpCUn p, ‖a‖ =
      ((WithZeroMulInt.toNNReal (p_ne_zero p) (Valued.v a) : NNReal) : ℝ) :=
    QpCUn.norm_eq_toNNReal_valued
  -- p > 1 in NNReal
  have hp1 : (1 : NNReal) < p := by exact_mod_cast (Fact.out : Nat.Prime p).one_lt
  have hp_pos : (0 : NNReal) < p := zero_lt_one.trans hp1
  have hpinv_lt : (p : NNReal)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp1
  have hpinv_nn : 0 ≤ ((p : NNReal)⁻¹ : NNReal) := zero_le
  -- Strict monotonicity of toNNReal
  have hsm : StrictMono (WithZeroMulInt.toNNReal (p_ne_zero p)) :=
    WithZeroMulInt.toNNReal_strictMono hp1
  -- toNNReal of ofAdd(-n) = (p : NNReal)^(-n)
  have htoNN : ∀ n : ℤ,
      (WithZeroMulInt.toNNReal (p_ne_zero p)
        (((Multiplicative.ofAdd (n : ℤ) : Multiplicative ℤ) : WithZero _))) = (p : NNReal)^n := by
    intro n
    rw [WithZeroMulInt.toNNReal_neg_apply _ WithZero.coe_ne_zero]
    simp
  -- Find N : ℕ such that (p : NNReal)⁻¹^N < ε
  have htendsto : Filter.Tendsto (fun n : ℕ => ((p : NNReal)⁻¹)^n) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hpinv_nn hpinv_lt
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ((p : NNReal)⁻¹)^N < ε := by
    have h_eventually : ∀ᶠ n : ℕ in Filter.atTop, ((p : NNReal)⁻¹)^n < ε :=
      htendsto.eventually (eventually_lt_nhds hε)
    exact h_eventually.exists
  -- Set K₀ := N - 1 (an integer). For K ≥ K₀, K + 1 ≥ N.
  refine ⟨(N : ℤ) - 1, ?_⟩
  intro K K' hK hK'
  -- Reduce to K ≤ K' case
  rcases le_total K K' with hKK' | hKK'
  · -- K ≤ K' case: ‖intPartial K - intPartial K'‖ = ‖intPartial K' - intPartial K‖
    rw [norm_sub_rev, intPartial_diff_eq_sdiff_sum α g K K' hKK']
    -- Show valuation bound
    have hval_bound : Valued.v (∑ n ∈ (Set.Finite.toFinset (finiteBelowInt α g K') \
            Set.Finite.toFinset (finiteBelowInt α g K)),
          (p : QpCUn p) ^ n * algebraMap (OQpCUn p) (QpCUn p) (α.coeff (g + n))) ≤
        ((Multiplicative.ofAdd (-(K + 1) : ℤ) : Multiplicative ℤ) : WithZero _) := by
      apply Valuation.map_sum_le
      intro n hn
      have hn_mem : n ∈ Set.Finite.toFinset (finiteBelowInt α g K') ∧
          n ∉ Set.Finite.toFinset (finiteBelowInt α g K) := Finset.mem_sdiff.mp hn
      have hn1 : n ≤ K' ∧ α.coeff (g + n) ≠ 0 :=
        (Set.Finite.mem_toFinset (hs := finiteBelowInt α g K')).mp hn_mem.1
      have hn2 : ¬ (n ≤ K ∧ α.coeff (g + n) ≠ 0) := by
        intro h
        exact hn_mem.2 ((Set.Finite.mem_toFinset (hs := finiteBelowInt α g K)).mpr h)
      have hn_gt : K < n := by
        by_contra hle
        push Not at hle
        exact hn2 ⟨hle, hn1.2⟩
      have hn_ge : K + 1 ≤ n := hn_gt
      -- Apply per-summand bound
      have h1 := valued_v_term_le (α.coeff (g + n)) n
      -- Bound by ofAdd(-(K+1)) using monotonicity
      have h2 : ((Multiplicative.ofAdd (-n : ℤ) : Multiplicative ℤ) :
            WithZero (Multiplicative ℤ)) ≤
          ((Multiplicative.ofAdd (-(K + 1) : ℤ) : Multiplicative ℤ) :
            WithZero (Multiplicative ℤ)) := by
        rw [WithZero.coe_le_coe]
        exact Multiplicative.ofAdd_le.mpr (by omega)
      exact h1.trans h2
    -- Convert valuation bound to norm bound
    rw [hnorm_eq]
    have h_nnreal_le : WithZeroMulInt.toNNReal (p_ne_zero p)
        (Valued.v (∑ n ∈ (Set.Finite.toFinset (finiteBelowInt α g K') \
            Set.Finite.toFinset (finiteBelowInt α g K)),
          (p : QpCUn p) ^ n * algebraMap (OQpCUn p) (QpCUn p) (α.coeff (g + n)))) ≤
        WithZeroMulInt.toNNReal (p_ne_zero p)
          (((Multiplicative.ofAdd (-(K + 1) : ℤ) : Multiplicative ℤ) : WithZero _)) :=
      hsm.monotone hval_bound
    rw [htoNN (-(K + 1))] at h_nnreal_le
    have h_pow_lt : (p : NNReal)^(-((K : ℤ) + 1)) < ε := by
      have h_pow_eq : (p : NNReal)^(-((K : ℤ) + 1)) = ((p : NNReal)⁻¹)^((K : ℤ) + 1) := by
        rw [zpow_neg, ← inv_zpow]
      rw [h_pow_eq]
      have hKN : (N : ℤ) ≤ K + 1 := by linarith
      have hN_pos : 0 ≤ (K : ℤ) + 1 := by linarith
      -- ((p : NNReal)⁻¹)^(K+1 : ℤ) = ((p : NNReal)⁻¹)^(K+1).toNat
      have h_zpow_toNat : ((p : NNReal)⁻¹)^((K : ℤ) + 1) =
          ((p : NNReal)⁻¹)^((K + 1).toNat) := by
        rw [← zpow_natCast]
        congr 1
        omega
      rw [h_zpow_toNat]
      -- For K+1 ≥ N, ((p⁻¹))^(K+1) ≤ ((p⁻¹))^N (decreasing)
      have h_le : ((p : NNReal)⁻¹)^((K + 1).toNat) ≤ ((p : NNReal)⁻¹)^N := by
        apply pow_le_pow_of_le_one hpinv_nn (le_of_lt hpinv_lt)
        omega
      exact h_le.trans_lt hN
    have h_combined : WithZeroMulInt.toNNReal (p_ne_zero p)
        (Valued.v (∑ n ∈ (Set.Finite.toFinset (finiteBelowInt α g K') \
              Set.Finite.toFinset (finiteBelowInt α g K)),
            (p : QpCUn p) ^ n * algebraMap (OQpCUn p) (QpCUn p) (α.coeff (g + n)))) < ε :=
      h_nnreal_le.trans_lt h_pow_lt
    exact_mod_cast h_combined
  · -- K' ≤ K case: diff is over T(K) \ T(K'), bound at K' + 1
    rw [intPartial_diff_eq_sdiff_sum α g K' K hKK']
    have hval_bound : Valued.v (∑ n ∈ (Set.Finite.toFinset (finiteBelowInt α g K) \
            Set.Finite.toFinset (finiteBelowInt α g K')),
          (p : QpCUn p) ^ n * algebraMap (OQpCUn p) (QpCUn p) (α.coeff (g + n))) ≤
        ((Multiplicative.ofAdd (-(K' + 1) : ℤ) : Multiplicative ℤ) : WithZero _) := by
      apply Valuation.map_sum_le
      intro n hn
      have hn_mem : n ∈ Set.Finite.toFinset (finiteBelowInt α g K) ∧
          n ∉ Set.Finite.toFinset (finiteBelowInt α g K') := Finset.mem_sdiff.mp hn
      have hn1 : n ≤ K ∧ α.coeff (g + n) ≠ 0 :=
        (Set.Finite.mem_toFinset (hs := finiteBelowInt α g K)).mp hn_mem.1
      have hn2 : ¬ (n ≤ K' ∧ α.coeff (g + n) ≠ 0) := by
        intro h
        exact hn_mem.2 ((Set.Finite.mem_toFinset (hs := finiteBelowInt α g K')).mpr h)
      have hn_gt : K' < n := by
        by_contra hle
        push Not at hle
        exact hn2 ⟨hle, hn1.2⟩
      have hn_ge : K' + 1 ≤ n := hn_gt
      have h1 := valued_v_term_le (α.coeff (g + n)) n
      have h2 : ((Multiplicative.ofAdd (-n : ℤ) : Multiplicative ℤ) :
            WithZero (Multiplicative ℤ)) ≤
          ((Multiplicative.ofAdd (-(K' + 1) : ℤ) : Multiplicative ℤ) :
            WithZero (Multiplicative ℤ)) := by
        rw [WithZero.coe_le_coe]
        exact Multiplicative.ofAdd_le.mpr (by omega)
      exact h1.trans h2
    rw [hnorm_eq]
    have h_nnreal_le : WithZeroMulInt.toNNReal (p_ne_zero p)
        (Valued.v (∑ n ∈ (Set.Finite.toFinset (finiteBelowInt α g K) \
            Set.Finite.toFinset (finiteBelowInt α g K')),
          (p : QpCUn p) ^ n * algebraMap (OQpCUn p) (QpCUn p) (α.coeff (g + n)))) ≤
        WithZeroMulInt.toNNReal (p_ne_zero p)
          (((Multiplicative.ofAdd (-(K' + 1) : ℤ) : Multiplicative ℤ) : WithZero _)) :=
      hsm.monotone hval_bound
    rw [htoNN (-(K' + 1))] at h_nnreal_le
    have h_pow_lt : (p : NNReal)^(-((K' : ℤ) + 1)) < ε := by
      have h_pow_eq : (p : NNReal)^(-((K' : ℤ) + 1)) = ((p : NNReal)⁻¹)^((K' : ℤ) + 1) := by
        rw [zpow_neg, ← inv_zpow]
      rw [h_pow_eq]
      have hKN : (N : ℤ) ≤ K' + 1 := by linarith
      have hN_pos : 0 ≤ (K' : ℤ) + 1 := by linarith
      have h_zpow_toNat : ((p : NNReal)⁻¹)^((K' : ℤ) + 1) =
          ((p : NNReal)⁻¹)^((K' + 1).toNat) := by
        rw [← zpow_natCast]
        congr 1
        omega
      rw [h_zpow_toNat]
      have h_le : ((p : NNReal)⁻¹)^((K' + 1).toNat) ≤ ((p : NNReal)⁻¹)^N := by
        apply pow_le_pow_of_le_one hpinv_nn (le_of_lt hpinv_lt)
        omega
      exact h_le.trans_lt hN
    have h_combined : WithZeroMulInt.toNNReal (p_ne_zero p)
        (Valued.v (∑ n ∈ (Set.Finite.toFinset (finiteBelowInt α g K) \
              Set.Finite.toFinset (finiteBelowInt α g K')),
            (p : QpCUn p) ^ n * algebraMap (OQpCUn p) (QpCUn p) (α.coeff (g + n)))) < ε :=
      h_nnreal_le.trans_lt h_pow_lt
    exact_mod_cast h_combined

/--
**Limit of partial sums** (sub-claim of existence). The partial sums of `α` at
coset `g` converge in the complete DVR `ℚᶜᵘⁿ_[p]` to a limit `f_g`.
Uses `intPartial_isCauchy` and `CompleteSpace ℚᶜᵘⁿ_[p]` (which itself is an
instance available in `QpCUn.lean`).
-/
lemma exists_lim_intPartial (α : LiftedPAdicHahnSeries p) (g : ℚ) :
    ∃ y : ℚᶜᵘⁿ_[p], Filter.Tendsto (intPartial α g) Filter.atTop (nhds y) := by
  -- Cauchy in complete space ⇒ converges.
  -- Strategy: prove `CauchySeq` via `Valued.cauchy_iff` (since the default UniformSpace
  -- on `ℚᶜᵘⁿ_[p]` is the Valued one, not the metric one from `WithAbs.normedField`).
  -- Translate Γ₀ˣ-style Cauchy condition to ε-NNReal-style via `WithZeroMulInt.toNNReal`.
  have hp1 : (1 : NNReal) < p := by exact_mod_cast (Fact.out : Nat.Prime p).one_lt
  have hsm : StrictMono (WithZeroMulInt.toNNReal (p_ne_zero p)) :=
    WithZeroMulInt.toNNReal_strictMono hp1
  have hp_pos : (0 : NNReal) < p := zero_lt_one.trans hp1
  have hCauchy : CauchySeq (intPartial α g) := by
    rw [show CauchySeq (intPartial α g) = Cauchy (Filter.atTop.map (intPartial α g)) from rfl,
        Valued.cauchy_iff]
    refine ⟨Filter.map_neBot, ?_⟩
    intro γ
    -- In v4.31 `γ : (ValueGroup₀ Valued.v)ˣ`; bridge to a `WithZero (Multiplicative ℤ)` bound via
    -- `MonoidWithZeroHom.ValueGroup₀.embedding` (matching the `exists_v_lt_subset` template above).
    set c : WithZero (Multiplicative ℤ) := MonoidWithZeroHom.ValueGroup₀.embedding γ.1 with hc_def
    have hc_ne : c ≠ 0 := MonoidWithZeroHom.ValueGroup₀.embedding_unit_ne_zero γ
    -- Convert c to ε : NNReal
    set ε : NNReal :=
      WithZeroMulInt.toNNReal (p_ne_zero p) c with hε_def
    have hε_pos : (0 : NNReal) < ε := by
      rw [hε_def]
      exact WithZeroMulInt.toNNReal_pos (p_ne_zero p) hc_ne
    obtain ⟨K₀, hK₀⟩ := intPartial_isCauchy α g ε hε_pos
    -- The set M = `intPartial α g` applied to integers ≥ K₀
    refine ⟨{ a | ∃ K : ℤ, K₀ ≤ K ∧ a = intPartial α g K }, ?_, ?_⟩
    · -- M ∈ Filter.atTop.map (intPartial α g)
      rw [Filter.mem_map]
      refine Filter.mem_of_superset (Filter.Ici_mem_atTop K₀) ?_
      intro K hK
      exact ⟨K, hK, rfl⟩
    · -- For x, y ∈ M, Valued.v.restrict (y - x) < γ.1
      intro x hx y hy
      obtain ⟨K, hK, rfl⟩ := hx
      obtain ⟨K', hK', rfl⟩ := hy
      -- Need: Valued.v.restrict (intPartial α g K' - intPartial α g K) < γ.1, which by
      -- `restrict_lt_iff_lt_embedding` is `Valued.v (…) < c` (= embedding γ.1).
      have h_norm := hK₀ K' K hK' hK
      -- h_norm : ‖intPartial α g K' - intPartial α g K‖ < ε
      -- Convert to valuation bound
      have h_norm_eq :
          ‖intPartial α g K' - intPartial α g K‖ =
            ((WithZeroMulInt.toNNReal (p_ne_zero p)
              (Valued.v (intPartial α g K' - intPartial α g K)) : NNReal) : ℝ) :=
        QpCUn.norm_eq_toNNReal_valued _
      rw [h_norm_eq] at h_norm
      have h_NN :
          (WithZeroMulInt.toNNReal (p_ne_zero p)
            (Valued.v (intPartial α g K' - intPartial α g K)) : NNReal) < ε := by
        exact_mod_cast h_norm
      have h_val_lt :
          Valued.v.restrict (intPartial α g K' - intPartial α g K) < γ.1 := by
        rw [Valuation.restrict_lt_iff_lt_embedding, ← hc_def]
        rw [hε_def] at h_NN
        exact hsm.lt_iff_lt.mp h_NN
      exact h_val_lt
  -- Apply `CauchySeq.tendsto_limUnder` (uses `[CompleteSpace ℚᶜᵘⁿ_[p]]`)
  exact ⟨_, hCauchy.tendsto_limUnder⟩

/--
**Per-coset Teichmuller digit decomposition** (sub-claim of existence). For each
`y : ℚᶜᵘⁿ_[p]`, there exist a function `b : ℤ → Fpbar p` and an integer cutoff
`m₀` such that `b k = 0` for `k < m₀` and the partial sums
`intPartial-style sums of [b]·p^·` converge to `y` in `ℚᶜᵘⁿ_[p]`.

Built from Mathlib's
`WittVector.dvd_sub_sum_teichmuller_iterateFrobeniusEquiv_coeff` after
shifting by `p^{-v(y)}` to land in the integers.
-/
lemma exists_teichmuller_digits (y : ℚᶜᵘⁿ_[p]) :
    ∃ (b : ℤ → Fpbar p) (m₀ : ℤ),
      (∀ k : ℤ, k < m₀ → b k = 0) ∧
      Filter.Tendsto
        (fun K : ℤ => ∑ k ∈ Finset.Icc m₀ K,
          (p : QpCUn p) ^ k * algebraMap (OQpCUn p) (QpCUn p) (teichmuller p (b k)))
        Filter.atTop (nhds y) := by
  -- Apply Mathlib's teichmuller-series existence to `p^{-v(y)} · y ∈ ℤᶜᵘⁿ_[p]`.
  by_cases hy : y = 0
  · -- Case 1: y = 0. Take b ≡ 0, m₀ = 0. Each summand is 0.
    refine ⟨0, 0, fun _ _ => rfl, ?_⟩
    rw [hy]
    have hzero : (fun K : ℤ => ∑ k ∈ Finset.Icc (0 : ℤ) K,
        (p : QpCUn p) ^ k * algebraMap (OQpCUn p) (QpCUn p)
          (teichmuller p ((0 : ℤ → Fpbar p) k))) = fun _ => (0 : QpCUn p) := by
      funext K
      apply Finset.sum_eq_zero
      intro k _
      simp
    rw [hzero]
    exact tendsto_const_nhds
  · -- Case 2: y ≠ 0.
    have hv_ne : Valued.v y ≠ 0 := by
      simp [hy]
    -- m' : Multiplicative ℤ from WithZero.unzero
    set m' : Multiplicative ℤ := WithZero.unzero hv_ne with hm'_def
    -- m₀ := -m'.toAdd
    set m₀ : ℤ := -m'.toAdd with hm₀_def
    have hvy_eq : Valued.v y = (m' : WithZero (Multiplicative ℤ)) := by
      rw [hm'_def, WithZero.coe_unzero]
    have hm'_eq : (m' : WithZero (Multiplicative ℤ)) =
        ((Multiplicative.ofAdd (-m₀ : ℤ) : Multiplicative ℤ) : WithZero _) := by
      rw [hm₀_def, neg_neg]
      congr
    have hpn_val := valued_v_p_zpow (p := p)
    -- z := (p : QpCUn p)^(-m₀) * y, Valued.v z = 1
    set z : QpCUn p := (p : QpCUn p)^(-m₀) * y with hz_def
    have hvz : Valued.v z = 1 := by
      rw [hz_def, Valuation.map_mul, hpn_val (-m₀), hvy_eq, hm'_eq]
      rw [← WithZero.coe_mul]
      rw [show (Multiplicative.ofAdd (-(-m₀) : ℤ) * Multiplicative.ofAdd (-m₀ : ℤ)
            : Multiplicative ℤ) = 1 from by
        rw [← ofAdd_add]
        simp]
      rfl
    have hvz_le : Valued.v z ≤ 1 := hvz.le
    -- Lift z to OQpCUn p
    obtain ⟨z', hz'⟩ := exists_lift_of_valued_le_one hvz_le
    -- Define the Teichmuller digits from z'
    let a : ℕ → Fpbar p := fun n => ((frobeniusEquiv (Fpbar p) p).symm ^ n) (z'.coeff n)
    let b : ℤ → Fpbar p := fun k =>
      if h : 0 ≤ k - m₀ then a (k - m₀).toNat else 0
    refine ⟨b, m₀, ?_, ?_⟩
    · -- ∀ k < m₀, b k = 0
      intro k hk
      have hneg : ¬ (0 ≤ k - m₀) := by linarith
      change (if h : 0 ≤ k - m₀ then a (k - m₀).toNat else 0) = 0
      rw [dif_neg hneg]
    · -- Filter.Tendsto (partial sums) atTop (nhds y)
      have hp_ne : (p : QpCUn p) ≠ 0 := by
        rw [show (p : QpCUn p) = algebraMap (OQpCUn p) (QpCUn p) (p : OQpCUn p) from by
          push_cast; rfl]
        exact fun h => WittVector.p_nonzero p _
          ((IsFractionRing.injective (OQpCUn p) (QpCUn p))
            (by simpa using h))
      -- Key norm-like bound: for K ≥ m₀,
      -- Valued.v (y - partial_sum K) ≤ ofAdd(-(K+1))
      have hbound : ∀ K : ℤ, m₀ ≤ K → Valued.v (y -
          ∑ k ∈ Finset.Icc m₀ K,
            (p : QpCUn p) ^ k * algebraMap (OQpCUn p) (QpCUn p) (teichmuller p (b k))) ≤
        ((Multiplicative.ofAdd (-(K + 1) : ℤ) : Multiplicative ℤ) : WithZero _) := by
        intro K hK
        set n : ℕ := (K - m₀).toNat with hn_def
        have hK_eq : K = m₀ + (n : ℤ) := by
          rw [hn_def]; omega
        -- Mathlib's theorem applied to z'
        have hmathlib : (p : OQpCUn p)^(n+1) ∣ z' - ∑ i ∈ Finset.Iic n,
            teichmuller p (a i) * (p : OQpCUn p)^i :=
          WittVector.dvd_sub_sum_teichmuller_iterateFrobeniusEquiv_coeff z' n
        obtain ⟨c, hc⟩ := hmathlib
        -- Transport to QpCUn p via algebraMap
        have halg := congrArg (algebraMap (OQpCUn p) (QpCUn p)) hc
        simp only [map_sub, map_sum, map_mul, map_pow] at halg
        rw [hz'] at halg
        -- Introduce p in QpCUn p form
        have hp_cast : algebraMap (OQpCUn p) (QpCUn p) (p : OQpCUn p) = (p : QpCUn p) := by
          push_cast; rfl
        rw [hp_cast] at halg
        -- halg : z - ∑ i ∈ Iic n, algebraMap (teichmuller p (a i)) * (p : QpCUn p)^i =
        --        (p : QpCUn p)^(n+1) * algebraMap c
        -- Multiply by (p : QpCUn p)^m₀ to get y - partial_sum
        have hy_eq : y = (p : QpCUn p)^m₀ * z := by
          rw [hz_def, ← mul_assoc, ← zpow_add₀ hp_ne, add_neg_cancel, zpow_zero, one_mul]
        -- Reindex the partial sum
        have hreindex : ∑ k ∈ Finset.Icc m₀ K,
            (p : QpCUn p) ^ k * algebraMap (OQpCUn p) (QpCUn p) (teichmuller p (b k)) =
          (p : QpCUn p)^m₀ * ∑ i ∈ Finset.Iic n,
            algebraMap (OQpCUn p) (QpCUn p) (teichmuller p (a i)) * (p : QpCUn p)^i := by
          have hIcc_eq : Finset.Icc m₀ K =
              (Finset.range (n + 1)).map (Nat.castEmbedding.trans <| addLeftEmbedding m₀) := by
            rw [Int.Icc_eq_finset_map]
            congr 1
            have : K + 1 - m₀ = (n : ℤ) + 1 := by rw [hK_eq]; ring
            rw [this]
            simp
          rw [hIcc_eq, Finset.sum_map, ← Nat.range_succ_eq_Iic, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          simp only [Function.Embedding.trans_apply, Nat.castEmbedding_apply,
            addLeftEmbedding_apply]
          have hbi : b (m₀ + (i : ℤ)) = a i := by
            change (if h : 0 ≤ (m₀ + (i : ℤ)) - m₀ then a ((m₀ + (i : ℤ)) - m₀).toNat else 0) = a i
            have h_nn : (0 : ℤ) ≤ (m₀ + (i : ℤ)) - m₀ := by omega
            rw [dif_pos h_nn]
            congr 1
            omega
          rw [hbi, zpow_add₀ hp_ne, zpow_natCast]
          ring
        -- y - partial_sum K = (p : QpCUn p)^m₀ * ((p : QpCUn p)^(n+1) * algebraMap c)
        have hkey : y - ∑ k ∈ Finset.Icc m₀ K,
            (p : QpCUn p) ^ k * algebraMap (OQpCUn p) (QpCUn p) (teichmuller p (b k)) =
          (p : QpCUn p)^m₀ * ((p : QpCUn p)^(n+1) * algebraMap (OQpCUn p) (QpCUn p) c) := by
          rw [hreindex, hy_eq, ← mul_sub, halg]
        rw [hkey]
        rw [Valuation.map_mul, Valuation.map_mul, hpn_val m₀]
        rw [show ((p : QpCUn p)^(n+1) : QpCUn p) = ((p : QpCUn p)^((n : ℤ)+1) : QpCUn p) from by
          rw [← zpow_natCast (p : QpCUn p) (n+1)]; push_cast; rfl]
        rw [hpn_val ((n : ℤ)+1)]
        have h_alg_le : Valued.v (algebraMap (OQpCUn p) (QpCUn p) c) ≤ 1 :=
          (IsDiscreteValuationRing.maximalIdeal (OQpCUn p)).valuation_le_one c
        calc ((Multiplicative.ofAdd (-m₀ : ℤ) : Multiplicative ℤ) : WithZero _) *
            (((Multiplicative.ofAdd (-((n : ℤ) + 1)) : Multiplicative ℤ) : WithZero _) *
              Valued.v (algebraMap (OQpCUn p) (QpCUn p) c))
            ≤ ((Multiplicative.ofAdd (-m₀ : ℤ) : Multiplicative ℤ) : WithZero _) *
              (((Multiplicative.ofAdd (-((n : ℤ) + 1)) : Multiplicative ℤ) : WithZero _) * 1) :=
              mul_le_mul' (le_refl _) (mul_le_mul' (le_refl _) h_alg_le)
          _ = ((Multiplicative.ofAdd (-m₀ : ℤ) : Multiplicative ℤ) : WithZero _) *
              (((Multiplicative.ofAdd (-((n : ℤ) + 1)) : Multiplicative ℤ) : WithZero _)) := by
              rw [mul_one]
          _ = ((Multiplicative.ofAdd ((-m₀) + (-((n : ℤ) + 1))) : Multiplicative ℤ) :
                WithZero _) := by
              rw [← WithZero.coe_mul, ← ofAdd_add]
          _ = ((Multiplicative.ofAdd (-(K + 1) : ℤ) : Multiplicative ℤ) : WithZero _) := by
              congr 2; omega
      -- Step 2: Use this bound to prove Tendsto.
      have hp1 : (1 : NNReal) < p := by exact_mod_cast (Fact.out : Nat.Prime p).one_lt
      have hp_pos : (0 : NNReal) < p := zero_lt_one.trans hp1
      have hsm : StrictMono (WithZeroMulInt.toNNReal (p_ne_zero p)) :=
        WithZeroMulInt.toNNReal_strictMono hp1
      have hpinv_lt : (p : NNReal)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp1
      have hpinv_nn : 0 ≤ ((p : NNReal)⁻¹ : NNReal) := zero_le
      rw [Filter.tendsto_iff_forall_eventually_mem]
      intro U hU
      obtain ⟨γ, hγ_ne, hγ⟩ := exists_v_sub_lt_subset hU
      set ε : NNReal :=
        WithZeroMulInt.toNNReal (p_ne_zero p) (γ : WithZero (Multiplicative ℤ)) with hε_def
      have hε_pos : (0 : NNReal) < ε := by
        rw [hε_def]
        rw [show ((WithZeroMulInt.toNNReal (p_ne_zero p)) (γ : WithZero (Multiplicative ℤ)) =
          if h : (γ : WithZero (Multiplicative ℤ)) = 0 then 0
          else (p : NNReal) ^ ((WithZero.unzero h).toAdd : ℤ)) from rfl]
        rw [dif_neg hγ_ne]
        exact zpow_pos hp_pos _
      have htendsto : Filter.Tendsto (fun n : ℕ => ((p : NNReal)⁻¹)^n) Filter.atTop (nhds 0) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one hpinv_nn hpinv_lt
      obtain ⟨N, hN⟩ : ∃ N : ℕ, ((p : NNReal)⁻¹)^N < ε := by
        have h_eventually : ∀ᶠ n : ℕ in Filter.atTop, ((p : NNReal)⁻¹)^n < ε :=
          htendsto.eventually (eventually_lt_nhds hε_pos)
        exact h_eventually.exists
      rw [Filter.eventually_atTop]
      refine ⟨max m₀ ((N : ℤ) - 1), ?_⟩
      intro K hK
      have hK_ge_m₀ : m₀ ≤ K := le_of_max_le_left hK
      have hK_ge_N : (N : ℤ) - 1 ≤ K := le_of_max_le_right hK
      have hK_plus_1 : (N : ℤ) ≤ K + 1 := by linarith
      apply hγ
      change Valued.v ((∑ k ∈ Finset.Icc m₀ K,
        (p : QpCUn p) ^ k * algebraMap (OQpCUn p) (QpCUn p) (teichmuller p (b k))) - y) < γ
      rw [Valuation.map_sub_swap]
      -- h1 : Valued.v (y - partial_sum K) ≤ ofAdd(-(K+1))
      have h1 := hbound K hK_ge_m₀
      have h_nnreal_le : WithZeroMulInt.toNNReal (p_ne_zero p)
          (Valued.v (y - ∑ k ∈ Finset.Icc m₀ K,
            (p : QpCUn p) ^ k * algebraMap (OQpCUn p) (QpCUn p) (teichmuller p (b k)))) ≤
          WithZeroMulInt.toNNReal (p_ne_zero p)
            (((Multiplicative.ofAdd (-(K + 1) : ℤ) : Multiplicative ℤ) : WithZero _)) :=
        hsm.monotone h1
      have htoNN : WithZeroMulInt.toNNReal (p_ne_zero p)
          (((Multiplicative.ofAdd (-(K + 1) : ℤ) : Multiplicative ℤ) : WithZero _)) =
          (p : NNReal)^(-(K + 1)) := by
        rw [WithZeroMulInt.toNNReal_neg_apply (p_ne_zero p) WithZero.coe_ne_zero,
          WithZero.unzero_coe]
        congr 1
      rw [htoNN] at h_nnreal_le
      -- Bound by ((p : NNReal)⁻¹)^N
      have h_pow_le : (p : NNReal)^(-(K + 1)) ≤ ((p : NNReal)⁻¹)^N := by
        rw [show (p : NNReal)^(-(K + 1)) = ((p : NNReal)⁻¹)^((K : ℤ) + 1) from by
          rw [zpow_neg, ← inv_zpow]]
        rw [show ((p : NNReal)⁻¹)^((K : ℤ) + 1) = ((p : NNReal)⁻¹)^((K + 1).toNat) from by
          rw [← zpow_natCast]
          congr 1
          omega]
        apply pow_le_pow_of_le_one hpinv_nn (le_of_lt hpinv_lt)
        omega
      have h_chain : WithZeroMulInt.toNNReal (p_ne_zero p)
          (Valued.v (y - ∑ k ∈ Finset.Icc m₀ K,
            (p : QpCUn p) ^ k * algebraMap (OQpCUn p) (QpCUn p) (teichmuller p (b k)))) < ε :=
        (h_nnreal_le.trans h_pow_le).trans_lt hN
      -- Bridge back to valuation-form
      rw [hε_def] at h_chain
      exact hsm.lt_iff_lt.mp h_chain

set_option maxHeartbeats 400000 in
-- maxHeartbeats: heavy elaboration in the multi-phase proof body
/--
**Per-coset Teichmuller digit uniqueness** (sub-claim of uniqueness). Two
digit-decompositions `b, b' : ℤ → Fpbar p` of the same element of `ℚᶜᵘⁿ_[p]`
with the same vanishing-below-cutoff property must agree.

Mathlib's `Mathlib.RingTheory.WittVector.TeichmullerSeries` lists this as
the key remaining ingredient. The argument is to read off the lowest nonzero coefficient using
`teichmuller_mul_pow_coeff_of_ne` plus `teichmuller_mul_pow_coeff`, subtract,
and recurse.
-/
lemma teichmuller_digits_unique (b b' : ℤ → Fpbar p) (m₀ m₀' : ℤ)
    (hb : ∀ k : ℤ, k < m₀ → b k = 0) (hb' : ∀ k : ℤ, k < m₀' → b' k = 0)
    {y : ℚᶜᵘⁿ_[p]}
    (htb : Filter.Tendsto
        (fun K : ℤ => ∑ k ∈ Finset.Icc m₀ K,
          (p : QpCUn p) ^ k * algebraMap (OQpCUn p) (QpCUn p) (teichmuller p (b k)))
        Filter.atTop (nhds y))
    (htb' : Filter.Tendsto
        (fun K : ℤ => ∑ k ∈ Finset.Icc m₀' K,
          (p : QpCUn p) ^ k * algebraMap (OQpCUn p) (QpCUn p) (teichmuller p (b' k)))
        Filter.atTop (nhds y)) :
    ∀ k : ℤ, b k = b' k := by
  -- ==========================================================================
  -- Strategy. Set m := min m₀ m₀'. Both `b, b'` vanish below `m`. Reindex
  -- both `Icc m₀ K`-sums to `Icc m K`-sums (zero on the gap). Define
  -- `c i := b (m + i)` and `c' i := b' (m + i)` (both `ℕ → Fpbar p`).
  -- After multiplying both Tendstos by the constant `(p : QpCUn p)^(-m)`, we
  -- get `algebraMap (Spart c N) → z` and `algebraMap (Spart c' N) → z`
  -- where `Spart c N := ∑ i ∈ Iic N, (p : OQpCUn p)^i * teichmuller p (c i)`
  -- and `z := (p : QpCUn p)^(-m) * y`. Hence
  -- `algebraMap (Spart c N - Spart c' N) → 0` in QpCUn p.
  --
  -- For each `i : ℕ`, eventually `Valued.v (algebraMap (Spart c N - Spart c' N))
  -- ≤ ofAdd(-(i+1))`, hence `(p : OQpCUn p)^(i+1) ∣ Spart c N - Spart c' N`
  -- (DVR uniformizer characterization, via `IsDiscreteValuationRing.exists_lift_of_le_one`
  -- and injectivity of `algebraMap`).
  --
  -- Inductively, assume `c j = c' j` for all `j < i`. Then
  --   `Spart c N - Spart c' N
  --     = (teichmuller(c i) - teichmuller(c' i)) * p^i + p^(i+1) * rest`
  -- in OQpCUn p. Combined with `p^(i+1) ∣ Spart c N - Spart c' N`, get
  -- `p ∣ teichmuller(c i) - teichmuller(c' i)`. Apply
  -- `WittVector.mem_span_p_pow_iff_le_coeff_eq_zero` (n=1) +
  -- `WittVector.le_coeff_eq_iff_le_sub_coeff_eq_zero` +
  -- `WittVector.teichmuller_coeff_zero` to extract `c i = c' i`.
  -- Lift back from ℕ to ℤ via the shift `k = m + i`.
  -- ==========================================================================
  -- Step 1. Define the unified cutoff `m`.
  set m : ℤ := min m₀ m₀' with hm_def
  have hm_le_m₀ : m ≤ m₀ := min_le_left _ _
  have hm_le_m₀' : m ≤ m₀' := min_le_right _ _
  have hb_below : ∀ k : ℤ, k < m → b k = 0 := fun k hk => hb k (lt_of_lt_of_le hk hm_le_m₀)
  have hb'_below : ∀ k : ℤ, k < m → b' k = 0 := fun k hk => hb' k (lt_of_lt_of_le hk hm_le_m₀')
  -- Step 2. ℕ-indexed digits.
  let c : ℕ → Fpbar p := fun i => b (m + i)
  let c' : ℕ → Fpbar p := fun i => b' (m + i)
  -- Step 3. Witt-integer partial sum.
  let Spart : (ℕ → Fpbar p) → ℕ → OQpCUn p := fun d N =>
    ∑ i ∈ Finset.Iic N, (p : OQpCUn p)^i * teichmuller p (d i)
  -- p ≠ 0 in QpCUn p (used throughout)
  have hp_ne : (p : QpCUn p) ≠ 0 := by
    rw [show (p : QpCUn p) = algebraMap (OQpCUn p) (QpCUn p) (p : OQpCUn p) from by
      push_cast; rfl]
    exact fun h => WittVector.p_nonzero p _
      ((IsFractionRing.injective (OQpCUn p) (QpCUn p))
        (by simpa using h))
  have hpn_val := valued_v_p_zpow (p := p)
  -- Step 4. Replace `Icc m₀ K`-sum with `Icc m K`-sum (extending b by 0).
  have hsum_eq_b : ∀ K : ℤ, ∑ k ∈ Finset.Icc m₀ K,
        (p : QpCUn p)^k * algebraMap (OQpCUn p) (QpCUn p) (teichmuller p (b k)) =
      ∑ k ∈ Finset.Icc m K,
        (p : QpCUn p)^k * algebraMap (OQpCUn p) (QpCUn p) (teichmuller p (b k)) := by
    intro K
    apply Finset.sum_subset
    · intro k hk
      rw [Finset.mem_Icc] at hk ⊢
      exact ⟨le_trans hm_le_m₀ hk.1, hk.2⟩
    · intro k hk hk_not
      rw [Finset.mem_Icc] at hk
      have hk_lt : k < m₀ := by
        by_contra hge
        push Not at hge
        exact hk_not (Finset.mem_Icc.mpr ⟨hge, hk.2⟩)
      rw [hb k hk_lt]
      simp
  have hsum_eq_b' : ∀ K : ℤ, ∑ k ∈ Finset.Icc m₀' K,
        (p : QpCUn p)^k * algebraMap (OQpCUn p) (QpCUn p) (teichmuller p (b' k)) =
      ∑ k ∈ Finset.Icc m K,
        (p : QpCUn p)^k * algebraMap (OQpCUn p) (QpCUn p) (teichmuller p (b' k)) := by
    intro K
    apply Finset.sum_subset
    · intro k hk
      rw [Finset.mem_Icc] at hk ⊢
      exact ⟨le_trans hm_le_m₀' hk.1, hk.2⟩
    · intro k hk hk_not
      rw [Finset.mem_Icc] at hk
      have hk_lt : k < m₀' := by
        by_contra hge
        push Not at hge
        exact hk_not (Finset.mem_Icc.mpr ⟨hge, hk.2⟩)
      rw [hb' k hk_lt]
      simp
  -- Step 5. Reindex `Icc m (m + N)` to `Iic N`, isolating `(p : QpCUn p)^m` factor.
  -- Step 5b. Connect `Icc m (m + N)`-sum to `algebraMap(Spart c N)`.
  have h_to_Spart : ∀ (d : ℕ → Fpbar p) (N : ℕ),
      ∑ i ∈ Finset.Iic N,
        algebraMap (OQpCUn p) (QpCUn p) (teichmuller p (d i)) * (p : QpCUn p)^i =
      algebraMap (OQpCUn p) (QpCUn p)
        (∑ i ∈ Finset.Iic N, (p : OQpCUn p)^i * teichmuller p (d i)) := by
    intro d N
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_mul, map_pow, mul_comm]
    push_cast
    rfl
  -- Step 6. Build the converging ℕ-indexed shifted sequence.
  -- σ N := algebraMap (Spart c N), σ' N := algebraMap (Spart c' N).
  -- Show σ N → z and σ' N → z, where z := (p : QpCUn p)^(-m) * y.
  set z : QpCUn p := (p : QpCUn p)^(-m) * y with hz_def
  have h_natTendsto : ∀ (d : ℕ → Fpbar p),
      Filter.Tendsto
        (fun K : ℤ => ∑ k ∈ Finset.Icc m K,
          (p : QpCUn p) ^ k * algebraMap (OQpCUn p) (QpCUn p) (teichmuller p (d (k - m).toNat)))
        Filter.atTop (nhds y) →
      Filter.Tendsto
        (fun N : ℕ => algebraMap (OQpCUn p) (QpCUn p) (Spart d N))
        Filter.atTop (nhds z) := by
    intro d hd
    -- Multiply by (p : QpCUn p)^(-m) on the left
    have h_mul : Filter.Tendsto
        (fun K : ℤ => (p : QpCUn p)^(-m) *
          ∑ k ∈ Finset.Icc m K, (p : QpCUn p)^k *
            algebraMap (OQpCUn p) (QpCUn p) (teichmuller p (d (k - m).toNat)))
        Filter.atTop (nhds ((p : QpCUn p)^(-m) * y)) := hd.const_mul _
    -- Compose with N ↦ m + N
    have h_compose : Filter.Tendsto (fun N : ℕ => m + (N : ℤ)) Filter.atTop Filter.atTop :=
      Filter.tendsto_atTop_add_const_left _ m tendsto_natCast_atTop_atTop
    have h_comp := h_mul.comp h_compose
    -- Rewrite using hreindex
    change Filter.Tendsto (fun N : ℕ => algebraMap (OQpCUn p) (QpCUn p) (Spart d N)) _ _
    apply h_comp.congr
    intro N
    simp only [Function.comp_apply]
    -- The sum at K = m + N reindexes: argument to teichmuller is d ((m + N - m).toNat) = d N
    -- Let's simplify the sum:
    have h_inner_eq : ∀ d : ℕ → Fpbar p, ∀ N : ℕ,
        ∑ k ∈ Finset.Icc m (m + (N : ℤ)),
          (p : QpCUn p)^k * algebraMap (OQpCUn p) (QpCUn p)
            (teichmuller p (d (k - m).toNat)) =
        (p : QpCUn p)^m * ∑ i ∈ Finset.Iic N,
          algebraMap (OQpCUn p) (QpCUn p) (teichmuller p (d i)) * (p : QpCUn p)^i := by
      intros d N
      have hIcc_eq : Finset.Icc m ((m : ℤ) + N) =
          (Finset.range (N + 1)).map (Nat.castEmbedding.trans <| addLeftEmbedding m) := by
        rw [Int.Icc_eq_finset_map]
        congr 1
        have h_simp : (m + (N : ℤ)) + 1 - m = (N : ℤ) + 1 := by ring
        rw [h_simp]
        simp
      rw [hIcc_eq, Finset.sum_map, ← Nat.range_succ_eq_Iic, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      simp only [Function.Embedding.trans_apply, Nat.castEmbedding_apply,
        addLeftEmbedding_apply]
      have h_toNat : ((m + (i : ℤ)) - m).toNat = i := by
        have h_simp_eq : (m + (i : ℤ)) - m = (i : ℤ) := by ring
        rw [h_simp_eq]
        simp
      rw [h_toNat]
      rw [zpow_add₀ hp_ne, zpow_natCast]
      ring
    rw [h_inner_eq d N]
    rw [show (p : QpCUn p)^(-m) * ((p : QpCUn p)^m * _) =
        ((p : QpCUn p)^(-m) * (p : QpCUn p)^m) *
        ∑ i ∈ Finset.Iic N,
          algebraMap (OQpCUn p) (QpCUn p) (teichmuller p (d i)) * (p : QpCUn p)^i from by ring]
    rw [show (p : QpCUn p)^(-m) * (p : QpCUn p)^m = (1 : QpCUn p) from by
      rw [← zpow_add₀ hp_ne]; rw [neg_add_cancel]; rw [zpow_zero]]
    rw [one_mul]
    rw [h_to_Spart d N]
  have hcb_to_z : Filter.Tendsto
      (fun N : ℕ => algebraMap (OQpCUn p) (QpCUn p) (Spart c N))
      Filter.atTop (nhds z) := by
    apply h_natTendsto c
    -- Need: Tendsto (fun K => ∑ k ∈ Icc m K, p^k * algebraMap (teichmuller p (c (k-m).toNat)))
    --       atTop (nhds y)
    -- Note c (k-m).toNat = b (m + (k-m).toNat).
    -- For k ≥ m, this equals b k. For k < m, b k = 0.
    -- So this is the original sum, just with different indexing.
    -- The original Tendsto from htb is over Icc m₀ K.
    -- Use Filter.Tendsto.congr' (eventually equal for K ≥ m).
    have h_eventual : ∀ᶠ K : ℤ in Filter.atTop,
        ∑ k ∈ Finset.Icc m K,
          (p : QpCUn p)^k * algebraMap (OQpCUn p) (QpCUn p) (teichmuller p (c (k - m).toNat)) =
        ∑ k ∈ Finset.Icc m₀ K,
          (p : QpCUn p)^k * algebraMap (OQpCUn p) (QpCUn p) (teichmuller p (b k)) := by
      filter_upwards [Filter.eventually_ge_atTop m] with K hKm
      have h_inner : ∑ k ∈ Finset.Icc m K,
            (p : QpCUn p)^k * algebraMap (OQpCUn p) (QpCUn p) (teichmuller p (c (k - m).toNat)) =
          ∑ k ∈ Finset.Icc m K,
            (p : QpCUn p)^k * algebraMap (OQpCUn p) (QpCUn p) (teichmuller p (b k)) := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [Finset.mem_Icc] at hk
        have h_toNat_eq : (k - m).toNat = (k - m).toNat := rfl
        have h_c_eq : c (k - m).toNat = b k := by
          change b (m + ((k - m).toNat : ℤ)) = b k
          have hkm : (0 : ℤ) ≤ k - m := by linarith
          rw [Int.toNat_of_nonneg hkm]
          ring_nf
        rw [h_c_eq]
      rw [h_inner, hsum_eq_b K]
    exact Filter.Tendsto.congr' (Filter.EventuallyEq.symm h_eventual) htb
  have hcb'_to_z : Filter.Tendsto
      (fun N : ℕ => algebraMap (OQpCUn p) (QpCUn p) (Spart c' N))
      Filter.atTop (nhds z) := by
    apply h_natTendsto c'
    have h_eventual : ∀ᶠ K : ℤ in Filter.atTop,
        ∑ k ∈ Finset.Icc m K,
          (p : QpCUn p)^k * algebraMap (OQpCUn p) (QpCUn p) (teichmuller p (c' (k - m).toNat)) =
        ∑ k ∈ Finset.Icc m₀' K,
          (p : QpCUn p)^k * algebraMap (OQpCUn p) (QpCUn p) (teichmuller p (b' k)) := by
      filter_upwards [Filter.eventually_ge_atTop m] with K hKm
      have h_inner : ∑ k ∈ Finset.Icc m K,
            (p : QpCUn p)^k * algebraMap (OQpCUn p) (QpCUn p) (teichmuller p (c' (k - m).toNat)) =
          ∑ k ∈ Finset.Icc m K,
            (p : QpCUn p)^k * algebraMap (OQpCUn p) (QpCUn p) (teichmuller p (b' k)) := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [Finset.mem_Icc] at hk
        have h_c'_eq : c' (k - m).toNat = b' k := by
          change b' (m + ((k - m).toNat : ℤ)) = b' k
          have hkm : (0 : ℤ) ≤ k - m := by linarith
          rw [Int.toNat_of_nonneg hkm]
          ring_nf
        rw [h_c'_eq]
      rw [h_inner, hsum_eq_b' K]
    exact Filter.Tendsto.congr' (Filter.EventuallyEq.symm h_eventual) htb'
  -- Difference tends to 0.
  have hdiff_tendsto : Filter.Tendsto
      (fun N : ℕ => algebraMap (OQpCUn p) (QpCUn p) (Spart c N - Spart c' N))
      Filter.atTop (nhds 0) := by
    have h := hcb_to_z.sub hcb'_to_z
    simp only [sub_self] at h
    apply h.congr
    intro N
    rw [map_sub]
  -- Step 7. For each i, find N with `(p : OQpCUn p)^(i+1) ∣ Spart c N - Spart c' N`.
  have h_eventual_div : ∀ i : ℕ, ∃ N : ℕ, N ≥ i ∧
      (p : OQpCUn p)^(i+1) ∣ (Spart c N - Spart c' N) := by
    intro i
    -- Eventually `Valued.v (algebraMap (Spart c N - Spart c' N)) < ofAdd(-i)`,
    -- which gives `≤ ofAdd(-(i+1))` since values are discrete.
    -- Use the `mem_nhds_zero_v_lt` helper (v4.31 phrases the nhds basis via `ValueGroup₀`).
    set cval : WithZero (Multiplicative ℤ) :=
      ((Multiplicative.ofAdd (-(i : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))
      with hcval_def
    have h_nhds :
        {a : QpCUn p | Valued.v a < cval} ∈ nhds (0 : QpCUn p) :=
      mem_nhds_zero_v_lt WithZero.coe_ne_zero
    have h_eventual : ∀ᶠ N : ℕ in Filter.atTop,
        algebraMap (OQpCUn p) (QpCUn p) (Spart c N - Spart c' N) ∈
          {a : QpCUn p | Valued.v a < cval} := hdiff_tendsto h_nhds
    rw [Filter.eventually_atTop] at h_eventual
    obtain ⟨N₀, hN₀⟩ := h_eventual
    refine ⟨max N₀ i, le_max_right _ _, ?_⟩
    set N := max N₀ i
    have hN_ge : N₀ ≤ N := le_max_left _ _
    have h_lt : Valued.v (algebraMap (OQpCUn p) (QpCUn p) (Spart c N - Spart c' N)) <
        ((Multiplicative.ofAdd (-(i : ℤ)) : Multiplicative ℤ) : WithZero _) := by
      rw [← hcval_def]; exact hN₀ N hN_ge
    -- From v(...) < ofAdd(-i), deduce v(...) ≤ ofAdd(-(i+1)).
    have h_le : Valued.v (algebraMap (OQpCUn p) (QpCUn p) (Spart c N - Spart c' N)) ≤
        ((Multiplicative.ofAdd (-((i : ℤ) + 1)) : Multiplicative ℤ) : WithZero _) := by
      rcases eq_or_ne (Valued.v (algebraMap (OQpCUn p) (QpCUn p) (Spart c N - Spart c' N))) 0
        with h0 | h0
      · rw [h0]; exact bot_le
      · rw [← WithZero.coe_unzero h0]
        rw [← WithZero.coe_unzero h0] at h_lt
        rw [WithZero.coe_lt_coe] at h_lt
        rw [WithZero.coe_le_coe]
        rw [show (WithZero.unzero h0) =
            Multiplicative.ofAdd (Multiplicative.toAdd (WithZero.unzero h0)) from rfl] at h_lt ⊢
        rw [Multiplicative.ofAdd_lt] at h_lt
        rw [Multiplicative.ofAdd_le]
        omega
    -- Now use the DVR uniformizer characterization to get divisibility.
    -- Strategy: lift `algebraMap(diff) * (p : QpCUn p)^(-(i+1))` back to OQpCUn p.
    -- Its valuation is ≤ ofAdd(0) = 1, so it's in OQpCUn p.
    set diff : OQpCUn p := Spart c N - Spart c' N with hdiff_def
    set q : QpCUn p :=
      algebraMap (OQpCUn p) (QpCUn p) diff * (p : QpCUn p)^(-((i : ℤ)+1)) with hq_def
    have hq_val_le_one : Valued.v q ≤ 1 := by
      rw [hq_def, Valuation.map_mul, hpn_val (-((i : ℤ)+1))]
      rw [show (-(-((i : ℤ)+1))) = (i : ℤ)+1 from by ring]
      have h_prod : Valued.v (algebraMap (OQpCUn p) (QpCUn p) diff) *
          ((Multiplicative.ofAdd ((i : ℤ)+1) : Multiplicative ℤ) : WithZero _) ≤
          ((Multiplicative.ofAdd (-((i : ℤ)+1)) : Multiplicative ℤ) : WithZero _) *
          ((Multiplicative.ofAdd ((i : ℤ)+1) : Multiplicative ℤ) : WithZero _) :=
        mul_le_mul_left h_le _
      have h_one : ((Multiplicative.ofAdd (-((i : ℤ)+1)) : Multiplicative ℤ) : WithZero _) *
          ((Multiplicative.ofAdd ((i : ℤ)+1) : Multiplicative ℤ) : WithZero _) =
          (1 : WithZero (Multiplicative ℤ)) := by
        rw [← WithZero.coe_mul]
        rw [show (Multiplicative.ofAdd (-((i : ℤ)+1)) * Multiplicative.ofAdd ((i : ℤ)+1)
              : Multiplicative ℤ) = 1 from by
          rw [← ofAdd_add]; rw [neg_add_cancel]; rfl]
        rfl
      rw [h_one] at h_prod
      exact h_prod
    obtain ⟨q', hq'⟩ := exists_lift_of_valued_le_one hq_val_le_one
    -- q' lifts q. Now show diff = (p : OQpCUn p)^(i+1) * q'.
    have h_eq_QpCUn : algebraMap (OQpCUn p) (QpCUn p) diff =
        (p : QpCUn p)^((i : ℤ)+1) * algebraMap (OQpCUn p) (QpCUn p) q' := by
      rw [hq']; rw [hq_def]
      rw [show (p : QpCUn p)^((i : ℤ)+1) *
          (algebraMap (OQpCUn p) (QpCUn p) diff * (p : QpCUn p)^(-((i : ℤ)+1))) =
          algebraMap (OQpCUn p) (QpCUn p) diff *
          ((p : QpCUn p)^((i : ℤ)+1) * (p : QpCUn p)^(-((i : ℤ)+1))) from by ring]
      rw [show (p : QpCUn p)^((i : ℤ)+1) * (p : QpCUn p)^(-((i : ℤ)+1)) = 1 from by
        rw [← zpow_add₀ hp_ne]; rw [add_neg_cancel]; rw [zpow_zero]]
      rw [mul_one]
    -- Convert (p : QpCUn p)^((i:ℤ)+1) to a coercion of (p : OQpCUn p)^(i+1).
    -- (v4.31: `ℚᶜᵘⁿ_[p]` is a `WithVal` structure with its own `Pow ℤ`, so `rw [zpow_natCast]`
    -- no longer matches syntactically; apply it in term mode instead.)
    have h_pow_alg : (p : QpCUn p)^((i : ℤ)+1) =
        algebraMap (OQpCUn p) (QpCUn p) ((p : OQpCUn p)^(i+1)) := by
      have hz : (p : QpCUn p)^((i : ℤ)+1) = (p : QpCUn p)^(i+1) := by
        rw [show ((i : ℤ)+1) = ((i+1 : ℕ) : ℤ) from by push_cast; ring]; exact zpow_natCast _ _
      rw [hz, map_pow, map_natCast]
    rw [h_pow_alg, ← map_mul] at h_eq_QpCUn
    have h_eq_OQpCUn : diff = (p : OQpCUn p)^(i+1) * q' :=
      IsFractionRing.injective (OQpCUn p) (QpCUn p) h_eq_QpCUn
    exact ⟨q', h_eq_OQpCUn⟩
  -- Step 8. Inductively prove c i = c' i for all i : ℕ.
  -- Helper: for j ≤ i with c k = c' k for k < i, expand the difference.
  have h_induction : ∀ i : ℕ, c i = c' i := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      have h_ih : ∀ j < i, c j = c' j := fun j hj => ih j hj
      -- Get N ≥ i with (p : OQpCUn p)^(i+1) ∣ Spart c N - Spart c' N.
      obtain ⟨N, hNi, hN_dvd⟩ := h_eventual_div i
      -- Decompose Spart c N - Spart c' N.
      -- Each summand: (p : OQpCUn p)^k * teichmuller p (c k)
      --             - (p : OQpCUn p)^k * teichmuller p (c' k)
      --             = (p : OQpCUn p)^k * (teichmuller p (c k) - teichmuller p (c' k))
      have h_diff_expand : Spart c N - Spart c' N =
          ∑ k ∈ Finset.Iic N, (p : OQpCUn p)^k *
            (teichmuller p (c k) - teichmuller p (c' k)) := by
        change (∑ k ∈ Finset.Iic N, (p : OQpCUn p)^k * teichmuller p (c k)) -
              (∑ k ∈ Finset.Iic N, (p : OQpCUn p)^k * teichmuller p (c' k)) = _
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro k _
        ring
      -- Use the IH to drop the first i terms (they vanish).
      have h_drop : Spart c N - Spart c' N =
          ∑ k ∈ Finset.Iic N \ Finset.range i, (p : OQpCUn p)^k *
            (teichmuller p (c k) - teichmuller p (c' k)) := by
        rw [h_diff_expand]
        rw [show ∑ k ∈ Finset.Iic N, (p : OQpCUn p)^k *
              (teichmuller p (c k) - teichmuller p (c' k)) =
            (∑ k ∈ Finset.Iic N ∩ Finset.range i, (p : OQpCUn p)^k *
              (teichmuller p (c k) - teichmuller p (c' k))) +
            (∑ k ∈ Finset.Iic N \ Finset.range i, (p : OQpCUn p)^k *
              (teichmuller p (c k) - teichmuller p (c' k))) from
            (Finset.sum_inter_add_sum_sdiff (Finset.Iic N) (Finset.range i) _).symm]
        have h_zero : ∑ k ∈ Finset.Iic N ∩ Finset.range i,
            (p : OQpCUn p)^k * (teichmuller p (c k) - teichmuller p (c' k)) = 0 := by
          apply Finset.sum_eq_zero
          intro k hk
          rw [Finset.mem_inter, Finset.mem_range] at hk
          rw [h_ih k hk.2]
          ring
        rw [h_zero, zero_add]
      -- Reindex: Iic N \ range i = Icc i N (since i ≤ N).
      have h_reindex_set : Finset.Iic N \ Finset.range i = Finset.Icc i N := by
        ext k
        simp only [Finset.mem_sdiff, Finset.mem_Iic, Finset.mem_range,
          Finset.mem_Icc, not_lt]
        tauto
      rw [h_reindex_set] at h_drop
      -- Reindex Icc i N to range (N - i + 1) shifted by i: k = i + j.
      have h_reindex_full : ∑ k ∈ Finset.Icc i N, (p : OQpCUn p)^k *
            (teichmuller p (c k) - teichmuller p (c' k)) =
          (p : OQpCUn p)^i * ∑ j ∈ Finset.range (N - i + 1), (p : OQpCUn p)^j *
            (teichmuller p (c (i + j)) - teichmuller p (c' (i + j))) := by
        rw [show Finset.Icc i N =
            (Finset.range (N - i + 1)).map ⟨fun j => i + j, by
              intros a b h; simp only at h; omega⟩ from ?_]
        · rw [Finset.sum_map, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          change (p : OQpCUn p)^(i + j) *
            (teichmuller p (c (i + j)) - teichmuller p (c' (i + j))) = _
          rw [show (p : OQpCUn p)^(i + j) = (p : OQpCUn p)^i * (p : OQpCUn p)^j from pow_add _ _ _]
          ring
        · ext k
          simp only [Finset.mem_Icc, Finset.mem_map, Finset.mem_range]
          constructor
          · intro ⟨hk1, hk2⟩
            refine ⟨k - i, by omega, ?_⟩
            change i + (k - i) = k
            omega
          · rintro ⟨j, hj, hjk⟩
            have hk : i + j = k := hjk
            omega
      -- Now extract p^i factor.
      have h_factored : Spart c N - Spart c' N = (p : OQpCUn p)^i *
          ∑ j ∈ Finset.range (N - i + 1), (p : OQpCUn p)^j *
            (teichmuller p (c (i + j)) - teichmuller p (c' (i + j))) := by
        rw [h_drop, h_reindex_full]
      -- From divisibility p^(i+1) ∣ Spart c N - Spart c' N = p^i * X, deduce p ∣ X.
      obtain ⟨q', hq'⟩ := hN_dvd
      have h_eq : (p : OQpCUn p)^i *
          ∑ j ∈ Finset.range (N - i + 1), (p : OQpCUn p)^j *
            (teichmuller p (c (i + j)) - teichmuller p (c' (i + j))) =
          (p : OQpCUn p)^(i+1) * q' := by
        rw [← h_factored]; exact hq'
      have h_p_pow_succ : (p : OQpCUn p)^(i+1) = (p : OQpCUn p)^i * (p : OQpCUn p) := by
        rw [pow_succ]
      rw [h_p_pow_succ, mul_assoc] at h_eq
      have hpi_ne : (p : OQpCUn p)^i ≠ 0 := by
        apply pow_ne_zero
        exact WittVector.p_nonzero p _
      have h_X_eq : ∑ j ∈ Finset.range (N - i + 1), (p : OQpCUn p)^j *
            (teichmuller p (c (i + j)) - teichmuller p (c' (i + j))) =
          (p : OQpCUn p) * q' :=
        mul_left_cancel₀ hpi_ne h_eq
      -- Split the X sum into j=0 term + p * (rest).
      have h_split : ∑ j ∈ Finset.range (N - i + 1), (p : OQpCUn p)^j *
            (teichmuller p (c (i + j)) - teichmuller p (c' (i + j))) =
          (teichmuller p (c i) - teichmuller p (c' i)) +
          (p : OQpCUn p) * ∑ j ∈ Finset.range (N - i), (p : OQpCUn p)^j *
            (teichmuller p (c (i + 1 + j)) - teichmuller p (c' (i + 1 + j))) := by
        rw [Finset.sum_range_succ', add_comm]
        simp only [pow_zero, one_mul, Nat.add_zero]
        congr 1
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        rw [show i + (j + 1) = i + 1 + j from by ring]
        rw [show (p : OQpCUn p)^(j + 1) = (p : OQpCUn p) * (p : OQpCUn p)^j from by
          rw [pow_succ]; ring]
        ring
      -- So `(t(c i) - t(c' i)) + p * Y = p * q'`, hence `p ∣ t(c i) - t(c' i)`.
      rw [h_split] at h_X_eq
      have h_p_div : (p : OQpCUn p) ∣ teichmuller p (c i) - teichmuller p (c' i) := by
        refine ⟨q' -
            ∑ j ∈ Finset.range (N - i), (p : OQpCUn p)^j *
              (teichmuller p (c (i + 1 + j)) - teichmuller p (c' (i + 1 + j))), ?_⟩
        linear_combination h_X_eq
      -- Use mem_span_p_pow_iff_le_coeff_eq_zero (with n = 1)
      have h_in_span : teichmuller p (c i) - teichmuller p (c' i) ∈
          Ideal.span {(p : OQpCUn p)^1} := by
        rw [pow_one]
        rwa [Ideal.mem_span_singleton]
      rw [WittVector.mem_span_p_pow_iff_le_coeff_eq_zero] at h_in_span
      -- h_in_span : ∀ m < 1, (teichmuller(c i) - teichmuller(c' i)).coeff m = 0
      have h_coeff_zero : (teichmuller p (c i) - teichmuller p (c' i)).coeff 0 = 0 :=
        h_in_span 0 (by omega)
      -- Use `le_coeff_eq_iff_le_sub_coeff_eq_zero` to translate:
      -- (teichmuller(c i) - teichmuller(c' i)).coeff 0 = 0
      --   ↔ (teichmuller(c i)).coeff 0 = (teichmuller(c' i)).coeff 0
      have h_coeffs_eq :
          ∀ j < 1, (teichmuller p (c i)).coeff j = (teichmuller p (c' i)).coeff j := by
        rw [WittVector.le_coeff_eq_iff_le_sub_coeff_eq_zero]
        intro j hj
        interval_cases j
        exact h_coeff_zero
      have h_at_zero := h_coeffs_eq 0 (by omega)
      rw [WittVector.teichmuller_coeff_zero, WittVector.teichmuller_coeff_zero] at h_at_zero
      exact h_at_zero
  -- Step 9. Lift back to ℤ.
  intro k
  by_cases hk : k < m
  · rw [hb_below k hk, hb'_below k hk]
  · push Not at hk
    have hk_eq : k = m + ((k - m).toNat : ℤ) := by
      rw [Int.toNat_of_nonneg (by linarith)]
      ring
    have h_c_eq : c (k - m).toNat = b k := by
      change b (m + ((k - m).toNat : ℤ)) = b k
      rw [← hk_eq]
    have h_c'_eq : c' (k - m).toNat = b' k := by
      change b' (m + ((k - m).toNat : ℤ)) = b' k
      rw [← hk_eq]
    rw [← h_c_eq, ← h_c'_eq]
    exact h_induction (k - m).toNat

end existsCanonicalExpansionAux

set_option maxHeartbeats 250000 in
-- maxHeartbeats: heavy elaboration in the multi-phase proof body
/--
**Existence of a Teichmuller-style canonical expansion**.

For every `α : LiftedPAdicHahnSeries p`, there exists `s : ℚ → Fpbar p` with
PWO support such that `α - LiftedPAdicHahnSeries.fromCoeff s hspwo` is a null
series (i.e. lies in `NullSeriesIdeal p`).

The construction (per Poonen1993, p. 6):
for each coset rep `g ∈ Set.Ico 0 1`, take `f_g := ∑_{n∈ℤ} α_{g+n} p^n ∈ ℚᶜᵘⁿ_[p]`,
shift to land in the integers, and read off coefficients via Mathlib's
`WittVector.dvd_sub_sum_teichmuller_iterateFrobeniusEquiv_coeff`.

This proof relies on `existsCanonicalExpansionAux.exists_lim_intPartial`,
`existsCanonicalExpansionAux.exists_teichmuller_digits`, and the
support-PWO bound combining `Set.IsPWO.add` with
`existsCanonicalExpansionAux.natRange_isPWO`.
-/
theorem exists_canonical_representative {p : ℕ} [Fact (Nat.Prime p)]
    (α : LiftedPAdicHahnSeries p) :
    ∃ (s : ℚ → Fpbar p) (hspwo : (Function.support s).IsPWO),
      α - LiftedPAdicHahnSeries.fromCoeff s hspwo ∈ NullSeriesIdeal p := by
  classical
  -- ============================================================
  -- SETUP: hp_ne, hpn_val
  -- ============================================================
  have hp_ne : (p : QpCUn p) ≠ 0 := by
    rw [show (p : QpCUn p) = algebraMap (OQpCUn p) (QpCUn p) (p : OQpCUn p) from by
      push_cast; rfl]
    exact fun h_zero => WittVector.p_nonzero p _
      ((IsFractionRing.injective (OQpCUn p) (QpCUn p))
        (by simpa using h_zero))
  have hpn_val := valued_v_p_zpow (p := p)
  have hp_term_val : ∀ (a : Fpbar p) (n : ℤ), a ≠ 0 →
      Valued.v ((p : QpCUn p)^n * algebraMap (OQpCUn p) (QpCUn p) (teichmuller p a)) =
        ((Multiplicative.ofAdd (-n : ℤ) : Multiplicative ℤ) : WithZero _) := by
    intro a n ha
    rw [Valuation.map_mul, hpn_val n]
    -- teichmuller p a is a unit in OQpCUn p when a ≠ 0
    have h_a_unit : IsUnit a := isUnit_iff_ne_zero.mpr ha
    have h_teich_unit : IsUnit (teichmuller p a) := h_a_unit.map (teichmuller p)
    -- For a unit u in OQpCUn p, Valued.v(algMap u) = 1
    have h_val_one : Valued.v (algebraMap (OQpCUn p) (QpCUn p) (teichmuller p a)) = 1 := by
      rcases h_teich_unit with ⟨u, hu⟩
      rw [← hu, valued_v_algebraMap_unit_one u]
    rw [h_val_one, mul_one]
  -- ============================================================
  -- Per-γ data: f γ, b γ, m_b γ
  -- ============================================================
  set f : ℚ → QpCUn p := fun γ =>
    (existsCanonicalExpansionAux.exists_lim_intPartial α γ).choose with hf_def
  have hf_spec : ∀ γ, Filter.Tendsto (intPartial α γ) Filter.atTop (nhds (f γ)) :=
    fun γ => (existsCanonicalExpansionAux.exists_lim_intPartial α γ).choose_spec
  set b : ℚ → ℤ → Fpbar p := fun γ =>
    (existsCanonicalExpansionAux.exists_teichmuller_digits (f γ)).choose with hb_def
  set m_b : ℚ → ℤ := fun γ =>
    (existsCanonicalExpansionAux.exists_teichmuller_digits (f γ)).choose_spec.choose with hmb_def
  have hb_spec : ∀ γ : ℚ,
      (∀ k : ℤ, k < m_b γ → b γ k = 0) ∧
      Filter.Tendsto
        (fun K : ℤ => ∑ k ∈ Finset.Icc (m_b γ) K,
          (p : QpCUn p) ^ k * algebraMap (OQpCUn p) (QpCUn p) (teichmuller p (b γ k)))
        Filter.atTop (nhds (f γ)) := fun γ =>
    (existsCanonicalExpansionAux.exists_teichmuller_digits (f γ)).choose_spec.choose_spec
  have hb_vanish : ∀ γ k, k < m_b γ → b γ k = 0 := fun γ => (hb_spec γ).1
  have hb_tendsto : ∀ γ, Filter.Tendsto
      (fun K : ℤ => ∑ k ∈ Finset.Icc (m_b γ) K,
        (p : QpCUn p) ^ k * algebraMap (OQpCUn p) (QpCUn p) (teichmuller p (b γ k)))
      Filter.atTop (nhds (f γ)) := fun γ => (hb_spec γ).2
  -- ============================================================
  -- Key claim: ∀ γ k, b γ k ≠ 0 → ∃ n_α ≤ k with α.coeff (γ + n_α) ≠ 0.
  -- Proof via strict ultrametric.
  -- ============================================================
  have h_key : ∀ γ : ℚ, ∀ k : ℤ, b γ k ≠ 0 →
      ∃ n_α : ℤ, n_α ≤ k ∧ α.coeff (γ + n_α) ≠ 0 := by
    intro γ k hbk
    -- Step 0: Define k_min := smallest j ≥ m_b γ with b γ j ≠ 0.
    have h_k_in : k ∈ {j : ℤ | m_b γ ≤ j ∧ b γ j ≠ 0} := by
      refine ⟨?_, hbk⟩
      by_contra h_nge
      push Not at h_nge
      exact hbk (hb_vanish γ k h_nge)
    have hbset_ne : ({j : ℤ | m_b γ ≤ j ∧ b γ j ≠ 0}).Nonempty := ⟨k, h_k_in⟩
    have hbset_bdd : BddBelow {j : ℤ | m_b γ ≤ j ∧ b γ j ≠ 0} := ⟨m_b γ, fun j hj => hj.1⟩
    obtain ⟨k_min, hk_min_mem, hk_min_le⟩ := Int.exists_least_of_bdd hbset_bdd hbset_ne
    -- Step 1: For K ≥ k_min, Valued.v(Icc m_b γ K sum) = ofAdd(-k_min) by strict ultrametric.
    have h_sum_eq : ∀ K : ℤ, k_min ≤ K → Valued.v (∑ j ∈ Finset.Icc (m_b γ) K,
          (p : QpCUn p) ^ j * algebraMap (OQpCUn p) (QpCUn p) (teichmuller p (b γ j))) =
        ((Multiplicative.ofAdd (-k_min : ℤ) : Multiplicative ℤ) : WithZero _) := by
      intro K hK
      have h_in : k_min ∈ Finset.Icc (m_b γ) K := Finset.mem_Icc.mpr ⟨hk_min_mem.1, hK⟩
      rw [show Finset.Icc (m_b γ) K = insert k_min ((Finset.Icc (m_b γ) K).erase k_min) from
        (Finset.insert_erase h_in).symm]
      rw [Finset.sum_insert (Finset.notMem_erase _ _)]
      rw [Valuation.map_add_eq_of_lt_left]
      · exact hp_term_val (b γ k_min) k_min hk_min_mem.2
      · -- v(rest) < ofAdd(-k_min)
        have h_bound : Valued.v (∑ j ∈ (Finset.Icc (m_b γ) K).erase k_min,
              (p : QpCUn p) ^ j * algebraMap (OQpCUn p) (QpCUn p) (teichmuller p (b γ j))) ≤
            ((Multiplicative.ofAdd (-(k_min + 1) : ℤ) : Multiplicative ℤ) : WithZero _) := by
          apply Valuation.map_sum_le
          intro j hj_mem
          rw [Finset.mem_erase, Finset.mem_Icc] at hj_mem
          by_cases h_zero : b γ j = 0
          · rw [h_zero, WittVector.teichmuller_zero, map_zero, mul_zero]
            rw [Valuation.map_zero]
            exact bot_le
          · have hj_in : j ∈ {i : ℤ | m_b γ ≤ i ∧ b γ i ≠ 0} := ⟨hj_mem.2.1, h_zero⟩
            have hj_ge : k_min ≤ j := hk_min_le j hj_in
            have hj_gt : k_min < j := lt_of_le_of_ne hj_ge (Ne.symm hj_mem.1)
            rw [hp_term_val (b γ j) j h_zero]
            rw [WithZero.coe_le_coe]
            exact Multiplicative.ofAdd_le.mpr (by omega)
        apply lt_of_le_of_lt h_bound
        rw [hp_term_val (b γ k_min) k_min hk_min_mem.2]
        rw [WithZero.coe_lt_coe]
        exact Multiplicative.ofAdd_lt.mpr (by omega)
    -- Step 2: We need to derive contradictions / equations using Tendsto.
    -- Helper: Tendsto + eventually constant valuation ⇒ Valued.v(limit) constraint.
    -- Specifically, if y ≠ 0 then Valued.v y equals the constant.
    -- If y = 0 and the constant is nonzero, contradiction.
    -- Apply with y = f γ.
    by_cases h_fγ : f γ = 0
    · -- f γ = 0 case: contradiction since Tendsto sum → 0 but eventually Valued.v(sum K) ≠ 0.
      exfalso
      -- Build a neighborhood of 0 that excludes the eventually-equal sum value.
      have h_nhds :
          {x : QpCUn p | Valued.v x <
              ((Multiplicative.ofAdd (-k_min : ℤ) : Multiplicative ℤ) : WithZero _)} ∈
            nhds (0 : QpCUn p) :=
        mem_nhds_zero_v_lt WithZero.coe_ne_zero
      have h_evtl_close : ∀ᶠ K : ℤ in Filter.atTop,
          Valued.v (∑ j ∈ Finset.Icc (m_b γ) K,
              (p : QpCUn p) ^ j * algebraMap (OQpCUn p) (QpCUn p) (teichmuller p (b γ j))) <
            ((Multiplicative.ofAdd (-k_min : ℤ) : Multiplicative ℤ) : WithZero _) := by
        have h_tend := hb_tendsto γ
        rw [h_fγ] at h_tend
        exact h_tend h_nhds
      have h_evtl_K_ge : ∀ᶠ K : ℤ in Filter.atTop, k_min ≤ K := Filter.eventually_ge_atTop k_min
      obtain ⟨K, hKge, hKclose⟩ := (h_evtl_K_ge.and h_evtl_close).exists
      rw [h_sum_eq K hKge] at hKclose
      exact lt_irrefl _ hKclose
    · -- f γ ≠ 0 case.
      -- Show Valued.v(f γ) = ofAdd(-k_min) using ultrametric stability.
      have h_v_fγ_eq : Valued.v (f γ) =
          ((Multiplicative.ofAdd (-k_min : ℤ) : Multiplicative ℤ) : WithZero _) := by
        -- Use that eventually Valued.v(sum K) = Valued.v(f γ) (valuation stability)
        -- AND eventually Valued.v(sum K) = ofAdd(-k_min) (h_sum_eq).
        -- Combine to get Valued.v(f γ) = ofAdd(-k_min).
        have h_v_fγ_ne : Valued.v (f γ) ≠ 0 := by rwa [Valuation.ne_zero_iff]
        have h_nhds_y :
            {x : QpCUn p | Valued.v (x - f γ) < Valued.v (f γ)} ∈ nhds (f γ) :=
          mem_nhds_v_sub_lt h_v_fγ_ne rfl
        have h_evtl_stable : ∀ᶠ K : ℤ in Filter.atTop,
            Valued.v ((∑ j ∈ Finset.Icc (m_b γ) K,
                (p : QpCUn p) ^ j *
                  algebraMap (OQpCUn p) (QpCUn p) (teichmuller p (b γ j))) - f γ) <
              Valued.v (f γ) := hb_tendsto γ h_nhds_y
        have h_evtl_K_ge : ∀ᶠ K : ℤ in Filter.atTop, k_min ≤ K :=
          Filter.eventually_ge_atTop k_min
        obtain ⟨K, hKge, hKstable⟩ := (h_evtl_K_ge.and h_evtl_stable).exists
        -- Now: Valued.v(sum K - f γ) < Valued.v(f γ).
        -- f γ = sum K - (sum K - f γ).
        -- By ultrametric strict: Valued.v(f γ) = Valued.v(sum K).
        have h_valeq : Valued.v (∑ j ∈ Finset.Icc (m_b γ) K,
              (p : QpCUn p) ^ j *
                algebraMap (OQpCUn p) (QpCUn p) (teichmuller p (b γ j))) =
              Valued.v (f γ) := by
          rw [show (∑ j ∈ Finset.Icc (m_b γ) K,
                (p : QpCUn p) ^ j *
                  algebraMap (OQpCUn p) (QpCUn p) (teichmuller p (b γ j))) =
              f γ + ((∑ j ∈ Finset.Icc (m_b γ) K,
                (p : QpCUn p) ^ j *
                  algebraMap (OQpCUn p) (QpCUn p) (teichmuller p (b γ j))) - f γ) from by ring]
          rw [Valuation.map_add_eq_of_lt_left]
          exact hKstable
        rw [← h_valeq, h_sum_eq K hKge]
      -- Slice nonempty
      set slice : Set ℤ := {n : ℤ | α.coeff (γ + n) ≠ 0} with hslice_def
      have h_slice_ne : slice.Nonempty := by
        -- f γ ≠ 0 ⟹ intPartial α γ has some nonzero K, which has some nonzero term.
        -- intPartial α γ K = 0 iff slice ∩ ≤K is empty.
        -- If slice is empty then intPartial α γ ≡ 0, hence f γ = 0. Contradiction.
        by_contra h_sl_e
        apply h_fγ
        have h_intP_zero : ∀ K : ℤ, intPartial α γ K = 0 := by
          intro K
          simp only [intPartial]
          apply Finset.sum_eq_zero
          intro n _
          have hn_mem : n.1 ≤ K ∧ α.coeff (γ + n.1) ≠ 0 :=
            (Set.Finite.mem_toFinset (hs := finiteBelowInt α γ K)).mp n.2
          exfalso
          apply h_sl_e
          exact ⟨n.1, hn_mem.2⟩
        have h := hf_spec γ
        rw [show (intPartial α γ) = (fun _ => (0 : QpCUn p)) from funext h_intP_zero] at h
        exact (tendsto_nhds_unique h tendsto_const_nhds)
      have hslice_bdd : BddBelow slice := by
        by_cases hsupp : α.support.Nonempty
        · refine ⟨⌈(α.isWF_support.min hsupp - γ : ℚ)⌉, ?_⟩
          intro n hn
          have hn_mem : (γ + (n : ℚ)) ∈ α.support := hn
          have hmin_le : α.isWF_support.min hsupp ≤ γ + n :=
            α.isWF_support.min_le hsupp hn_mem
          have : (α.isWF_support.min hsupp - γ : ℚ) ≤ (n : ℚ) := by linarith
          exact Int.ceil_le.mpr this
        · exfalso
          obtain ⟨n, hn⟩ := h_slice_ne
          apply hsupp
          exact ⟨γ + n, hn⟩
      obtain ⟨m, hm_mem, hm_min⟩ := Int.exists_least_of_bdd hslice_bdd h_slice_ne
      refine ⟨m, ?_, hm_mem⟩
      -- Need m ≤ k. Show via Valued.v(f γ) ≤ ofAdd(-m).
      have h_v_fγ_le : Valued.v (f γ) ≤
          ((Multiplicative.ofAdd (-m : ℤ) : Multiplicative ℤ) : WithZero _) := by
        -- Argue: eventually Valued.v(intPartial K) ≤ ofAdd(-m).
        -- Combined with eventually Valued.v(intPartial K) = Valued.v(f γ) (stability):
        -- Valued.v(f γ) ≤ ofAdd(-m).
        have h_intP_α_bound : ∀ K : ℤ, m ≤ K →
            Valued.v (intPartial α γ K) ≤
              ((Multiplicative.ofAdd (-m : ℤ) : Multiplicative ℤ) : WithZero _) := by
          intro K hK
          simp only [intPartial]
          rw [show (∑ n : Set.Finite.toFinset (finiteBelowInt α γ K),
                (p : QpCUn p) ^ n.1 *
                  algebraMap (OQpCUn p) (QpCUn p) (α.coeff (γ + n))) =
              ∑ n ∈ Set.Finite.toFinset (finiteBelowInt α γ K),
                (p : QpCUn p) ^ n *
                  algebraMap (OQpCUn p) (QpCUn p) (α.coeff (γ + n)) from
              Finset.sum_attach (s := Set.Finite.toFinset (finiteBelowInt α γ K))
                (f := fun n : ℤ => (p : QpCUn p) ^ n *
                  algebraMap (OQpCUn p) (QpCUn p) (α.coeff (γ + n)))]
          apply Valuation.map_sum_le
          intro n hn
          have hn_mem : n ≤ K ∧ α.coeff (γ + n) ≠ 0 :=
            (Set.Finite.mem_toFinset (hs := finiteBelowInt α γ K)).mp hn
          have hn_in_slice : n ∈ slice := hn_mem.2
          have hm_le_n : m ≤ n := hm_min n hn_in_slice
          rw [Valuation.map_mul, hpn_val n]
          have h_alg_le : Valued.v (algebraMap (OQpCUn p) (QpCUn p) (α.coeff (γ + n))) ≤ 1 :=
            (IsDiscreteValuationRing.maximalIdeal (OQpCUn p)).valuation_le_one (α.coeff (γ + n))
          calc ((Multiplicative.ofAdd (-n : ℤ) : Multiplicative ℤ) : WithZero _) *
                  Valued.v (algebraMap (OQpCUn p) (QpCUn p) (α.coeff (γ + n)))
              ≤ ((Multiplicative.ofAdd (-n : ℤ) : Multiplicative ℤ) : WithZero _) * 1 :=
                mul_le_mul' (le_refl _) h_alg_le
            _ = ((Multiplicative.ofAdd (-n : ℤ) : Multiplicative ℤ) : WithZero _) := mul_one _
            _ ≤ ((Multiplicative.ofAdd (-m : ℤ) : Multiplicative ℤ) : WithZero _) := by
                rw [WithZero.coe_le_coe]
                exact Multiplicative.ofAdd_le.mpr (by omega)
        -- Use ultrametric stability to get Valued.v(f γ) ≤ ofAdd(-m).
        have h_v_fγ_ne : Valued.v (f γ) ≠ 0 := by rwa [Valuation.ne_zero_iff]
        have h_nhds_y :
            {x : QpCUn p | Valued.v (x - f γ) < Valued.v (f γ)} ∈ nhds (f γ) :=
          mem_nhds_v_sub_lt h_v_fγ_ne rfl
        have h_evtl_stable : ∀ᶠ K : ℤ in Filter.atTop,
            Valued.v (intPartial α γ K - f γ) < Valued.v (f γ) := hf_spec γ h_nhds_y
        have h_evtl_K_ge : ∀ᶠ K : ℤ in Filter.atTop, m ≤ K := Filter.eventually_ge_atTop m
        obtain ⟨K, hKge, hKstable⟩ := (h_evtl_K_ge.and h_evtl_stable).exists
        have h_intP_le := h_intP_α_bound K hKge
        have h_v_intP_eq_fγ : Valued.v (intPartial α γ K) = Valued.v (f γ) := by
          rw [show intPartial α γ K =
              f γ + (intPartial α γ K - f γ) from by ring]
          rw [Valuation.map_add_eq_of_lt_left]
          exact hKstable
        rw [h_v_intP_eq_fγ] at h_intP_le
        exact h_intP_le
      rw [h_v_fγ_eq] at h_v_fγ_le
      rw [WithZero.coe_le_coe] at h_v_fγ_le
      have hk_min_ge_m : m ≤ k_min := by
        have := Multiplicative.ofAdd_le.mp h_v_fγ_le
        omega
      have hk_min_le_k : k_min ≤ k := hk_min_le k h_k_in
      omega
  -- ============================================================
  -- DEFINE s := fun q => b (Int.fract q) ⌊q⌋
  -- ============================================================
  set s : ℚ → Fpbar p := fun q => b (Int.fract q) ⌊q⌋ with hs_def
  -- ============================================================
  -- Show support s ⊆ support α + Set.range (Nat.cast : ℕ → ℚ)
  -- ============================================================
  open scoped Pointwise in
  have hsupp_sub : Function.support s ⊆ α.support + Set.range ((↑) : ℕ → ℚ) := by
    intro q hq
    simp only [hs_def, Function.mem_support] at hq
    -- hq : b (Int.fract q) ⌊q⌋ ≠ 0
    obtain ⟨n_α, hn_α_le, hn_α_ne⟩ := h_key (Int.fract q) ⌊q⌋ hq
    refine ⟨Int.fract q + n_α, hn_α_ne, ((⌊q⌋ - n_α).toNat : ℕ), ?_, ?_⟩
    · exact Set.mem_range_self _
    · -- Goal: Int.fract q + n_α + ((⌊q⌋ - n_α).toNat : ℚ) = q
      have h_pos : 0 ≤ ⌊q⌋ - n_α := sub_nonneg.mpr hn_α_le
      have h_toNat_int : ((⌊q⌋ - n_α).toNat : ℤ) = ⌊q⌋ - n_α := Int.toNat_of_nonneg h_pos
      have h_cast : ((⌊q⌋ - n_α).toNat : ℚ) = ((⌊q⌋ : ℤ) : ℚ) - (n_α : ℚ) := by
        have h1 : ((⌊q⌋ - n_α).toNat : ℚ) = (((⌊q⌋ - n_α).toNat : ℤ) : ℚ) := by push_cast; rfl
        rw [h1, h_toNat_int]
        push_cast
        ring
      have hf := Int.fract_add_floor q
      change Int.fract q + (n_α : ℚ) + ((⌊q⌋ - n_α).toNat : ℚ) = q
      rw [h_cast]
      linarith
  -- ============================================================
  -- support s.IsPWO
  -- ============================================================
  have hspwo : (Function.support s).IsPWO :=
    existsCanonicalExpansionAux.support_isPWO_of_subset_support_add_natRange α hsupp_sub
  refine ⟨s, hspwo, ?_⟩
  -- ============================================================
  -- IsNullSeries (α - fromCoeff s)
  -- ============================================================
  change IsNullSeries (α - LiftedPAdicHahnSeries.fromCoeff s hspwo)
  intro g
  set β : LiftedPAdicHahnSeries p := LiftedPAdicHahnSeries.fromCoeff s hspwo with hβ_def
  set γ : ℚ := Int.fract g with hγ_def
  set n₀ : ℤ := ⌊g⌋ with hn₀_def
  have hg_eq : g = γ + (n₀ : ℚ) := by
    have h := Int.fract_add_floor g
    change g = Int.fract g + (⌊g⌋ : ℚ)
    linarith
  have hγ_in_Ico : 0 ≤ γ ∧ γ < 1 := ⟨Int.fract_nonneg g, Int.fract_lt_one g⟩
  have hγ_self : Int.fract γ = γ := Int.fract_eq_self.mpr hγ_in_Ico
  have hβ_coeff : ∀ q : ℚ, β.coeff q = teichmuller p (s q) := fun _ => rfl
  -- ============================================================
  -- h_intPartial_eq_Icc — generalized over γ' parameter
  -- ============================================================
  have h_intPartial_eq_Icc :
      ∀ (γ' : ℚ) (β' : LiftedPAdicHahnSeries p) (t : ℚ → Fpbar p) (m : ℤ),
        (∀ q : ℚ, β'.coeff q = teichmuller p (t q)) →
        (∀ k : ℤ, k < m → t (γ' + k) = 0) →
        ∀ K : ℤ, m ≤ K →
        intPartial β' γ' K =
          ∑ k ∈ Finset.Icc m K,
            (p : QpCUn p) ^ k * algebraMap (OQpCUn p) (QpCUn p) (teichmuller p (t (γ' + k))) := by
    intro γ' β' t m hβ'_coeff hm K hK
    have h_step1 : intPartial β' γ' K =
        ∑ n ∈ Set.Finite.toFinset (finiteBelowInt β' γ' K),
          (p : QpCUn p) ^ n * algebraMap (OQpCUn p) (QpCUn p) (β'.coeff (γ' + n)) := by
      simp only [intPartial]
      exact Finset.sum_attach (s := Set.Finite.toFinset (finiteBelowInt β' γ' K))
        (f := fun n : ℤ => (p : QpCUn p) ^ n * algebraMap (OQpCUn p) (QpCUn p) (β'.coeff (γ' + n)))
    rw [h_step1]
    have h_subset : Set.Finite.toFinset (finiteBelowInt β' γ' K) ⊆ Finset.Icc m K := by
      intro n hn
      have hn_mem : n ≤ K ∧ β'.coeff (γ' + n) ≠ 0 :=
        (Set.Finite.mem_toFinset (hs := finiteBelowInt β' γ' K)).mp hn
      have h_t_ne : t (γ' + n) ≠ 0 := by
        intro h_zero
        apply hn_mem.2
        rw [hβ'_coeff (γ' + n), h_zero]
        exact WittVector.teichmuller_zero p
      have h_n_ge : m ≤ n := by
        by_contra h_lt
        push Not at h_lt
        exact h_t_ne (hm n h_lt)
      exact Finset.mem_Icc.mpr ⟨h_n_ge, hn_mem.1⟩
    have h_extend : ∑ n ∈ Set.Finite.toFinset (finiteBelowInt β' γ' K),
          (p : QpCUn p) ^ n * algebraMap (OQpCUn p) (QpCUn p) (β'.coeff (γ' + n)) =
        ∑ n ∈ Finset.Icc m K,
          (p : QpCUn p) ^ n * algebraMap (OQpCUn p) (QpCUn p) (β'.coeff (γ' + n)) := by
      apply Finset.sum_subset h_subset
      intro n hn_Icc hn_not
      rw [Finset.mem_Icc] at hn_Icc
      have h_β_zero : β'.coeff (γ' + n) = 0 := by
        by_contra hne
        apply hn_not
        exact (Set.Finite.mem_toFinset (hs := finiteBelowInt β' γ' K)).mpr ⟨hn_Icc.2, hne⟩
      rw [h_β_zero]
      simp
    rw [h_extend]
    apply Finset.sum_congr rfl
    intro n _
    rw [hβ'_coeff (γ' + n)]
  -- ============================================================
  -- intPartial β γ K → f γ via h_intPartial_eq_Icc + hb_tendsto
  -- ============================================================
  have hs_eq_b : ∀ k : ℤ, s (γ + (k : ℚ)) = b γ k := by
    intro k
    change b (Int.fract (γ + (k : ℚ))) ⌊(γ : ℚ) + (k : ℚ)⌋ = b γ k
    have h_fract : Int.fract ((γ : ℚ) + (k : ℚ)) = γ := by
      rw [Int.fract_add_intCast γ k]
      exact hγ_self
    have h_floor : ⌊(γ : ℚ) + (k : ℚ)⌋ = k := by
      rw [Int.floor_add_intCast γ k]
      have hγ_floor : ⌊(γ : ℚ)⌋ = 0 := by
        apply Int.floor_eq_zero_iff.mpr
        exact ⟨hγ_in_Ico.1, hγ_in_Ico.2⟩
      rw [hγ_floor, zero_add]
    rw [h_fract, h_floor]
  have h_vanish_γ : ∀ k : ℤ, k < m_b γ → s (γ + (k : ℚ)) = 0 := by
    intro k hk
    rw [hs_eq_b k]; exact hb_vanish γ k hk
  have h_β_eq_γ : ∀ K : ℤ, m_b γ ≤ K →
      intPartial β γ K =
        ∑ k ∈ Finset.Icc (m_b γ) K,
          (p : QpCUn p) ^ k * algebraMap (OQpCUn p) (QpCUn p) (teichmuller p (b γ k)) := by
    intro K hK
    rw [h_intPartial_eq_Icc γ β s (m_b γ) hβ_coeff h_vanish_γ K hK]
    apply Finset.sum_congr rfl
    intro k _
    rw [hs_eq_b k]
  have h_tendsto_β_γ : Filter.Tendsto (intPartial β γ) Filter.atTop (nhds (f γ)) := by
    apply (hb_tendsto γ).congr'
    rw [Filter.EventuallyEq]
    filter_upwards [Filter.eventually_ge_atTop (m_b γ)] with K hK
    exact (h_β_eq_γ K hK).symm
  -- ============================================================
  -- Translation: intPartial β' g K = (p:QpCUn)^(-n₀) * intPartial β' γ (K + n₀)
  -- ============================================================
  have h_translate : ∀ (β' : LiftedPAdicHahnSeries p) (K : ℤ),
      intPartial β' g K = (p : QpCUn p) ^ (-n₀) * intPartial β' γ (K + n₀) := by
    intro β' K
    have hL : intPartial β' g K =
        ∑ n ∈ Set.Finite.toFinset (finiteBelowInt β' g K),
          (p : QpCUn p) ^ n * algebraMap (OQpCUn p) (QpCUn p) (β'.coeff (g + n)) := by
      simp only [intPartial]
      exact Finset.sum_attach (s := Set.Finite.toFinset (finiteBelowInt β' g K))
        (f := fun n : ℤ => (p : QpCUn p) ^ n * algebraMap (OQpCUn p) (QpCUn p) (β'.coeff (g + n)))
    have hR : intPartial β' γ (K + n₀) =
        ∑ n ∈ Set.Finite.toFinset (finiteBelowInt β' γ (K + n₀)),
          (p : QpCUn p) ^ n * algebraMap (OQpCUn p) (QpCUn p) (β'.coeff (γ + n)) := by
      simp only [intPartial]
      exact Finset.sum_attach (s := Set.Finite.toFinset (finiteBelowInt β' γ (K + n₀)))
        (f := fun n : ℤ => (p : QpCUn p) ^ n * algebraMap (OQpCUn p) (QpCUn p) (β'.coeff (γ + n)))
    rw [hL, hR]
    have h_image : Set.Finite.toFinset (finiteBelowInt β' γ (K + n₀)) =
        (Set.Finite.toFinset (finiteBelowInt β' g K)).image (fun n : ℤ => n + n₀) := by
      ext n'
      simp only [Set.Finite.mem_toFinset, Finset.mem_image, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨n' - n₀, ⟨by omega, ?_⟩, by omega⟩
        have h_eq_q : (g : ℚ) + ((n' - n₀ : ℤ) : ℚ) = (γ : ℚ) + (n' : ℚ) := by
          push_cast
          rw [hg_eq]; ring
        rw [h_eq_q]; exact h2
      · rintro ⟨n, ⟨hn1, hn2⟩, h_eq⟩
        refine ⟨by omega, ?_⟩
        have h_eq_q : (γ : ℚ) + (n' : ℚ) = (g : ℚ) + (n : ℚ) := by
          have h_n' : (n' : ℚ) = ((n + n₀ : ℤ) : ℚ) := by exact_mod_cast h_eq.symm
          rw [h_n']; push_cast; rw [hg_eq]; ring
        rw [h_eq_q]; exact hn2
    rw [h_image]
    rw [Finset.sum_image (by
      intro a _ b _ h
      simp only at h
      omega)]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    have h_coeff : β'.coeff ((γ : ℚ) + ((n + n₀ : ℤ) : ℚ)) = β'.coeff ((g : ℚ) + (n : ℚ)) := by
      congr 1
      push_cast
      rw [hg_eq]; ring
    rw [h_coeff]
    rw [show ((p : QpCUn p) ^ (-n₀)) * ((p : QpCUn p) ^ (n + n₀) *
          algebraMap (OQpCUn p) (QpCUn p) (β'.coeff ((g : ℚ) + (n : ℚ)))) =
        ((p : QpCUn p) ^ (-n₀) * (p : QpCUn p) ^ (n + n₀)) *
          algebraMap (OQpCUn p) (QpCUn p) (β'.coeff ((g : ℚ) + (n : ℚ))) from by ring]
    rw [show (p : QpCUn p) ^ (-n₀) * (p : QpCUn p) ^ (n + n₀) = (p : QpCUn p) ^ n from by
      rw [← zpow_add₀ hp_ne]
      congr 1
      omega]
  -- ============================================================
  -- intPartial β g K → f g (via translation + h_tendsto_β_γ + uniqueness)
  -- ============================================================
  have h_α_g : Filter.Tendsto (intPartial α g) Filter.atTop (nhds (f g)) := hf_spec g
  have h_α_γ : Filter.Tendsto (intPartial α γ) Filter.atTop (nhds (f γ)) := hf_spec γ
  have h_shift_atTop : Filter.Tendsto (fun K : ℤ => K + n₀) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_add_const_right _ _ Filter.tendsto_id
  have h_α_γ_shift : Filter.Tendsto (fun K : ℤ => intPartial α γ (K + n₀)) Filter.atTop
      (nhds (f γ)) := h_α_γ.comp h_shift_atTop
  have h_α_γ_mul : Filter.Tendsto
      (fun K : ℤ => (p : QpCUn p) ^ (-n₀) * intPartial α γ (K + n₀)) Filter.atTop
      (nhds ((p : QpCUn p) ^ (-n₀) * f γ)) := h_α_γ_shift.const_mul _
  have h_α_translate : Filter.Tendsto (intPartial α g) Filter.atTop
      (nhds ((p : QpCUn p) ^ (-n₀) * f γ)) := by
    apply h_α_γ_mul.congr'
    rw [Filter.EventuallyEq]
    filter_upwards with K
    exact (h_translate α K).symm
  have h_fg_eq : f g = (p : QpCUn p) ^ (-n₀) * f γ :=
    tendsto_nhds_unique h_α_g h_α_translate
  have h_β_γ_shift : Filter.Tendsto (fun K : ℤ => intPartial β γ (K + n₀)) Filter.atTop
      (nhds (f γ)) := h_tendsto_β_γ.comp h_shift_atTop
  have h_β_γ_mul : Filter.Tendsto
      (fun K : ℤ => (p : QpCUn p) ^ (-n₀) * intPartial β γ (K + n₀)) Filter.atTop
      (nhds ((p : QpCUn p) ^ (-n₀) * f γ)) := h_β_γ_shift.const_mul _
  have h_β_g : Filter.Tendsto (intPartial β g) Filter.atTop (nhds (f g)) := by
    rw [h_fg_eq]
    apply h_β_γ_mul.congr'
    rw [Filter.EventuallyEq]
    filter_upwards with K
    exact (h_translate β K).symm
  -- ============================================================
  -- intPartial (α - β) g K = intPartial α g K - intPartial β g K
  -- ============================================================
  have h_intPartial_sub : ∀ K : ℤ,
      intPartial (α - β) g K = intPartial α g K - intPartial β g K := by
    intro K
    set T_α : Finset ℤ := Set.Finite.toFinset (finiteBelowInt α g K) with hT_α_def
    set T_β : Finset ℤ := Set.Finite.toFinset (finiteBelowInt β g K) with hT_β_def
    set T_d : Finset ℤ := Set.Finite.toFinset (finiteBelowInt (α - β) g K) with hT_d_def
    set T_U : Finset ℤ := T_α ∪ T_β with hT_U_def
    have e_α : intPartial α g K =
        ∑ n ∈ T_α, (p : QpCUn p) ^ n * algebraMap (OQpCUn p) (QpCUn p) (α.coeff (g + n)) := by
      simp only [intPartial, hT_α_def]
      exact Finset.sum_attach (s := Set.Finite.toFinset (finiteBelowInt α g K))
        (f := fun n : ℤ => (p : QpCUn p) ^ n * algebraMap (OQpCUn p) (QpCUn p) (α.coeff (g + n)))
    have e_β : intPartial β g K =
        ∑ n ∈ T_β, (p : QpCUn p) ^ n * algebraMap (OQpCUn p) (QpCUn p) (β.coeff (g + n)) := by
      simp only [intPartial, hT_β_def]
      exact Finset.sum_attach (s := Set.Finite.toFinset (finiteBelowInt β g K))
        (f := fun n : ℤ => (p : QpCUn p) ^ n * algebraMap (OQpCUn p) (QpCUn p) (β.coeff (g + n)))
    have e_d : intPartial (α - β) g K =
        ∑ n ∈ T_d, (p : QpCUn p) ^ n *
          algebraMap (OQpCUn p) (QpCUn p) ((α - β).coeff (g + n)) := by
      simp only [intPartial, hT_d_def]
      exact Finset.sum_attach (s := Set.Finite.toFinset (finiteBelowInt (α - β) g K))
        (f := fun n : ℤ => (p : QpCUn p) ^ n *
          algebraMap (OQpCUn p) (QpCUn p) ((α - β).coeff (g + n)))
    have h_α_sub_U : T_α ⊆ T_U := Finset.subset_union_left
    have h_β_sub_U : T_β ⊆ T_U := Finset.subset_union_right
    have h_d_sub_U : T_d ⊆ T_U := by
      intro n hn
      have hn_mem : n ≤ K ∧ (α - β).coeff (g + n) ≠ 0 :=
        (Set.Finite.mem_toFinset (hs := finiteBelowInt (α - β) g K)).mp hn
      have h_sub_eq : (α - β).coeff (g + n) = α.coeff (g + n) - β.coeff (g + n) := rfl
      rw [h_sub_eq] at hn_mem
      by_cases h_α_z : α.coeff (g + n) = 0
      · have h_β_ne : β.coeff (g + n) ≠ 0 := by
          intro h_β_z
          apply hn_mem.2
          rw [h_α_z, h_β_z, sub_self]
        exact Finset.mem_union_right T_α
          ((Set.Finite.mem_toFinset (hs := finiteBelowInt β g K)).mpr ⟨hn_mem.1, h_β_ne⟩)
      · exact Finset.mem_union_left T_β
          ((Set.Finite.mem_toFinset (hs := finiteBelowInt α g K)).mpr ⟨hn_mem.1, h_α_z⟩)
    have he_α_U : ∑ n ∈ T_α,
          (p : QpCUn p) ^ n * algebraMap (OQpCUn p) (QpCUn p) (α.coeff (g + n)) =
        ∑ n ∈ T_U,
          (p : QpCUn p) ^ n * algebraMap (OQpCUn p) (QpCUn p) (α.coeff (g + n)) := by
      apply Finset.sum_subset h_α_sub_U
      intro n hn_U hn_not_α
      have hn_le_K : n ≤ K := by
        rcases Finset.mem_union.mp hn_U with h_α_mem | h_β_mem
        · exact ((Set.Finite.mem_toFinset (hs := finiteBelowInt α g K)).mp h_α_mem).1
        · exact ((Set.Finite.mem_toFinset (hs := finiteBelowInt β g K)).mp h_β_mem).1
      have h_α_z : α.coeff (g + n) = 0 := by
        by_contra hne
        exact hn_not_α
          ((Set.Finite.mem_toFinset (hs := finiteBelowInt α g K)).mpr ⟨hn_le_K, hne⟩)
      rw [h_α_z]
      simp
    have he_β_U : ∑ n ∈ T_β,
          (p : QpCUn p) ^ n * algebraMap (OQpCUn p) (QpCUn p) (β.coeff (g + n)) =
        ∑ n ∈ T_U,
          (p : QpCUn p) ^ n * algebraMap (OQpCUn p) (QpCUn p) (β.coeff (g + n)) := by
      apply Finset.sum_subset h_β_sub_U
      intro n hn_U hn_not_β
      have hn_le_K : n ≤ K := by
        rcases Finset.mem_union.mp hn_U with h_α_mem | h_β_mem
        · exact ((Set.Finite.mem_toFinset (hs := finiteBelowInt α g K)).mp h_α_mem).1
        · exact ((Set.Finite.mem_toFinset (hs := finiteBelowInt β g K)).mp h_β_mem).1
      have h_β_z : β.coeff (g + n) = 0 := by
        by_contra hne
        exact hn_not_β
          ((Set.Finite.mem_toFinset (hs := finiteBelowInt β g K)).mpr ⟨hn_le_K, hne⟩)
      rw [h_β_z]
      simp
    have he_d_U : ∑ n ∈ T_d,
          (p : QpCUn p) ^ n *
            algebraMap (OQpCUn p) (QpCUn p) ((α - β).coeff (g + n)) =
        ∑ n ∈ T_U,
          (p : QpCUn p) ^ n *
            algebraMap (OQpCUn p) (QpCUn p) ((α - β).coeff (g + n)) := by
      apply Finset.sum_subset h_d_sub_U
      intro n hn_U hn_not_d
      have hn_le_K : n ≤ K := by
        rcases Finset.mem_union.mp hn_U with h_α_mem | h_β_mem
        · exact ((Set.Finite.mem_toFinset (hs := finiteBelowInt α g K)).mp h_α_mem).1
        · exact ((Set.Finite.mem_toFinset (hs := finiteBelowInt β g K)).mp h_β_mem).1
      have h_d_z : (α - β).coeff (g + n) = 0 := by
        by_contra hne
        exact hn_not_d
          ((Set.Finite.mem_toFinset (hs := finiteBelowInt (α - β) g K)).mpr ⟨hn_le_K, hne⟩)
      rw [h_d_z]
      simp
    rw [e_d, he_d_U, e_α, he_α_U, e_β, he_β_U]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n _
    have h_sub_coeff : (α - β).coeff (g + n) = α.coeff (g + n) - β.coeff (g + n) := rfl
    rw [h_sub_coeff, map_sub, mul_sub]
  -- ============================================================
  -- intPartial (α - β) g K → 0
  -- ============================================================
  have h_intPartial_zero : Filter.Tendsto (fun K : ℤ => intPartial (α - β) g K) Filter.atTop
      (nhds (0 : QpCUn p)) := by
    have h_diff : Filter.Tendsto
        (fun K : ℤ => intPartial α g K - intPartial β g K) Filter.atTop
        (nhds ((f g) - (f g))) := h_α_g.sub h_β_g
    rw [sub_self] at h_diff
    apply h_diff.congr'
    rw [Filter.EventuallyEq]
    filter_upwards with K
    exact (h_intPartial_sub K).symm
  -- ============================================================
  -- Phase 1: bridge finiteBelow ⇄ intPartial
  -- ============================================================
  have h_finiteBelow_eq_finiteBelowInt :
      ∀ (x : LiftedPAdicHahnSeries p) (M : ℕ),
        (Set.Finite.toFinset (finiteBelow x g M) : Finset ℤ) =
        (Set.Finite.toFinset (finiteBelowInt x g ⌊((M : ℚ) - g)⌋) : Finset ℤ) := by
    intro x M
    ext n
    simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
    constructor
    · intro ⟨h1, h2⟩
      refine ⟨?_, h2⟩
      have hineq : (n : ℚ) ≤ (M : ℚ) - g := by linarith
      exact Int.le_floor.mpr hineq
    · intro ⟨h1, h2⟩
      refine ⟨?_, h2⟩
      have hineq : (n : ℚ) ≤ (M : ℚ) - g :=
        le_trans (by exact_mod_cast h1) (Int.floor_le ((M : ℚ) - g))
      linarith
  have h_finiteBelow_to_intPartial :
      (fun M : ℕ => ∑ n : Set.Finite.toFinset (finiteBelow (α - β) g M),
        (p : QpCUn p) ^ n.val *
          algebraMap (OQpCUn p) (QpCUn p) ((α - β).coeff (g + n))) =
      fun M : ℕ => intPartial (α - β) g ⌊((M : ℚ) - g)⌋ := by
    funext M
    simp only [intPartial]
    have h_attach_α := Finset.sum_attach
      (s := Set.Finite.toFinset (finiteBelow (α - β) g M))
      (f := fun n : ℤ => (p : QpCUn p) ^ n *
        algebraMap (OQpCUn p) (QpCUn p) ((α - β).coeff (g + n)))
    have h_attach_β := Finset.sum_attach
      (s := Set.Finite.toFinset (finiteBelowInt (α - β) g ⌊((M : ℚ) - g)⌋))
      (f := fun n : ℤ => (p : QpCUn p) ^ n *
        algebraMap (OQpCUn p) (QpCUn p) ((α - β).coeff (g + n)))
    rw [show (∑ n : Set.Finite.toFinset (finiteBelow (α - β) g M),
        (p : QpCUn p) ^ n.val *
          algebraMap (OQpCUn p) (QpCUn p) ((α - β).coeff (g + n))) =
      ∑ n ∈ Set.Finite.toFinset (finiteBelow (α - β) g M),
        (p : QpCUn p) ^ n *
          algebraMap (OQpCUn p) (QpCUn p) ((α - β).coeff (g + n)) from h_attach_α]
    rw [show (∑ n : Set.Finite.toFinset (finiteBelowInt (α - β) g ⌊((M : ℚ) - g)⌋),
        (p : QpCUn p) ^ n.1 *
          algebraMap (OQpCUn p) (QpCUn p) ((α - β).coeff (g + n))) =
      ∑ n ∈ Set.Finite.toFinset (finiteBelowInt (α - β) g ⌊((M : ℚ) - g)⌋),
        (p : QpCUn p) ^ n *
          algebraMap (OQpCUn p) (QpCUn p) ((α - β).coeff (g + n)) from h_attach_β]
    rw [h_finiteBelow_eq_finiteBelowInt (α - β) M]
  have h_φ : Filter.Tendsto (fun M : ℕ => ⌊((M : ℚ) - g)⌋) Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop_atTop.mpr
    intro b
    obtain ⟨N, hN⟩ := exists_nat_ge ((b : ℚ) + g)
    refine ⟨N, ?_⟩
    intro M hM
    rw [Int.le_floor]
    have hM' : (N : ℚ) ≤ (M : ℚ) := by exact_mod_cast hM
    linarith
  -- ============================================================
  -- Compose to get the goal
  -- ============================================================
  rw [h_finiteBelow_to_intPartial]
  exact h_intPartial_zero.comp h_φ

set_option maxHeartbeats 220000 in
-- maxHeartbeats: heavy elaboration in the multi-phase proof body
/--
**Uniqueness of the Teichmuller-style canonical expansion**.

If `s, s'` both have PWO support and `fromCoeff s ≡ fromCoeff s'` modulo
`NullSeriesIdeal p`, then `s = s'`.
-/
theorem unique_canonical_representative {p : ℕ} [Fact (Nat.Prime p)]
    {s s' : ℚ → Fpbar p}
    (hspwo : (Function.support s).IsPWO) (hspwo' : (Function.support s').IsPWO)
    (h : LiftedPAdicHahnSeries.fromCoeff s hspwo -
         LiftedPAdicHahnSeries.fromCoeff s' hspwo' ∈ NullSeriesIdeal p) :
    s = s' := by
  classical
  set α : LiftedPAdicHahnSeries p := LiftedPAdicHahnSeries.fromCoeff s hspwo with hα_def
  set α' : LiftedPAdicHahnSeries p := LiftedPAdicHahnSeries.fromCoeff s' hspwo' with hα'_def
  -- Unfold null series
  change IsNullSeries (α - α') at h
  -- p ≠ 0 in QpCUn p
  have hp_ne : (p : QpCUn p) ≠ 0 := by
    rw [show (p : QpCUn p) = algebraMap (OQpCUn p) (QpCUn p) (p : OQpCUn p) from by
      push_cast; rfl]
    exact fun h_zero => WittVector.p_nonzero p _
      ((IsFractionRing.injective (OQpCUn p) (QpCUn p))
        (by simpa using h_zero))
  -- Coefficient identities
  have hα_coeff : ∀ q : ℚ, α.coeff q = teichmuller p (s q) := fun _ => rfl
  have hα'_coeff : ∀ q : ℚ, α'.coeff q = teichmuller p (s' q) := fun _ => rfl
  have hsub_coeff : ∀ q : ℚ,
      (α - α').coeff q = teichmuller p (s q) - teichmuller p (s' q) := fun _ => rfl
  -- ============================================================
  -- funext
  -- ============================================================
  funext q
  set γ : ℚ := Int.fract q with hγ_def
  set n₀ : ℤ := ⌊q⌋ with hn₀_def
  have hq_eq : q = γ + (n₀ : ℚ) := by
    have := Int.fract_add_floor q
    linarith
  rw [hq_eq]
  set Bs : ℤ → Fpbar p := fun k => s (γ + k) with hBs_def
  set Bs' : ℤ → Fpbar p := fun k => s' (γ + k) with hBs'_def
  change s (γ + (n₀ : ℚ)) = s' (γ + (n₀ : ℚ))
  suffices h_Bs_eq : ∀ k : ℤ, Bs k = Bs' k by
    exact h_Bs_eq n₀
  -- ============================================================
  -- Get cutoffs m_s, m_s'
  -- ============================================================
  obtain ⟨m_s, hm_s⟩ : ∃ m_s : ℤ, ∀ k : ℤ, k < m_s → Bs k = 0 := by
    by_cases hsp : (Function.support s).Nonempty
    · refine ⟨⌈(hspwo.isWF.min hsp - γ : ℚ)⌉, ?_⟩
      intro k hk
      change s (γ + k) = 0
      by_contra hne
      have hmem : (γ + (k : ℚ)) ∈ Function.support s := hne
      have hmin_le : hspwo.isWF.min hsp ≤ γ + k := hspwo.isWF.min_le hsp hmem
      have hk_ineq : (hspwo.isWF.min hsp - γ : ℚ) ≤ (k : ℚ) := by linarith
      have hceil : ⌈(hspwo.isWF.min hsp - γ : ℚ)⌉ ≤ k := Int.ceil_le.mpr hk_ineq
      linarith
    · refine ⟨0, ?_⟩
      intro k _
      change s (γ + k) = 0
      have hs_zero : s = 0 := Function.support_eq_empty_iff.mp
        (Set.not_nonempty_iff_eq_empty.mp hsp)
      simp [hs_zero]
  obtain ⟨m_s', hm_s'⟩ : ∃ m_s' : ℤ, ∀ k : ℤ, k < m_s' → Bs' k = 0 := by
    by_cases hsp : (Function.support s').Nonempty
    · refine ⟨⌈(hspwo'.isWF.min hsp - γ : ℚ)⌉, ?_⟩
      intro k hk
      change s' (γ + k) = 0
      by_contra hne
      have hmem : (γ + (k : ℚ)) ∈ Function.support s' := hne
      have hmin_le : hspwo'.isWF.min hsp ≤ γ + k := hspwo'.isWF.min_le hsp hmem
      have hk_ineq : (hspwo'.isWF.min hsp - γ : ℚ) ≤ (k : ℚ) := by linarith
      have hceil : ⌈(hspwo'.isWF.min hsp - γ : ℚ)⌉ ≤ k := Int.ceil_le.mpr hk_ineq
      linarith
    · refine ⟨0, ?_⟩
      intro k _
      change s' (γ + k) = 0
      have hs'_zero : s' = 0 := Function.support_eq_empty_iff.mp
        (Set.not_nonempty_iff_eq_empty.mp hsp)
      simp [hs'_zero]
  -- ============================================================
  -- Get limits y_s, y_s', y_d
  -- ============================================================
  obtain ⟨y_s, hy_s⟩ := existsCanonicalExpansionAux.exists_lim_intPartial α γ
  obtain ⟨y_s', hy_s'⟩ := existsCanonicalExpansionAux.exists_lim_intPartial α' γ
  obtain ⟨y_d, hy_d⟩ := existsCanonicalExpansionAux.exists_lim_intPartial (α - α') γ
  -- ============================================================
  -- Helper: intPartial = Icc-form sum (for K ≥ m)
  -- ============================================================
  have h_intPartial_eq_Icc :
      ∀ (β : LiftedPAdicHahnSeries p) (t : ℚ → Fpbar p) (m : ℤ),
        (∀ q : ℚ, β.coeff q = teichmuller p (t q)) →
        (∀ k : ℤ, k < m → t (γ + k) = 0) →
        ∀ K : ℤ, m ≤ K →
        intPartial β γ K =
          ∑ k ∈ Finset.Icc m K,
            (p : QpCUn p) ^ k * algebraMap (OQpCUn p) (QpCUn p) (teichmuller p (t (γ + k))) := by
    intro β t m hβ_coeff hm K hK
    have h_step1 : intPartial β γ K =
        ∑ n ∈ Set.Finite.toFinset (finiteBelowInt β γ K),
          (p : QpCUn p) ^ n * algebraMap (OQpCUn p) (QpCUn p) (β.coeff (γ + n)) := by
      simp only [intPartial]
      exact Finset.sum_attach (s := Set.Finite.toFinset (finiteBelowInt β γ K))
        (f := fun n : ℤ => (p : QpCUn p) ^ n * algebraMap (OQpCUn p) (QpCUn p) (β.coeff (γ + n)))
    rw [h_step1]
    have h_subset : Set.Finite.toFinset (finiteBelowInt β γ K) ⊆ Finset.Icc m K := by
      intro n hn
      have hn_mem : n ≤ K ∧ β.coeff (γ + n) ≠ 0 :=
        (Set.Finite.mem_toFinset (hs := finiteBelowInt β γ K)).mp hn
      have h_t_ne : t (γ + n) ≠ 0 := by
        intro h_zero
        apply hn_mem.2
        rw [hβ_coeff (γ + n), h_zero]
        exact WittVector.teichmuller_zero p
      have h_n_ge : m ≤ n := by
        by_contra h_lt
        push Not at h_lt
        exact h_t_ne (hm n h_lt)
      exact Finset.mem_Icc.mpr ⟨h_n_ge, hn_mem.1⟩
    have h_extend : ∑ n ∈ Set.Finite.toFinset (finiteBelowInt β γ K),
          (p : QpCUn p) ^ n * algebraMap (OQpCUn p) (QpCUn p) (β.coeff (γ + n)) =
        ∑ n ∈ Finset.Icc m K,
          (p : QpCUn p) ^ n * algebraMap (OQpCUn p) (QpCUn p) (β.coeff (γ + n)) := by
      apply Finset.sum_subset h_subset
      intro n hn_Icc hn_not
      rw [Finset.mem_Icc] at hn_Icc
      have h_β_zero : β.coeff (γ + n) = 0 := by
        by_contra hne
        apply hn_not
        exact (Set.Finite.mem_toFinset (hs := finiteBelowInt β γ K)).mpr ⟨hn_Icc.2, hne⟩
      rw [h_β_zero]
      simp
    rw [h_extend]
    apply Finset.sum_congr rfl
    intro n _
    rw [hβ_coeff (γ + n)]
  -- ============================================================
  -- Tendsto in Icc form for α and α'
  -- ============================================================
  have htendsto_s :
      Filter.Tendsto
        (fun K : ℤ => ∑ k ∈ Finset.Icc m_s K,
          (p : QpCUn p) ^ k * algebraMap (OQpCUn p) (QpCUn p) (teichmuller p (Bs k)))
        Filter.atTop (nhds y_s) := by
    apply hy_s.congr'
    rw [Filter.EventuallyEq]
    filter_upwards [Filter.eventually_ge_atTop m_s] with K hK
    have := h_intPartial_eq_Icc α s m_s hα_coeff hm_s K hK
    change intPartial α γ K = _
    rw [this]
  have htendsto_s' :
      Filter.Tendsto
        (fun K : ℤ => ∑ k ∈ Finset.Icc m_s' K,
          (p : QpCUn p) ^ k * algebraMap (OQpCUn p) (QpCUn p) (teichmuller p (Bs' k)))
        Filter.atTop (nhds y_s') := by
    apply hy_s'.congr'
    rw [Filter.EventuallyEq]
    filter_upwards [Filter.eventually_ge_atTop m_s'] with K hK
    have := h_intPartial_eq_Icc α' s' m_s' hα'_coeff hm_s' K hK
    change intPartial α' γ K = _
    rw [this]
  -- ============================================================
  -- Show y_d = y_s - y_s' (via intPartial of difference)
  -- ============================================================
  have h_intPartial_sub : ∀ K : ℤ,
      intPartial (α - α') γ K = intPartial α γ K - intPartial α' γ K := by
    intro K
    -- Setup: index sets and union
    set T_α : Finset ℤ := Set.Finite.toFinset (finiteBelowInt α γ K) with hT_α_def
    set T_α' : Finset ℤ := Set.Finite.toFinset (finiteBelowInt α' γ K) with hT_α'_def
    set T_d : Finset ℤ := Set.Finite.toFinset (finiteBelowInt (α - α') γ K) with hT_d_def
    set T_U : Finset ℤ := T_α ∪ T_α' with hT_U_def
    -- Convert each intPartial to plain Finset.sum
    have e_α : intPartial α γ K =
        ∑ n ∈ T_α, (p : QpCUn p) ^ n * algebraMap (OQpCUn p) (QpCUn p) (α.coeff (γ + n)) := by
      simp only [intPartial, hT_α_def]
      exact Finset.sum_attach (s := Set.Finite.toFinset (finiteBelowInt α γ K))
        (f := fun n : ℤ => (p : QpCUn p) ^ n * algebraMap (OQpCUn p) (QpCUn p) (α.coeff (γ + n)))
    have e_α' : intPartial α' γ K =
        ∑ n ∈ T_α', (p : QpCUn p) ^ n * algebraMap (OQpCUn p) (QpCUn p) (α'.coeff (γ + n)) := by
      simp only [intPartial, hT_α'_def]
      exact Finset.sum_attach (s := Set.Finite.toFinset (finiteBelowInt α' γ K))
        (f := fun n : ℤ => (p : QpCUn p) ^ n * algebraMap (OQpCUn p) (QpCUn p) (α'.coeff (γ + n)))
    have e_d : intPartial (α - α') γ K =
        ∑ n ∈ T_d, (p : QpCUn p) ^ n *
          algebraMap (OQpCUn p) (QpCUn p) ((α - α').coeff (γ + n)) := by
      simp only [intPartial, hT_d_def]
      exact Finset.sum_attach (s := Set.Finite.toFinset (finiteBelowInt (α - α') γ K))
        (f := fun n : ℤ => (p : QpCUn p) ^ n *
          algebraMap (OQpCUn p) (QpCUn p) ((α - α').coeff (γ + n)))
    -- Subset claims
    have h_α_sub_U : T_α ⊆ T_U := Finset.subset_union_left
    have h_α'_sub_U : T_α' ⊆ T_U := Finset.subset_union_right
    have h_d_sub_U : T_d ⊆ T_U := by
      intro n hn
      have hn_mem : n ≤ K ∧ (α - α').coeff (γ + n) ≠ 0 :=
        (Set.Finite.mem_toFinset (hs := finiteBelowInt (α - α') γ K)).mp hn
      have h_sub_eq : (α - α').coeff (γ + n) = α.coeff (γ + n) - α'.coeff (γ + n) := rfl
      rw [h_sub_eq] at hn_mem
      by_cases h_α_z : α.coeff (γ + n) = 0
      · have h_α'_ne : α'.coeff (γ + n) ≠ 0 := by
          intro h_α'_z
          apply hn_mem.2
          rw [h_α_z, h_α'_z, sub_self]
        exact Finset.mem_union_right T_α
          ((Set.Finite.mem_toFinset (hs := finiteBelowInt α' γ K)).mpr ⟨hn_mem.1, h_α'_ne⟩)
      · exact Finset.mem_union_left T_α'
          ((Set.Finite.mem_toFinset (hs := finiteBelowInt α γ K)).mpr ⟨hn_mem.1, h_α_z⟩)
    -- Extend each sum to T_U
    have he_α_U : ∑ n ∈ T_α,
          (p : QpCUn p) ^ n * algebraMap (OQpCUn p) (QpCUn p) (α.coeff (γ + n)) =
        ∑ n ∈ T_U,
          (p : QpCUn p) ^ n * algebraMap (OQpCUn p) (QpCUn p) (α.coeff (γ + n)) := by
      apply Finset.sum_subset h_α_sub_U
      intro n hn_U hn_not_α
      have hn_le_K : n ≤ K := by
        rcases Finset.mem_union.mp hn_U with h_α_mem | h_α'_mem
        · exact ((Set.Finite.mem_toFinset (hs := finiteBelowInt α γ K)).mp h_α_mem).1
        · exact ((Set.Finite.mem_toFinset (hs := finiteBelowInt α' γ K)).mp h_α'_mem).1
      have h_α_z : α.coeff (γ + n) = 0 := by
        by_contra hne
        exact hn_not_α
          ((Set.Finite.mem_toFinset (hs := finiteBelowInt α γ K)).mpr ⟨hn_le_K, hne⟩)
      rw [h_α_z]
      simp
    have he_α'_U : ∑ n ∈ T_α',
          (p : QpCUn p) ^ n * algebraMap (OQpCUn p) (QpCUn p) (α'.coeff (γ + n)) =
        ∑ n ∈ T_U,
          (p : QpCUn p) ^ n * algebraMap (OQpCUn p) (QpCUn p) (α'.coeff (γ + n)) := by
      apply Finset.sum_subset h_α'_sub_U
      intro n hn_U hn_not_α'
      have hn_le_K : n ≤ K := by
        rcases Finset.mem_union.mp hn_U with h_α_mem | h_α'_mem
        · exact ((Set.Finite.mem_toFinset (hs := finiteBelowInt α γ K)).mp h_α_mem).1
        · exact ((Set.Finite.mem_toFinset (hs := finiteBelowInt α' γ K)).mp h_α'_mem).1
      have h_α'_z : α'.coeff (γ + n) = 0 := by
        by_contra hne
        exact hn_not_α'
          ((Set.Finite.mem_toFinset (hs := finiteBelowInt α' γ K)).mpr ⟨hn_le_K, hne⟩)
      rw [h_α'_z]
      simp
    have he_d_U : ∑ n ∈ T_d,
          (p : QpCUn p) ^ n *
            algebraMap (OQpCUn p) (QpCUn p) ((α - α').coeff (γ + n)) =
        ∑ n ∈ T_U,
          (p : QpCUn p) ^ n *
            algebraMap (OQpCUn p) (QpCUn p) ((α - α').coeff (γ + n)) := by
      apply Finset.sum_subset h_d_sub_U
      intro n hn_U hn_not_d
      have hn_le_K : n ≤ K := by
        rcases Finset.mem_union.mp hn_U with h_α_mem | h_α'_mem
        · exact ((Set.Finite.mem_toFinset (hs := finiteBelowInt α γ K)).mp h_α_mem).1
        · exact ((Set.Finite.mem_toFinset (hs := finiteBelowInt α' γ K)).mp h_α'_mem).1
      have h_d_z : (α - α').coeff (γ + n) = 0 := by
        by_contra hne
        exact hn_not_d
          ((Set.Finite.mem_toFinset (hs := finiteBelowInt (α - α') γ K)).mpr ⟨hn_le_K, hne⟩)
      rw [h_d_z]
      simp
    -- Combine
    rw [e_d, he_d_U, e_α, he_α_U, e_α', he_α'_U]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n _
    have h_sub_coeff : (α - α').coeff (γ + n) = α.coeff (γ + n) - α'.coeff (γ + n) := rfl
    rw [h_sub_coeff, map_sub, mul_sub]
  have h_yd_eq : y_d = y_s - y_s' := by
    have h := hy_s.sub hy_s'
    have h_congr : Filter.Tendsto
        (fun K : ℤ => intPartial α γ K - intPartial α' γ K) Filter.atTop (nhds (y_s - y_s')) := h
    have h_eq_fn : (fun K : ℤ => intPartial (α - α') γ K) =
        (fun K : ℤ => intPartial α γ K - intPartial α' γ K) := by
      funext K
      exact h_intPartial_sub K
    have hy_d' : Filter.Tendsto
        (fun K : ℤ => intPartial α γ K - intPartial α' γ K) Filter.atTop (nhds y_d) := by
      rw [← h_eq_fn]; exact hy_d
    exact tendsto_nhds_unique hy_d' h_congr
  -- ============================================================
  -- Show y_d = 0 (using IsNullSeries)
  -- ============================================================
  have h_yd_zero : y_d = 0 := by
    -- Bridge: ∑ finiteBelow x γ M = intPartial x γ ⌊M - γ⌋
    have h_finiteBelow_eq_finiteBelowInt :
        ∀ (x : LiftedPAdicHahnSeries p) (M : ℕ),
          (Set.Finite.toFinset (finiteBelow x γ M) : Finset ℤ) =
          (Set.Finite.toFinset (finiteBelowInt x γ ⌊((M : ℚ) - γ)⌋) : Finset ℤ) := by
      intro x M
      ext n
      simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
      constructor
      · intro ⟨h1, h2⟩
        refine ⟨?_, h2⟩
        have hineq : (n : ℚ) ≤ (M : ℚ) - γ := by linarith
        exact Int.le_floor.mpr hineq
      · intro ⟨h1, h2⟩
        refine ⟨?_, h2⟩
        have hineq : (n : ℚ) ≤ (M : ℚ) - γ :=
          le_trans (by exact_mod_cast h1) (Int.floor_le ((M : ℚ) - γ))
        linarith
    -- Bridge the finiteBelow sum to intPartial form
    have h_finiteBelow_to_intPartial :
        (fun M : ℕ => ∑ n : Set.Finite.toFinset (finiteBelow (α - α') γ M),
          (p : QpCUn p) ^ n.val *
            algebraMap (OQpCUn p) (QpCUn p) ((α - α').coeff (γ + n))) =
        fun M : ℕ => intPartial (α - α') γ ⌊((M : ℚ) - γ)⌋ := by
      funext M
      simp only [intPartial]
      have h_attach_α := Finset.sum_attach
        (s := Set.Finite.toFinset (finiteBelow (α - α') γ M))
        (f := fun n : ℤ => (p : QpCUn p) ^ n *
          algebraMap (OQpCUn p) (QpCUn p) ((α - α').coeff (γ + n)))
      have h_attach_β := Finset.sum_attach
        (s := Set.Finite.toFinset (finiteBelowInt (α - α') γ ⌊((M : ℚ) - γ)⌋))
        (f := fun n : ℤ => (p : QpCUn p) ^ n *
          algebraMap (OQpCUn p) (QpCUn p) ((α - α').coeff (γ + n)))
      rw [show (∑ n : Set.Finite.toFinset (finiteBelow (α - α') γ M),
          (p : QpCUn p) ^ n.val *
            algebraMap (OQpCUn p) (QpCUn p) ((α - α').coeff (γ + n))) =
        ∑ n ∈ Set.Finite.toFinset (finiteBelow (α - α') γ M),
          (p : QpCUn p) ^ n *
            algebraMap (OQpCUn p) (QpCUn p) ((α - α').coeff (γ + n)) from h_attach_α]
      rw [show (∑ n : Set.Finite.toFinset (finiteBelowInt (α - α') γ ⌊((M : ℚ) - γ)⌋),
          (p : QpCUn p) ^ n.1 *
            algebraMap (OQpCUn p) (QpCUn p) ((α - α').coeff (γ + n))) =
        ∑ n ∈ Set.Finite.toFinset (finiteBelowInt (α - α') γ ⌊((M : ℚ) - γ)⌋),
          (p : QpCUn p) ^ n *
            algebraMap (OQpCUn p) (QpCUn p) ((α - α').coeff (γ + n)) from h_attach_β]
      rw [h_finiteBelow_eq_finiteBelowInt (α - α') M]
    -- Apply hypothesis at γ
    have h_at_γ := h γ
    rw [h_finiteBelow_to_intPartial] at h_at_γ
    -- h_at_γ : Tendsto (fun M => intPartial (α - α') γ ⌊M - γ⌋) atTop (𝓝 0)
    -- Compose: φ M = ⌊(M : ℚ) - γ⌋, φ → ∞
    have h_φ : Filter.Tendsto (fun M : ℕ => ⌊((M : ℚ) - γ)⌋) Filter.atTop Filter.atTop := by
      apply Filter.tendsto_atTop_atTop.mpr
      intro b
      obtain ⟨N, hN⟩ := exists_nat_ge ((b : ℚ) + γ)
      refine ⟨N, ?_⟩
      intro M hM
      rw [Int.le_floor]
      have hM' : (N : ℚ) ≤ (M : ℚ) := by exact_mod_cast hM
      linarith
    -- y_d is the limit of intPartial (α - α') γ; composing with φ gives y_d
    have h_comp : Filter.Tendsto
        (fun M : ℕ => intPartial (α - α') γ ⌊((M : ℚ) - γ)⌋) Filter.atTop (nhds y_d) := by
      have := hy_d.comp h_φ
      exact this
    exact tendsto_nhds_unique h_comp h_at_γ
  -- y_s = y_s'
  have h_y_eq : y_s = y_s' := by
    have h1 : y_s - y_s' = 0 := by rw [← h_yd_eq, h_yd_zero]
    exact sub_eq_zero.mp h1
  -- ============================================================
  -- Apply teichmuller_digits_unique
  -- ============================================================
  rw [h_y_eq] at htendsto_s
  exact existsCanonicalExpansionAux.teichmuller_digits_unique
    Bs Bs' m_s m_s' hm_s hm_s' htendsto_s htendsto_s'

/-- **[Poonen, Proposition 4].** Every element of `𝕃_[p]` has a unique canonical representative: a
well-ordered-support coefficient function `s : ℚ → 𝔽ᵃ_[p]` whose Teichmüller lift `∑ₖ [s(k)] tᵏ`
represents it. This canonical `s` underlies the `coeff` and `support` functions on `𝕃_[p]`. -/
theorem exists_canonical_expansion {p : ℕ} [Fact (Nat.Prime p)] :
  ∀ A : (LiftedPAdicHahnSeries p) ⧸ (NullSeriesIdeal p),
    ∃! (s : {f : ℚ → Fpbar p // (Function.support f).IsPWO}),
      Ideal.Quotient.ringCon (NullSeriesIdeal p)
      A.out (LiftedPAdicHahnSeries.fromCoeff s.val s.prop) := by
  intro A
  -- Apply the existence helper to `α := A.out`.
  obtain ⟨s, hspwo, hα⟩ := exists_canonical_representative (A.out)
  refine ⟨⟨s, hspwo⟩, ?_, ?_⟩
  · -- Existence: `A.out - fromCoeff s ∈ NullSeriesIdeal` ↔ the relation holds.
    -- `Ideal.Quotient.ringCon` is the relation `a ≡ b ↔ a - b ∈ I` (for an
    -- additive group), so we just unfold it.
    -- The relation is what `Quotient.exact` gives us from `mk a = mk b`.
    have hmk :
        (Ideal.Quotient.mk (NullSeriesIdeal p)) (A.out) =
          (Ideal.Quotient.mk (NullSeriesIdeal p))
            (LiftedPAdicHahnSeries.fromCoeff s hspwo) :=
      Ideal.Quotient.eq.mpr hα
    exact Quotient.exact hmk
  · -- Uniqueness: any `⟨s', hspwo'⟩` satisfying the relation has `s = s'`.
    rintro ⟨s', hspwo'⟩ h'
    -- `h'` says `A.out - fromCoeff s' ∈ NullSeriesIdeal p` (modulo
    -- unfolding the `ringCon` relation).
    have hα' :
        A.out - LiftedPAdicHahnSeries.fromCoeff s' hspwo' ∈ NullSeriesIdeal p := by
      have hmk' :
          (Ideal.Quotient.mk (NullSeriesIdeal p)) (A.out) =
            (Ideal.Quotient.mk (NullSeriesIdeal p))
              (LiftedPAdicHahnSeries.fromCoeff s' hspwo') :=
        Quotient.sound h'
      exact Ideal.Quotient.eq.mp hmk'
    -- Subtract: `fromCoeff s - fromCoeff s'` is in the ideal.
    -- We have `(A.out - fromCoeff s') - (A.out - fromCoeff s) = fromCoeff s - fromCoeff s'`
    -- via `sub_sub_sub_cancel_left`.
    have hsub :
        LiftedPAdicHahnSeries.fromCoeff s hspwo -
          LiftedPAdicHahnSeries.fromCoeff s' hspwo' ∈ NullSeriesIdeal p := by
      have h1 := (NullSeriesIdeal p).sub_mem hα' hα
      simpa [sub_sub_sub_cancel_left] using h1
    -- Apply uniqueness helper at the function level, then lift to subtypes.
    have hfun : s = s' := unique_canonical_representative hspwo hspwo' hsub
    subst hfun
    rfl

/-- The support of a `p`-adic Hahn series (the support of its canonical coefficient function) is
partially well-ordered — the defining well-orderedness property of Hahn series. -/
theorem support_IsPWO {p : ℕ} [Fact (Nat.Prime p)]
  (x : (LiftedPAdicHahnSeries p) ⧸ (NullSeriesIdeal p)) :
  (exists_canonical_expansion x).choose.val.support.IsPWO := by
  simp only [Subtype.forall]
  convert (exists_canonical_expansion x).choose.prop
  simp

/-- A nonzero `p`-adic Hahn series has nonempty support, so its valuation (the minimum of the
support) is well-defined. -/
theorem support_nonempty_of_nonzero
    (p : ℕ) [inst : Fact (Nat.Prime p)]
    (x : (LiftedPAdicHahnSeries p) ⧸ (NullSeriesIdeal p)) (h : ¬x = 0) :
    (exists_canonical_expansion x).choose.val.support.Nonempty := by
  contrapose h
  simp only [Subtype.forall, Function.support_nonempty_iff, ne_eq, not_not] at h
  have := (exists_canonical_expansion x).choose_spec.1
  simp only [Subtype.forall, h] at this
  suffices h' : (@LiftedPAdicHahnSeries.fromCoeff p _ 0 (by simp)) = 0 by
    simp only [h'] at this
    rw [← Quotient.out_eq x]
    exact Quotient.sound this
  simpa [LiftedPAdicHahnSeries.fromCoeff] using Eq.symm Pi.zero_def

-- Helper for `val.map_one'`: the minimum of the canonical expansion's support of `1` is `0`.
-- Strategy: `s := Pi.single 0 1` is a canonical-expansion candidate for `1`; uniqueness
-- (`exists_canonical_expansion.choose_spec.2`) forces `(exists_canonical_expansion 1).choose.val`
-- to equal `s`. Hence the support is `{0}`, and `Set.IsWF.min` of `{0}` is `0`.
private lemma val_one_eq_zero (p : ℕ) [Fact (Nat.Prime p)] :
    (support_IsPWO (1 : (LiftedPAdicHahnSeries p) ⧸ (NullSeriesIdeal p))).isWF.min
      (support_nonempty_of_nonzero p 1 (one_ne_zero_quot p)) = (0 : ℚ) := by
  set A : (LiftedPAdicHahnSeries p) ⧸ (NullSeriesIdeal p) := 1 with hA_def
  have hA_ne_zero : A ≠ 0 := one_ne_zero_quot p
  set s : ℚ → Fpbar p := Pi.single (0 : ℚ) (1 : Fpbar p) with hs_def
  have h_one_ne_zero_F : (1 : Fpbar p) ≠ 0 := one_ne_zero
  have hs_supp : Function.support s = ({(0 : ℚ)} : Set ℚ) :=
    Pi.support_single_of_ne h_one_ne_zero_F
  have hs_pwo : (Function.support s).IsPWO := by
    rw [hs_supp]; exact Set.isPWO_singleton 0
  have h_from_eq :
      LiftedPAdicHahnSeries.fromCoeff s hs_pwo = (HahnSeries.single (0 : ℚ) (1 : ℤᶜᵘⁿ_[p])) := by
    apply HahnSeries.ext
    funext n
    change (teichmuller p) (s n) = (HahnSeries.single (0 : ℚ) (1 : ℤᶜᵘⁿ_[p])).coeff n
    by_cases hn : n = 0
    · subst hn
      rw [hs_def, Pi.single_eq_same, HahnSeries.coeff_single_same]
      exact map_one (teichmuller p)
    · rw [hs_def, Pi.single_eq_of_ne hn, HahnSeries.coeff_single_of_ne hn]
      exact WittVector.teichmuller_zero p
  have h_from_one : LiftedPAdicHahnSeries.fromCoeff s hs_pwo = (1 : LiftedPAdicHahnSeries p) := by
    rw [h_from_eq]; exact HahnSeries.single_zero_one
  have h_mk_eq :
      (Ideal.Quotient.mk (NullSeriesIdeal p)) A.out =
      (Ideal.Quotient.mk (NullSeriesIdeal p))
          (LiftedPAdicHahnSeries.fromCoeff s hs_pwo) := by
    have h1 : (Ideal.Quotient.mk (NullSeriesIdeal p)) A.out = A := Quotient.out_eq A
    have h2 : (Ideal.Quotient.mk (NullSeriesIdeal p))
        (LiftedPAdicHahnSeries.fromCoeff s hs_pwo) = A := by
      rw [h_from_one, (Ideal.Quotient.mk _).map_one, hA_def]
    rw [h1, h2]
  have h_rel : (Ideal.Quotient.ringCon (NullSeriesIdeal p)) A.out
      (LiftedPAdicHahnSeries.fromCoeff s hs_pwo) := Quotient.exact h_mk_eq
  have h_choose_eq : (exists_canonical_expansion A).choose = ⟨s, hs_pwo⟩ := by
    have huniq := (exists_canonical_expansion A).choose_spec.2 ⟨s, hs_pwo⟩
    exact (huniq h_rel).symm
  have h_val_eq : ((exists_canonical_expansion A).choose).val = s :=
    congrArg Subtype.val h_choose_eq
  -- Generalize over the IsWF and Nonempty proofs to avoid rewrite-motive issues.
  suffices h : ∀ (S : Set ℚ) (hwf : S.IsWF) (hne : S.Nonempty), S = ({(0 : ℚ)} : Set ℚ) →
      hwf.min hne = (0 : ℚ) by
    apply h _ _ _
    rw [h_val_eq, hs_supp]
  intro S hwf hne hS
  subst hS
  exact Set.isWF_min_singleton 0

-- A null series cannot have a unit-valued leading coefficient. The "engine" lemma
-- powering the strict-ultrametric arguments in `val.map_add_le_max'` and `val.map_mul'`.
/-- A nonzero null series cannot have a unit as its leading (lowest-support) coefficient.

If `Δ.coeff q` is a unit and `Δ` vanishes strictly below `q`, then the partial sums of
`IsNullSeries Δ` at `g := q` have valuation `ofAdd(0)` for all `M ≥ ⌈q⌉` (by the strict ultrametric
inequality the `n = 0` term dominates), yet convergence to `0` requires the valuation to eventually
drop below `ofAdd(0)` — a contradiction. -/
lemma null_series_no_unit_leading {p : ℕ} [Fact (Nat.Prime p)]
    {Δ : LiftedPAdicHahnSeries p} (hΔ : Δ ∈ NullSeriesIdeal p)
    {q : ℚ} (hq_unit : IsUnit (Δ.coeff q))
    (hq_lead : ∀ q' < q, Δ.coeff q' = 0) : False := by
  change IsNullSeries Δ at hΔ
  have htend := hΔ q
  -- Step A: p has valuation ofAdd(-1) in QpCUn p, generalised to (p)^n by valued_v_p_zpow.
  have hpn_val := valued_v_p_zpow (p := p)
  -- Step B: the n=0 term has valuation = ofAdd(0).
  have h_lead_val : Valued.v ((p : QpCUn p)^(0 : ℤ) *
      algebraMap (OQpCUn p) (QpCUn p) (Δ.coeff q)) =
      ((Multiplicative.ofAdd (0 : ℤ) : Multiplicative ℤ) : WithZero _) := by
    rw [Valuation.map_mul]
    rw [hpn_val 0]
    have hval : Valued.v (algebraMap (OQpCUn p) (QpCUn p) (Δ.coeff q)) = 1 := by
      rcases hq_unit with ⟨u, hu⟩
      rw [← hu, valued_v_algebraMap_unit_one u]
    rw [hval, mul_one]
    rfl
  -- Step D: derive contradiction. For M ≥ ⌈q⌉, the partial sum equals (n=0 term) + (sum over n ≠ 0)
  -- The n=0 term has valuation ofAdd(0); the rest has valuation ≤ ofAdd(-1) < ofAdd(0).
  -- By strict ultrametric, the partial sum's valuation = ofAdd(0). But Tendsto ... → 0
  -- forces the valuation eventually < ofAdd(0). Contradiction.
  have hq_ne : Δ.coeff q ≠ 0 := by
    intro h
    rw [h] at hq_unit
    exact (not_isUnit_zero) hq_unit
  -- Note: integers `n` in the sum index satisfy `q + n ≤ M` and `Δ.coeff (q + n) ≠ 0`.
  -- For M ≥ ⌈q⌉, `n = 0` is in the index set (since `Δ.coeff q ≠ 0`), and the n < 0 indices
  -- are excluded by `hq_lead`.
  have h_zero_in : ∀ M : ℕ, q ≤ (M : ℚ) →
      (0 : ℤ) ∈ Set.Finite.toFinset (finiteBelow Δ q M) := by
    intro M hMq
    apply (Set.Finite.mem_toFinset (hs := finiteBelow Δ q M) (a := 0)).2
    refine ⟨?_, ?_⟩
    · simpa using hMq
    · simpa using hq_ne
  -- For each M ≥ ⌈q⌉, the partial sum's valuation equals ofAdd(0).
  have h_sum_eq : ∀ M : ℕ, q ≤ (M : ℚ) →
      Valued.v (∑ n : Set.Finite.toFinset (finiteBelow Δ q M),
          (p : QpCUn p) ^ n.val * algebraMap (OQpCUn p) (QpCUn p) (Δ.coeff (q + n))) =
        ((Multiplicative.ofAdd (0 : ℤ) : Multiplicative ℤ) : WithZero _) := by
    intro M hMq
    -- Convert the indexed-attach sum into a Finset sum so we can split off the 0 index.
    rw [show (∑ n : Set.Finite.toFinset (finiteBelow Δ q M),
            (p : QpCUn p) ^ n.val * algebraMap (OQpCUn p) (QpCUn p) (Δ.coeff (q + n))) =
        ∑ n ∈ Set.Finite.toFinset (finiteBelow Δ q M),
          (p : QpCUn p) ^ n * algebraMap (OQpCUn p) (QpCUn p) (Δ.coeff (q + n)) from
        Finset.sum_attach (s := Set.Finite.toFinset (finiteBelow Δ q M))
          (f := fun n : ℤ => (p : QpCUn p) ^ n *
            algebraMap (OQpCUn p) (QpCUn p) (Δ.coeff (q + n)))]
    -- Insert n = 0.
    have h_in : (0 : ℤ) ∈ Set.Finite.toFinset (finiteBelow Δ q M) := h_zero_in M hMq
    rw [show Set.Finite.toFinset (finiteBelow Δ q M) =
        insert (0 : ℤ) ((Set.Finite.toFinset (finiteBelow Δ q M)).erase 0) from
        (Finset.insert_erase h_in).symm]
    rw [Finset.sum_insert (Finset.notMem_erase _ _)]
    -- Apply strict ultrametric: the n=0 term dominates, the rest has smaller valuation.
    rw [Valuation.map_add_eq_of_lt_left]
    · -- Goal: Valued.v (term at n=0) = ofAdd(0).
      -- The term at n=0: (p)^(0:ℤ) * algMap(Δ.coeff(q + (0:ℤ))) = (p)^0 * algMap(Δ.coeff q).
      have h_eq_zero : (q + ((0 : ℤ) : ℚ)) = q := by push_cast; ring
      rw [h_eq_zero]
      exact h_lead_val
    · -- Goal: Valued.v (rest) < Valued.v (n=0 term).
      -- Each term in the rest has valuation ≤ ofAdd(-1) < ofAdd(0) = Valued.v(n=0 term).
      have h_bound : Valued.v (∑ n ∈ (Set.Finite.toFinset (finiteBelow Δ q M)).erase 0,
            (p : QpCUn p) ^ n * algebraMap (OQpCUn p) (QpCUn p) (Δ.coeff (q + n))) ≤
          ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero _) := by
        apply Valuation.map_sum_le
        intro n hn_mem
        have hn_ne_zero : n ≠ 0 := Finset.ne_of_mem_erase hn_mem
        have hn_in_finset : n ∈ Set.Finite.toFinset (finiteBelow Δ q M) :=
          (Finset.mem_erase.mp hn_mem).2
        have hn_data : q + (n : ℚ) ≤ (M : ℚ) ∧ Δ.coeff (q + n) ≠ 0 :=
          (Set.Finite.mem_toFinset (hs := finiteBelow Δ q M) (a := n)).1 hn_in_finset
        -- Show n ≥ 1 (since n ≠ 0 and n < 0 is excluded by hq_lead).
        have hn_pos : 1 ≤ n := by
          rcases Int.lt_or_le n 0 with hlt | hle
          · -- n < 0 case: q + n < q, so Δ.coeff(q + n) = 0 by hq_lead. Contradicts hn_data.2.
            exfalso
            apply hn_data.2
            apply hq_lead
            have hncast : ((n : ℚ)) < 0 := by exact_mod_cast hlt
            linarith
          · -- n ≥ 0; combined with n ≠ 0, get n ≥ 1.
            omega
        -- Now bound: valuation of term ≤ ofAdd(-n) ≤ ofAdd(-1).
        rw [Valuation.map_mul, hpn_val n]
        have h_alg_le : Valued.v (algebraMap (OQpCUn p) (QpCUn p) (Δ.coeff (q + n))) ≤ 1 :=
          (IsDiscreteValuationRing.maximalIdeal (OQpCUn p)).valuation_le_one (Δ.coeff (q + n))
        calc ((Multiplicative.ofAdd (-n : ℤ) : Multiplicative ℤ) : WithZero _) *
                Valued.v (algebraMap (OQpCUn p) (QpCUn p) (Δ.coeff (q + n)))
            ≤ ((Multiplicative.ofAdd (-n : ℤ) : Multiplicative ℤ) : WithZero _) * 1 :=
              mul_le_mul' (le_refl _) h_alg_le
          _ = ((Multiplicative.ofAdd (-n : ℤ) : Multiplicative ℤ) : WithZero _) := mul_one _
          _ ≤ ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero _) := by
              rw [WithZero.coe_le_coe]
              exact Multiplicative.ofAdd_le.mpr (by omega)
      apply lt_of_le_of_lt h_bound
      -- Goal: ofAdd(-1) < Valued.v(n=0 term). Rewrite the n=0 term using h_lead_val.
      have h_eq_zero : (q + ((0 : ℤ) : ℚ)) = q := by push_cast; ring
      rw [h_eq_zero, h_lead_val]
      rw [WithZero.coe_lt_coe]
      exact Multiplicative.ofAdd_lt.mpr (by omega)
  -- Use Tendsto to derive a contradiction: eventually valuation < ofAdd(0), contradicting h_sum_eq.
  have h_nhds :
      {x : QpCUn p | Valued.v x <
          ((Multiplicative.ofAdd (0 : ℤ) : Multiplicative ℤ) : WithZero _)} ∈
        nhds (0 : QpCUn p) :=
    mem_nhds_zero_v_lt WithZero.coe_ne_zero
  have h_evtl_close : ∀ᶠ M : ℕ in Filter.atTop,
      Valued.v (∑ n : Set.Finite.toFinset (finiteBelow Δ q M),
          (p : QpCUn p) ^ n.val * algebraMap (OQpCUn p) (QpCUn p) (Δ.coeff (q + n))) <
        ((Multiplicative.ofAdd (0 : ℤ) : Multiplicative ℤ) : WithZero _) :=
    htend h_nhds
  have h_evtl_M_ge : ∀ᶠ M : ℕ in Filter.atTop, q ≤ (M : ℚ) := by
    have h_int : ∀ᶠ M : ℕ in Filter.atTop, ⌈q⌉₊ ≤ M := Filter.eventually_ge_atTop ⌈q⌉₊
    filter_upwards [h_int] with M hM
    have h1 : (q : ℚ) ≤ (⌈q⌉₊ : ℚ) := Nat.le_ceil q
    have h2 : ((⌈q⌉₊ : ℕ) : ℚ) ≤ ((M : ℕ) : ℚ) := by exact_mod_cast hM
    linarith
  obtain ⟨M, hMge, hMclose⟩ := (h_evtl_M_ge.and h_evtl_close).exists
  rw [h_sum_eq M hMge] at hMclose
  exact lt_irrefl _ hMclose

/-- The leading coefficient of a `fromCoeff`-built series at the minimum of its support
is a unit in `W(Fpbar p)`. -/
private lemma canonical_leading_coeff_isUnit
    {p : ℕ} [Fact (Nat.Prime p)]
    {s : ℚ → Fpbar p} (hspwo : (Function.support s).IsPWO)
    (hsne : (Function.support s).Nonempty) :
    IsUnit ((LiftedPAdicHahnSeries.fromCoeff s hspwo).coeff
      (hspwo.isWF.min hsne)) := by
  set q₀ := hspwo.isWF.min hsne with hq₀_def
  have hq₀_in : q₀ ∈ Function.support s := hspwo.isWF.min_mem hsne
  have hsq₀_ne : s q₀ ≠ 0 := hq₀_in
  change IsUnit (teichmuller p (s q₀))
  apply WittVector.isUnit_of_coeff_zero_ne_zero
  rw [WittVector.teichmuller_coeff_zero]
  exact hsq₀_ne

/-- For any nonzero element `A` of the quotient `𝕃_[p]`,
there exists an inverse `B` with `A * B = 1`. The proof uses the canonical expansion to obtain
a representative `f := fromCoeff s_A`, applies `canonical_leading_coeff_isUnit` to show
`IsUnit f.leadingCoeff`, then concludes `IsUnit f` via Mathlib's `HahnSeries.isUnit_iff`,
and finally projects the Mathlib-supplied inverse to the quotient. -/
private lemma exists_inverse_of_nonzero
    (p : ℕ) [Fact (Nat.Prime p)]
    (A : (LiftedPAdicHahnSeries p) ⧸ (NullSeriesIdeal p)) (hA : A ≠ 0) :
    ∃ B, A * B = 1 := by
  set s_A : ℚ → Fpbar p := (exists_canonical_expansion A).choose.val with hs_A_def
  have hspwo : (Function.support s_A).IsPWO := (exists_canonical_expansion A).choose.prop
  have hsne : (Function.support s_A).Nonempty := support_nonempty_of_nonzero p A hA
  set f : LiftedPAdicHahnSeries p := LiftedPAdicHahnSeries.fromCoeff s_A hspwo with hf_def
  -- f represents A in the quotient.
  have hmk_f : (Ideal.Quotient.mk (NullSeriesIdeal p)) f = A := by
    have h := (exists_canonical_expansion A).choose_spec.1
    have h_eq : (Ideal.Quotient.mk (NullSeriesIdeal p)) A.out =
        (Ideal.Quotient.mk (NullSeriesIdeal p)) f := Quotient.sound h
    exact h_eq.symm.trans (Quotient.out_eq A)
  -- f.support = Function.support s_A (via injectivity of teichmuller).
  have h_supp_eq : f.support = Function.support s_A := by
    ext n
    simp only [HahnSeries.mem_support, Function.mem_support]
    change teichmuller p (s_A n) ≠ 0 ↔ s_A n ≠ 0
    refine ⟨fun h h' => h (by rw [h', WittVector.teichmuller_zero p]), fun h h' => h ?_⟩
    exact (injective_teichmuller p) (by rw [h', WittVector.teichmuller_zero p])
  -- f ≠ 0 from the support being nonempty.
  have hf_ne : f ≠ 0 := by
    intro hf0
    have h_zero_supp : Function.support s_A = ∅ := by
      rw [← h_supp_eq, hf0]
      exact HahnSeries.support_zero
    exact (Set.not_nonempty_iff_eq_empty.mpr h_zero_supp) hsne
  -- Bridge the Mathlib leading coefficient to the support-min coefficient.
  have h_lc_eq : f.leadingCoeff = f.coeff (hspwo.isWF.min hsne) := by
    rw [HahnSeries.leadingCoeff_eq, HahnSeries.order_of_ne hf_ne]
    congr!
  -- IsUnit of the leading coefficient.
  have h_lc_unit : IsUnit f.leadingCoeff := by
    rw [h_lc_eq]
    exact canonical_leading_coeff_isUnit hspwo hsne
  -- IsUnit of f via Mathlib's HahnSeries.isUnit_iff (uses IsDomain (ℤᶜᵘⁿ_[p])).
  have hf_unit : IsUnit f := HahnSeries.isUnit_iff.mpr h_lc_unit
  -- Take the inverse in LiftedPAdicHahnSeries p.
  set u := hf_unit.unit with hu_def
  have hu_val : u.val = f := IsUnit.unit_spec hf_unit
  set g : LiftedPAdicHahnSeries p := (u⁻¹).val with hg_def
  have hfg : f * g = 1 := by
    rw [← hu_val]
    exact u.mul_inv
  -- Project to the quotient.
  refine ⟨(Ideal.Quotient.mk (NullSeriesIdeal p)) g, ?_⟩
  rw [← hmk_f, ← (Ideal.Quotient.mk _).map_mul, hfg, (Ideal.Quotient.mk _).map_one]

-- [Corollary 3, Poonen1993] : The ideal of null series is maximal, so pAdicHahnSeries p is a field.
instance (p : ℕ) [Fact (Nat.Prime p)] : (NullSeriesIdeal p).IsMaximal := by
  apply Ideal.Quotient.maximal_of_isField
  refine ⟨?_, fun a b => mul_comm a b, ?_⟩
  · -- exists_pair_ne: 1 ≠ 0 in the quotient.
    refine ⟨1, 0, ?_⟩
    intro h
    apply one_notMem_NullSeriesIdeal p
    have h1 : (Ideal.Quotient.mk (NullSeriesIdeal p)) (1 : LiftedPAdicHahnSeries p) =
        (Ideal.Quotient.mk (NullSeriesIdeal p)) (0 : LiftedPAdicHahnSeries p) := by
      simp [h]
    have := Ideal.Quotient.eq.mp h1
    simpa using this
  · -- mul_inv_cancel: every nonzero element has a right inverse.
    intros a ha
    exact exists_inverse_of_nonzero p a ha

-- The valuation of a p-adic Hahn series x is defined to be the minimum of the support of x.
open Classical in
/-- The **valuation** on `𝕃_[p]`, sending a nonzero series to the minimum of its support (and `0`
to `⊤`). This is the additive valuation making `𝕃_[p]` a valued field. -/
noncomputable def val
  (p : ℕ) [Fact (Nat.Prime p)] :
  AddValuation ((LiftedPAdicHahnSeries p) ⧸ (NullSeriesIdeal p)) (WithTop ℚ) := by
  refine AddValuation.of
    (fun x =>
      if h : x = 0 then (⊤ : WithTop ℚ)
      else ((support_IsPWO x).isWF.min (support_nonempty_of_nonzero p x h) : WithTop ℚ))
    (dif_pos rfl)
    (by rw [dif_neg (one_ne_zero_quot p), val_one_eq_zero p]; exact WithTop.coe_zero)
    ?hadd ?hmul
  case hmul =>
    -- Goal: val(x*y) = val(x) * val(y) in `Multiplicative (WithTop ℚ)ᵒᵈ`,
    -- i.e., qxy = qx + qy in additive `WithTop ℚ` (when nonzero).
    -- Cases: x = 0, y = 0 — trivial since `⊤ * a = ⊤`.
    -- Main case (x ≠ 0, y ≠ 0): show x*y ≠ 0 first via `null_series_no_unit_leading`,
    -- then show qxy = qx + qy by deriving both inequalities from the helper applied
    -- to `Δ := fromCoeff s_x * fromCoeff s_y - fromCoeff s_{xy}`.
    intro x y
    by_cases hx : x = 0
    · -- x = 0 case: val(0 * y) = val(0) = ⊤, and `⊤ + a = ⊤` in `WithTop ℚ`.
      subst hx
      rw [dif_pos (zero_mul y), dif_pos (rfl : (0 : (LiftedPAdicHahnSeries p) ⧸ _) = 0)]
      simp
    · by_cases hy : y = 0
      · subst hy
        rw [dif_pos (mul_zero x), dif_pos (rfl : (0 : (LiftedPAdicHahnSeries p) ⧸ _) = 0)]
        simp
      · -- Main case: x ≠ 0, y ≠ 0.
        -- Set canonical-expansion data.
        set s_x : ℚ → Fpbar p := (exists_canonical_expansion x).choose.val with hs_x_def
        set s_y : ℚ → Fpbar p := (exists_canonical_expansion y).choose.val with hs_y_def
        have hs_x_pwo : (Function.support s_x).IsPWO :=
            (exists_canonical_expansion x).choose.prop
        have hs_y_pwo : (Function.support s_y).IsPWO :=
            (exists_canonical_expansion y).choose.prop
        have hsx_ne : (Function.support s_x).Nonempty := support_nonempty_of_nonzero p x hx
        have hsy_ne : (Function.support s_y).Nonempty := support_nonempty_of_nonzero p y hy
        set qx : ℚ := hs_x_pwo.isWF.min hsx_ne with hqx_def
        set qy : ℚ := hs_y_pwo.isWF.min hsy_ne with hqy_def
        -- Helpers: mk(fromCoeff s_z) = z (for z = x, y).
        set fx : LiftedPAdicHahnSeries p := LiftedPAdicHahnSeries.fromCoeff s_x hs_x_pwo
            with hfx_def
        set fy : LiftedPAdicHahnSeries p := LiftedPAdicHahnSeries.fromCoeff s_y hs_y_pwo
            with hfy_def
        have hmk_fx : (Ideal.Quotient.mk (NullSeriesIdeal p)) fx = x := by
          have h := (exists_canonical_expansion x).choose_spec.1
          have h_eq : (Ideal.Quotient.mk (NullSeriesIdeal p)) x.out =
              (Ideal.Quotient.mk (NullSeriesIdeal p)) fx := Quotient.sound h
          exact h_eq.symm.trans (Quotient.out_eq x)
        have hmk_fy : (Ideal.Quotient.mk (NullSeriesIdeal p)) fy = y := by
          have h := (exists_canonical_expansion y).choose_spec.1
          have h_eq : (Ideal.Quotient.mk (NullSeriesIdeal p)) y.out =
              (Ideal.Quotient.mk (NullSeriesIdeal p)) fy := Quotient.sound h
          exact h_eq.symm.trans (Quotient.out_eq y)
        -- Coefficient of fx * fy at qx + qy: nonzero, equals teichmuller(s_x qx · s_y qy).
        have hsx_qx_ne : s_x qx ≠ 0 := hs_x_pwo.isWF.min_mem hsx_ne
        have hsy_qy_ne : s_y qy ≠ 0 := hs_y_pwo.isWF.min_mem hsy_ne
        -- The product (fx * fy).coeff (qx + qy) = teichmuller(s_x qx) * teichmuller(s_y qy).
        -- This uses HahnSeries.coeff_mul: the antidiagonal at qx + qy is precisely {(qx, qy)}.
        -- fx.support = Function.support s_x, fy.support = Function.support s_y
        -- (def-eq via teichmuller).
        have h_supp_fx : fx.support = Function.support s_x := by
          ext n
          simp only [HahnSeries.mem_support, Function.mem_support]
          change teichmuller p (s_x n) ≠ 0 ↔ s_x n ≠ 0
          refine ⟨fun h h' => h (by rw [h', WittVector.teichmuller_zero p]), fun h h' => h ?_⟩
          exact (injective_teichmuller p) (by rw [h', WittVector.teichmuller_zero p])
        have h_supp_fy : fy.support = Function.support s_y := by
          ext n
          simp only [HahnSeries.mem_support, Function.mem_support]
          change teichmuller p (s_y n) ≠ 0 ↔ s_y n ≠ 0
          refine ⟨fun h h' => h (by rw [h', WittVector.teichmuller_zero p]), fun h h' => h ?_⟩
          exact (injective_teichmuller p) (by rw [h', WittVector.teichmuller_zero p])
        have h_prod_coeff_q : (fx * fy).coeff (qx + qy) =
            teichmuller p (s_x qx) * teichmuller p (s_y qy) := by
          rw [HahnSeries.coeff_mul]
          -- Show the antidiagonal is the singleton {(qx, qy)}.
          have h_set :
              Finset.antidiagonal fx.isPWO_support fy.isPWO_support (qx + qy) = {(qx, qy)} := by
            ext ⟨i, j⟩
            simp only [Finset.mem_antidiagonal, Finset.mem_singleton, Prod.mk.injEq]
            constructor
            · rintro ⟨hi, hj, hij⟩
              -- hi : i ∈ fx.support; convert to i ∈ Function.support s_x.
              rw [h_supp_fx] at hi
              rw [h_supp_fy] at hj
              have hi_ge : qx ≤ i := hs_x_pwo.isWF.min_le hsx_ne hi
              have hj_ge : qy ≤ j := hs_y_pwo.isWF.min_le hsy_ne hj
              refine ⟨?_, ?_⟩ <;> linarith
            · rintro ⟨hi_eq, hj_eq⟩
              subst hi_eq; subst hj_eq
              refine ⟨?_, ?_, rfl⟩
              · rw [h_supp_fx]; exact hsx_qx_ne
              · rw [h_supp_fy]; exact hsy_qy_ne
          rw [h_set, Finset.sum_singleton]
          change teichmuller p (s_x qx) * teichmuller p (s_y qy) = _
          rfl
        -- For q' < qx + qy, (fx * fy).coeff q' = 0.
        -- Use support_mul_subset: (fx * fy).support ⊆ supp fx + supp fy (sumset).
        have h_prod_coeff_lt : ∀ q' < qx + qy, (fx * fy).coeff q' = 0 := by
          open Pointwise in
          intro q' hq'
          by_contra hne
          have hq'_supp : q' ∈ (fx * fy).support := (HahnSeries.mem_support _ q').mpr hne
          have h_sub : (fx * fy).support ⊆ fx.support + fy.support :=
            HahnSeries.support_mul_subset
          have hq'_in : q' ∈ fx.support + fy.support := h_sub hq'_supp
          obtain ⟨a, ha, b, hb, hab⟩ := hq'_in
          rw [h_supp_fx] at ha
          rw [h_supp_fy] at hb
          have ha_ge : qx ≤ a := hs_x_pwo.isWF.min_le hsx_ne ha
          have hb_ge : qy ≤ b := hs_y_pwo.isWF.min_le hsy_ne hb
          have : qx + qy ≤ q' := by linarith
          exact absurd this (not_le.mpr hq')
        -- Step 1: x * y ≠ 0.
        have hxy_ne : x * y ≠ 0 := by
          intro hxy_zero
          -- fx * fy ∈ NullSeriesIdeal (since mk(fx * fy) = x * y = 0).
          have hΔ : fx * fy ∈ NullSeriesIdeal p := by
            have hmk_prod : (Ideal.Quotient.mk (NullSeriesIdeal p)) (fx * fy) = 0 := by
              rw [(Ideal.Quotient.mk _).map_mul, hmk_fx, hmk_fy, hxy_zero]
            exact (Ideal.Quotient.eq_zero_iff_mem).mp hmk_prod
          have h_unit : IsUnit ((fx * fy).coeff (qx + qy)) := by
            rw [h_prod_coeff_q]
            exact ((isUnit_iff_ne_zero.mpr hsx_qx_ne).map (teichmuller p)).mul
              ((isUnit_iff_ne_zero.mpr hsy_qy_ne).map (teichmuller p))
          exact (null_series_no_unit_leading hΔ h_unit h_prod_coeff_lt).elim
        -- Step 2: prove qxy = qx + qy.
        -- Set s_xy.
        set s_xy : ℚ → Fpbar p :=
            (exists_canonical_expansion (x * y)).choose.val with hs_xy_def
        have hs_xy_pwo : (Function.support s_xy).IsPWO :=
            (exists_canonical_expansion (x * y)).choose.prop
        have hsxy_ne : (Function.support s_xy).Nonempty :=
            support_nonempty_of_nonzero p (x * y) hxy_ne
        set qxy : ℚ := hs_xy_pwo.isWF.min hsxy_ne with hqxy_def
        set fxy : LiftedPAdicHahnSeries p := LiftedPAdicHahnSeries.fromCoeff s_xy hs_xy_pwo
            with hfxy_def
        have hmk_fxy : (Ideal.Quotient.mk (NullSeriesIdeal p)) fxy = x * y := by
          have h := (exists_canonical_expansion (x * y)).choose_spec.1
          have h_eq : (Ideal.Quotient.mk (NullSeriesIdeal p)) (x * y).out =
              (Ideal.Quotient.mk (NullSeriesIdeal p)) fxy := Quotient.sound h
          exact h_eq.symm.trans (Quotient.out_eq (x * y))
        -- Δ := fx * fy - fxy is in NullSeriesIdeal (since both reduce to x*y).
        have hΔ_mem : fx * fy - fxy ∈ NullSeriesIdeal p := by
          have hmk_eq : (Ideal.Quotient.mk (NullSeriesIdeal p)) (fx * fy) =
              (Ideal.Quotient.mk (NullSeriesIdeal p)) fxy := by
            rw [(Ideal.Quotient.mk _).map_mul, hmk_fx, hmk_fy, hmk_fxy]
          exact Ideal.Quotient.eq.mp hmk_eq
        -- Show qxy = qx + qy via two inequalities.
        -- ≥ direction: qxy ≥ qx + qy (i.e., qxy not strictly below qx + qy).
        have h_ge : qx + qy ≤ qxy := by
          by_contra h_not
          push Not at h_not  -- h_not : qxy < qx + qy
          -- At q := qxy < qx + qy, (fx * fy).coeff qxy = 0 by h_prod_coeff_lt.
          -- And fxy.coeff qxy = teichmuller(s_xy qxy), a unit.
          -- So (fx * fy - fxy).coeff qxy = 0 - teichmuller(...) = -teichmuller(...), a unit.
          -- For q' < qxy: similar (both 0).
          have hsxy_qxy_ne : s_xy qxy ≠ 0 := hs_xy_pwo.isWF.min_mem hsxy_ne
          have h_Δ_coeff_qxy : (fx * fy - fxy).coeff qxy = -teichmuller p (s_xy qxy) := by
            rw [HahnSeries.coeff_sub']
            change (fx * fy).coeff qxy - fxy.coeff qxy = _
            rw [h_prod_coeff_lt qxy h_not]
            change 0 - teichmuller p (s_xy qxy) = _
            ring
          have h_Δ_unit : IsUnit ((fx * fy - fxy).coeff qxy) := by
            rw [h_Δ_coeff_qxy]
            exact ((isUnit_iff_ne_zero.mpr hsxy_qxy_ne).map (teichmuller p)).neg
          have h_Δ_lead : ∀ q' < qxy, (fx * fy - fxy).coeff q' = 0 := by
            intro q' hq'
            have hq'_lt : q' < qx + qy := lt_trans hq' h_not
            have h_prod_q' : (fx * fy).coeff q' = 0 := h_prod_coeff_lt q' hq'_lt
            have h_fxy_q' : fxy.coeff q' = 0 := by
              change teichmuller p (s_xy q') = 0
              have : s_xy q' = 0 := by
                by_contra hne
                have hmem : q' ∈ Function.support s_xy := hne
                have h_le : qxy ≤ q' := hs_xy_pwo.isWF.min_le hsxy_ne hmem
                exact absurd h_le (not_le.mpr hq')
              rw [this, WittVector.teichmuller_zero p]
            change (fx * fy - fxy).coeff q' = 0
            rw [HahnSeries.coeff_sub']
            change (fx * fy).coeff q' - fxy.coeff q' = 0
            rw [h_prod_q', h_fxy_q']
            ring
          exact (null_series_no_unit_leading hΔ_mem h_Δ_unit h_Δ_lead).elim
        -- ≤ direction: qxy ≤ qx + qy (i.e., qxy not strictly above qx + qy).
        have h_le : qxy ≤ qx + qy := by
          by_contra h_not
          push Not at h_not  -- h_not : qx + qy < qxy
          -- At q := qx + qy, (fx * fy).coeff = teichmuller(s_x qx · s_y qy), a unit.
          -- And fxy.coeff (qx + qy) = teichmuller(s_xy (qx + qy)) = 0 (since qx + qy < qxy).
          -- For q' < qx + qy: (fx * fy).coeff q' = 0 by h_prod_coeff_lt; fxy.coeff q' = 0 too.
          have hsxy_zero_q : s_xy (qx + qy) = 0 := by
            by_contra hne
            have hmem : (qx + qy) ∈ Function.support s_xy := hne
            have h_le : qxy ≤ qx + qy := hs_xy_pwo.isWF.min_le hsxy_ne hmem
            exact absurd h_le (not_le.mpr h_not)
          have h_Δ_coeff_q : (fx * fy - fxy).coeff (qx + qy) =
              teichmuller p (s_x qx) * teichmuller p (s_y qy) := by
            rw [HahnSeries.coeff_sub']
            change (fx * fy).coeff (qx + qy) - fxy.coeff (qx + qy) = _
            rw [h_prod_coeff_q]
            change teichmuller p (s_x qx) * teichmuller p (s_y qy) -
                fxy.coeff (qx + qy) = _
            change teichmuller p (s_x qx) * teichmuller p (s_y qy) -
                teichmuller p (s_xy (qx + qy)) = _
            rw [hsxy_zero_q, WittVector.teichmuller_zero p]
            ring
          have h_Δ_unit : IsUnit ((fx * fy - fxy).coeff (qx + qy)) := by
            rw [h_Δ_coeff_q]
            exact ((isUnit_iff_ne_zero.mpr hsx_qx_ne).map (teichmuller p)).mul
              ((isUnit_iff_ne_zero.mpr hsy_qy_ne).map (teichmuller p))
          have h_Δ_lead : ∀ q' < qx + qy, (fx * fy - fxy).coeff q' = 0 := by
            intro q' hq'
            have hq'_lt_qxy : q' < qxy := lt_trans hq' h_not
            have h_prod_q' : (fx * fy).coeff q' = 0 := h_prod_coeff_lt q' hq'
            have h_fxy_q' : fxy.coeff q' = 0 := by
              change teichmuller p (s_xy q') = 0
              have : s_xy q' = 0 := by
                by_contra hne
                have hmem : q' ∈ Function.support s_xy := hne
                have h_le : qxy ≤ q' := hs_xy_pwo.isWF.min_le hsxy_ne hmem
                exact absurd h_le (not_le.mpr hq'_lt_qxy)
              rw [this, WittVector.teichmuller_zero p]
            change (fx * fy - fxy).coeff q' = 0
            rw [HahnSeries.coeff_sub']
            change (fx * fy).coeff q' - fxy.coeff q' = 0
            rw [h_prod_q', h_fxy_q']
            ring
          exact (null_series_no_unit_leading hΔ_mem h_Δ_unit h_Δ_lead).elim
        have h_eq : qxy = qx + qy := le_antisymm h_le h_ge
        -- Now translate to the goal.
        rw [dif_neg hxy_ne, dif_neg hx, dif_neg hy]
        -- Goal: ↑qxy = ↑qx + ↑qy in `WithTop ℚ`.
        change ((qxy : ℚ) : WithTop ℚ) = ((qx : ℚ) : WithTop ℚ) + ((qy : ℚ) : WithTop ℚ)
        rw [h_eq]
        exact_mod_cast rfl
  case hadd =>
    -- Goal in `Multiplicative (WithTop ℚ)ᵒᵈ`:
    --   val(x+y) ≤ max(val x, val y)
    -- Equivalent in additive `WithTop ℚ` to the standard ultrametric:
    --   val(x+y) ≥ min(val x, val y).
    -- Trivial cases: x+y = 0, x = 0, y = 0 — handled below.
    -- Main case (x, y, x+y all nonzero): reduces to showing
    --   `min(supp s_{x+y}) ≥ min(min(supp s_x), min(supp s_y))`.
    -- The main step is the support comparison stated below.
    intro x y
    -- Case x + y = 0: RHS is ⊤, so the ultrametric bound is trivial.
    by_cases hxy : x + y = 0
    · rw [dif_pos hxy]
      exact le_top
    -- Case x = 0: x + y = y, both reduce to val y; trivial.
    · by_cases hx : x = 0
      · subst hx
        rw [zero_add, dif_pos (rfl : (0 : (LiftedPAdicHahnSeries p) ⧸ (NullSeriesIdeal p)) = 0)]
        exact min_le_right _ _
      -- Case y = 0: similar; symmetric.
      · by_cases hy : y = 0
        · subst hy
          rw [add_zero, dif_pos (rfl : (0 : (LiftedPAdicHahnSeries p) ⧸ (NullSeriesIdeal p)) = 0)]
          exact min_le_left _ _
        -- Main case: all of x, y, x+y are nonzero.
        -- Reduces to showing `min(supp s_{x+y}) ≥ min(min(supp s_x), min(supp s_y))` in ℚ
        -- (then translate to the dual ordering in `Multiplicative (WithTop ℚ)ᵒᵈ`).
        --
        -- Strategy: use that
        --   `Δ := fromCoeff s_x + fromCoeff s_y - fromCoeff s_{x+y}`
        -- is a null series (since all three differ from x.out, y.out, (x+y).out by null series,
        -- plus (x+y).out - x.out - y.out is also a null series, since both reduce to `x+y` in the
        -- quotient).
        -- Suppose for contradiction val(x+y) < min(val x, val y). Set q := min(supp s_{x+y}).
        -- Then s_x.q = 0, s_y.q = 0, so Δ.coeff q = -teichmuller p (s_{x+y}.q).
        -- s_{x+y}.q is the value at the min of supp s_{x+y}, hence nonzero, so teichmuller of it
        -- is a unit in `OQpCUn p`, and so is its negation.
        -- For q' < q, all three coefficients vanish, so Δ.coeff q' = 0.
        -- Apply `null_series_no_unit_leading` → contradiction.
        rw [dif_neg hxy, dif_neg hx, dif_neg hy]
        -- Set canonical-expansion data.
        set s_x : ℚ → Fpbar p := (exists_canonical_expansion x).choose.val with hs_x_def
        set s_y : ℚ → Fpbar p := (exists_canonical_expansion y).choose.val with hs_y_def
        set s_xy : ℚ → Fpbar p :=
            (exists_canonical_expansion (x + y)).choose.val with hs_xy_def
        have hs_x_pwo : (Function.support s_x).IsPWO :=
            (exists_canonical_expansion x).choose.prop
        have hs_y_pwo : (Function.support s_y).IsPWO :=
            (exists_canonical_expansion y).choose.prop
        have hs_xy_pwo : (Function.support s_xy).IsPWO :=
            (exists_canonical_expansion (x + y)).choose.prop
        -- min values in ℚ.
        have hsx_ne : (Function.support s_x).Nonempty := support_nonempty_of_nonzero p x hx
        have hsy_ne : (Function.support s_y).Nonempty := support_nonempty_of_nonzero p y hy
        have hsxy_ne : (Function.support s_xy).Nonempty :=
            support_nonempty_of_nonzero p (x + y) hxy
        set qx : ℚ := hs_x_pwo.isWF.min hsx_ne with hqx_def
        set qy : ℚ := hs_y_pwo.isWF.min hsy_ne with hqy_def
        set qxy : ℚ := hs_xy_pwo.isWF.min hsxy_ne with hqxy_def
        -- Show goal in additive ℚ form: min(qx, qy) ≤ qxy.
        suffices h : min qx qy ≤ qxy by
          -- Translate the ℚ-level inequality to `WithTop ℚ`.
          change min ((qx : ℚ) : WithTop ℚ) ((qy : ℚ) : WithTop ℚ) ≤ ((qxy : ℚ) : WithTop ℚ)
          exact_mod_cast h
        -- Now prove min qx qy ≤ qxy by contradiction.
        by_contra hlt
        push Not at hlt
        -- hlt : qxy < min qx qy.
        have hqxy_lt_qx : qxy < qx := lt_of_lt_of_le hlt (min_le_left _ _)
        have hqxy_lt_qy : qxy < qy := lt_of_lt_of_le hlt (min_le_right _ _)
        have hsx_qxy : s_x qxy = 0 := by
          by_contra hne
          have hmem : qxy ∈ Function.support s_x := hne
          have h_le : qx ≤ qxy := hs_x_pwo.isWF.min_le hsx_ne hmem
          exact absurd h_le (not_le.mpr hqxy_lt_qx)
        have hsy_qxy : s_y qxy = 0 := by
          by_contra hne
          have hmem : qxy ∈ Function.support s_y := hne
          have h_le : qy ≤ qxy := hs_y_pwo.isWF.min_le hsy_ne hmem
          exact absurd h_le (not_le.mpr hqxy_lt_qy)
        -- s_xy qxy ≠ 0 (qxy is in supp s_xy, in fact at the min).
        have hsxy_qxy_ne : s_xy qxy ≠ 0 := hs_xy_pwo.isWF.min_mem hsxy_ne
        -- Build Δ := fromCoeff s_x + fromCoeff s_y - fromCoeff s_xy.
        set fx : LiftedPAdicHahnSeries p := LiftedPAdicHahnSeries.fromCoeff s_x hs_x_pwo
            with hfx_def
        set fy : LiftedPAdicHahnSeries p := LiftedPAdicHahnSeries.fromCoeff s_y hs_y_pwo
            with hfy_def
        set fxy : LiftedPAdicHahnSeries p := LiftedPAdicHahnSeries.fromCoeff s_xy hs_xy_pwo
            with hfxy_def
        set Δ : LiftedPAdicHahnSeries p := fx + fy - fxy with hΔ_def
        -- Show Δ ∈ NullSeriesIdeal p via decomposition into four null elements.
        have hx_null : x.out - fx ∈ NullSeriesIdeal p := by
          have h := (exists_canonical_expansion x).choose_spec.1
          have hmk : (Ideal.Quotient.mk (NullSeriesIdeal p)) x.out =
              (Ideal.Quotient.mk (NullSeriesIdeal p)) fx := Quotient.sound h
          exact Ideal.Quotient.eq.mp hmk
        have hy_null : y.out - fy ∈ NullSeriesIdeal p := by
          have h := (exists_canonical_expansion y).choose_spec.1
          have hmk : (Ideal.Quotient.mk (NullSeriesIdeal p)) y.out =
              (Ideal.Quotient.mk (NullSeriesIdeal p)) fy := Quotient.sound h
          exact Ideal.Quotient.eq.mp hmk
        have hxy_null : (x + y).out - fxy ∈ NullSeriesIdeal p := by
          have h := (exists_canonical_expansion (x + y)).choose_spec.1
          have hmk : (Ideal.Quotient.mk (NullSeriesIdeal p)) (x + y).out =
              (Ideal.Quotient.mk (NullSeriesIdeal p)) fxy := Quotient.sound h
          exact Ideal.Quotient.eq.mp hmk
        have hout_null : x.out + y.out - (x + y).out ∈ NullSeriesIdeal p := by
          have h_x_out : (Ideal.Quotient.mk (NullSeriesIdeal p)) x.out = x := Quotient.out_eq x
          have h_y_out : (Ideal.Quotient.mk (NullSeriesIdeal p)) y.out = y := Quotient.out_eq y
          have h_xy_out : (Ideal.Quotient.mk (NullSeriesIdeal p)) (x + y).out = x + y :=
            Quotient.out_eq (x + y)
          have h_mk_xy : (Ideal.Quotient.mk (NullSeriesIdeal p)) (x.out + y.out) =
              (Ideal.Quotient.mk (NullSeriesIdeal p)) (x + y).out := by
            rw [(Ideal.Quotient.mk _).map_add, h_x_out, h_y_out, h_xy_out]
          exact Ideal.Quotient.eq.mp h_mk_xy
        have hΔ : Δ ∈ NullSeriesIdeal p := by
          have hring : fx + fy - fxy =
              -(x.out - fx) + (-(y.out - fy)) + ((x + y).out - fxy) +
                (x.out + y.out - (x + y).out) := by ring
          rw [hΔ_def, hring]
          apply (NullSeriesIdeal p).add_mem
          · apply (NullSeriesIdeal p).add_mem
            · apply (NullSeriesIdeal p).add_mem
              · exact (NullSeriesIdeal p).neg_mem hx_null
              · exact (NullSeriesIdeal p).neg_mem hy_null
            · exact hxy_null
          · exact hout_null
        -- Compute Δ.coeff at qxy.
        have hΔ_coeff_qxy : Δ.coeff qxy = -teichmuller p (s_xy qxy) := by
          change (fx + fy - fxy).coeff qxy = _
          rw [HahnSeries.coeff_sub']
          change (fx + fy).coeff qxy - fxy.coeff qxy = _
          rw [HahnSeries.coeff_add']
          change fx.coeff qxy + fy.coeff qxy - fxy.coeff qxy = _
          change teichmuller p (s_x qxy) + teichmuller p (s_y qxy) -
                teichmuller p (s_xy qxy) = _
          rw [hsx_qxy, hsy_qxy]
          rw [WittVector.teichmuller_zero p]
          ring
        -- Δ.coeff qxy is a unit (negation of a unit).
        have h_teich_unit : IsUnit (teichmuller p (s_xy qxy)) :=
          (isUnit_iff_ne_zero.mpr hsxy_qxy_ne).map (teichmuller p)
        have hΔ_coeff_qxy_unit : IsUnit (Δ.coeff qxy) := by
          rw [hΔ_coeff_qxy]
          exact h_teich_unit.neg
        -- For q' < qxy, Δ.coeff q' = 0 (all three sₐ coefficients vanish).
        have hΔ_lead : ∀ q' < qxy, Δ.coeff q' = 0 := by
          intro q' hq'
          have hq'_lt_qx : q' < qx := lt_trans hq' hqxy_lt_qx
          have hq'_lt_qy : q' < qy := lt_trans hq' hqxy_lt_qy
          have hq'_lt_qxy : q' < qxy := hq'
          have hsx_q' : s_x q' = 0 := by
            by_contra hne
            have hmem : q' ∈ Function.support s_x := hne
            have h_le : qx ≤ q' := hs_x_pwo.isWF.min_le hsx_ne hmem
            exact absurd h_le (not_le.mpr hq'_lt_qx)
          have hsy_q' : s_y q' = 0 := by
            by_contra hne
            have hmem : q' ∈ Function.support s_y := hne
            have h_le : qy ≤ q' := hs_y_pwo.isWF.min_le hsy_ne hmem
            exact absurd h_le (not_le.mpr hq'_lt_qy)
          have hsxy_q' : s_xy q' = 0 := by
            by_contra hne
            have hmem : q' ∈ Function.support s_xy := hne
            have h_le : qxy ≤ q' := hs_xy_pwo.isWF.min_le hsxy_ne hmem
            exact absurd h_le (not_le.mpr hq'_lt_qxy)
          change (fx + fy - fxy).coeff q' = 0
          rw [HahnSeries.coeff_sub']
          change (fx + fy).coeff q' - fxy.coeff q' = 0
          rw [HahnSeries.coeff_add']
          change fx.coeff q' + fy.coeff q' - fxy.coeff q' = 0
          change teichmuller p (s_x q') + teichmuller p (s_y q') -
                teichmuller p (s_xy q') = 0
          rw [hsx_q', hsy_q', hsxy_q']
          rw [WittVector.teichmuller_zero p]
          ring
        -- Apply the helper to derive False.
        exact (null_series_no_unit_leading hΔ hΔ_coeff_qxy_unit hΔ_lead).elim

/-- The field `𝕃_[p]` of **`p`-adic Hahn series**: the quotient of `W(𝔽ᵃ_[p])((t^ℚ))` by the
null-series ideal.

Implementation note: in mathlib v4.31 `WithVal v` became a structure (previously a transparent type
synonym), so it is no longer defeq to the underlying ring. We therefore define `𝕃_[p]` as the bare
quotient (matching the earlier behaviour of `WithVal (val p)`) and install the valuation topology by
hand below. -/
abbrev pAdicHahnSeries (p : ℕ) [Fact (Nat.Prime p)] : Type _ :=
  (LiftedPAdicHahnSeries p) ⧸ (NullSeriesIdeal p)

@[inherit_doc] notation "𝕃_[" p "]" => pAdicHahnSeries p

namespace pAdicHahnSeries
/-- The **coefficient function** of a `p`-adic Hahn series `x`: writing `x = ∑ₖ [aₖ] pᵏ` in its
canonical expansion (with `aₖ ∈ 𝔽ᵃ_[p]`), this is the function `k ↦ aₖ`. -/
noncomputable def coeff {p : ℕ} [Fact (Nat.Prime p)] (x : 𝕃_[p]) :
  ℚ → Fpbar p := (exists_canonical_expansion x).choose.val

/-- The **support** of a `p`-adic Hahn series `x`: the support of its coefficient function. -/
noncomputable def support {p : ℕ} [Fact (Nat.Prime p)] (x : 𝕃_[p]) : Set ℚ :=
  (exists_canonical_expansion x).choose.val.support

instance wellFoundedLT_support {p : ℕ} [Fact (Nat.Prime p)] (f : 𝕃_[p]) :
  WellFoundedLT f.support := by
  have hs : f.support.IsWF := by
    simpa [pAdicHahnSeries.support] using (TrustworthyKedlaya.support_IsPWO (p := p) f).isWF
  refine ⟨?_⟩
  have hsub : WellFounded (Function.onFun (fun x y : ℚ => x < y) (Subtype.val : f.support → ℚ)) :=
    (Set.wellFoundedOn_range (f := (Subtype.val : f.support → ℚ)) (r := (· < ·))).mp
      (by simpa [Set.IsWF] using hs)
  change WellFounded (fun x y : f.support => x.1 < y.1)
  exact hsub

noncomputable instance (p : ℕ) [Fact (Nat.Prime p)] : Field (𝕃_[p]) := by
  apply Ideal.Quotient.field

noncomputable instance (p : ℕ) [Fact (Nat.Prime p)] :
  Valued (𝕃_[p]) (Multiplicative (WithTop ℚ)ᵒᵈ) :=
  Valued.mk' (val p)

/-- Helper: in `WittVector p (Fpbar p) = ℤᶜᵘⁿ_[p]`, the Teichmüller lifts of two distinct
elements differ by a unit. The argument uses the residue-field map (the `0`-th coefficient
in characteristic `p`) and `WittVector.isUnit_of_coeff_zero_ne_zero`. -/
lemma teich_sub_isUnit {p : ℕ} [Fact (Nat.Prime p)]
    {a b : Fpbar p} (h : a ≠ b) :
    IsUnit (teichmuller p a - teichmuller p b) := by
  apply WittVector.isUnit_of_coeff_zero_ne_zero
  intro h0
  have h_imp : ∀ i < 1, ((teichmuller p) a - (teichmuller p) b).coeff i = 0 := by
    intro i hi; interval_cases i; exact h0
  have h_eq : ((teichmuller p) a).coeff 0 = ((teichmuller p) b).coeff 0 :=
    (WittVector.le_coeff_eq_iff_le_sub_coeff_eq_zero (n := 1)).mpr h_imp 0 (by omega)
  rw [WittVector.teichmuller_coeff_zero, WittVector.teichmuller_coeff_zero] at h_eq
  exact h h_eq

set_option synthInstance.maxHeartbeats 220000 in
-- Heartbeat ceilings raised: the proof contains many `set` bindings over the canonical-expansion
-- choose_spec apparatus and exercises typeclass synthesis through the WithVal alias when calling
-- `Quotient.sound` on the choose_spec relation; the default budgets fall short.
/-- The canonical-section map `x ↦ LPHS.fromCoeff x.coeff (support_IsPWO x)` is an
isometry from the val-topology on 𝕃_[p] to the orderTop-topology on LPHS p:
`HahnSeries.orderTop (canonical(x) - canonical(y)) = val(x - y)` for all `x, y ∈ 𝕃_[p]`.

This is the strategic linchpin for the LaurentSeries-style proof of `CompleteSpace 𝕃_[p]`:
a Cauchy filter in 𝕃_[p] lifts to a Cauchy filter in LPHS via this section. The proof uses
`null_series_no_unit_leading` twice: once to show that `Δ := f_x - f_y - f_z` (a null series)
cannot have its leading coefficient strictly below `q_z := val(x - y)` (via `teich_sub_isUnit`
applied to differing s_x, s_y values at q_Δ), and once to show that `(f_x - f_y).coeff q_z ≠ 0`
(else `Δ.coeff q_z = -teich(s_z q_z)` is a unit, contradicting `null_series_no_unit_leading`). -/
private lemma canonical_isometry (p : ℕ) [Fact (Nat.Prime p)] (x y : 𝕃_[p]) :
    HahnSeries.orderTop
      (LiftedPAdicHahnSeries.fromCoeff (coeff x) (support_IsPWO x) -
       LiftedPAdicHahnSeries.fromCoeff (coeff y) (support_IsPWO y)) =
    (val p) (x - y) := by
  -- Setup canonical reps in LPHS.
  set s_x : ℚ → Fpbar p := coeff x with hs_x_def
  set s_y : ℚ → Fpbar p := coeff y with hs_y_def
  set s_z : ℚ → Fpbar p := coeff (x - y) with hs_z_def
  have hs_x_pwo : (Function.support s_x).IsPWO := support_IsPWO x
  have hs_y_pwo : (Function.support s_y).IsPWO := support_IsPWO y
  have hs_z_pwo : (Function.support s_z).IsPWO := support_IsPWO (x - y)
  set f_x : LiftedPAdicHahnSeries p := LiftedPAdicHahnSeries.fromCoeff s_x hs_x_pwo
    with hf_x_def
  set f_y : LiftedPAdicHahnSeries p := LiftedPAdicHahnSeries.fromCoeff s_y hs_y_pwo
    with hf_y_def
  set f_z : LiftedPAdicHahnSeries p := LiftedPAdicHahnSeries.fromCoeff s_z hs_z_pwo
    with hf_z_def
  -- f_x, f_y, f_z represent x, y, x - y in the quotient.
  have hf_x_repr : (Ideal.Quotient.mk (NullSeriesIdeal p)) f_x = x := by
    have h := (exists_canonical_expansion x).choose_spec.1
    have h_eq : (Ideal.Quotient.mk (NullSeriesIdeal p)) x.out =
        (Ideal.Quotient.mk (NullSeriesIdeal p)) f_x := Quotient.sound h
    exact h_eq.symm.trans (Quotient.out_eq x)
  have hf_y_repr : (Ideal.Quotient.mk (NullSeriesIdeal p)) f_y = y := by
    have h := (exists_canonical_expansion y).choose_spec.1
    have h_eq : (Ideal.Quotient.mk (NullSeriesIdeal p)) y.out =
        (Ideal.Quotient.mk (NullSeriesIdeal p)) f_y := Quotient.sound h
    exact h_eq.symm.trans (Quotient.out_eq y)
  have hf_z_repr : (Ideal.Quotient.mk (NullSeriesIdeal p)) f_z = x - y := by
    have h := (exists_canonical_expansion (x - y)).choose_spec.1
    have h_eq : (Ideal.Quotient.mk (NullSeriesIdeal p)) (x - y).out =
        (Ideal.Quotient.mk (NullSeriesIdeal p)) f_z := Quotient.sound h
    exact h_eq.symm.trans (Quotient.out_eq (x - y))
  -- Δ := f_x - f_y - f_z is a null series.
  set Δ : LiftedPAdicHahnSeries p := f_x - f_y - f_z with hΔ_def
  have hΔ_mem : Δ ∈ NullSeriesIdeal p := by
    have h_mk_zero : (Ideal.Quotient.mk (NullSeriesIdeal p)) Δ = 0 := by
      rw [hΔ_def]
      simp only [map_sub, hf_x_repr, hf_y_repr, hf_z_repr]
      ring
    exact (Ideal.Quotient.eq_zero_iff_mem).mp h_mk_zero
  -- Coefficient-level computations (def-eq via LPHS.fromCoeff).
  have hcoeff_fx : ∀ q, f_x.coeff q = teichmuller p (s_x q) := fun q => rfl
  have hcoeff_fy : ∀ q, f_y.coeff q = teichmuller p (s_y q) := fun q => rfl
  have hcoeff_fz : ∀ q, f_z.coeff q = teichmuller p (s_z q) := fun q => rfl
  have hcoeff_Δ : ∀ q, Δ.coeff q =
      teichmuller p (s_x q) - teichmuller p (s_y q) - teichmuller p (s_z q) := by
    intro q
    change (f_x - f_y - f_z).coeff q = _
    simp only [HahnSeries.coeff_sub, hcoeff_fx, hcoeff_fy, hcoeff_fz]
  -- Case split: x = y (trivial) vs x ≠ y (main case).
  by_cases hxy : x = y
  · -- Case x = y. Then s_x = s_y, hence f_x = f_y; LHS = orderTop 0 = ⊤. RHS = val 0 = ⊤.
    have h_s_eq : s_x = s_y := by simp [hs_x_def, hs_y_def, hxy]
    have h_f_eq : f_x = f_y := by
      apply HahnSeries.ext
      ext q
      rw [hcoeff_fx, hcoeff_fy, h_s_eq]
    rw [h_f_eq, sub_self]
    rw [HahnSeries.orderTop_zero, hxy, sub_self]
    rw [(val p).map_zero]
  · -- Case x ≠ y, so x - y ≠ 0, and val(x - y) = ↑q_z.
    have hxy_ne : x - y ≠ 0 := sub_ne_zero.mpr hxy
    have hsz_ne : (Function.support s_z).Nonempty :=
      support_nonempty_of_nonzero p (x - y) hxy_ne
    set q_z : ℚ := hs_z_pwo.isWF.min hsz_ne with hq_z_def
    have hsz_qz_ne : s_z q_z ≠ 0 := hs_z_pwo.isWF.min_mem hsz_ne
    have hsz_below : ∀ q' < q_z, s_z q' = 0 := by
      intro q' hq'
      by_contra hne
      have hmem : q' ∈ Function.support s_z := hne
      exact absurd (hs_z_pwo.isWF.min_le hsz_ne hmem) (not_le.mpr hq')
    -- val(x - y) = ↑q_z.
    have hval_xy : (val p) (x - y) = ((q_z : ℚ) : WithTop ℚ) := by
      classical
      change (if h : (x - y) = 0 then (⊤ : WithTop ℚ)
           else ((support_IsPWO (x - y)).isWF.min
              (support_nonempty_of_nonzero p (x - y) h) : WithTop ℚ))
        = ((q_z : ℚ) : WithTop ℚ)
      rw [dif_neg hxy_ne]
      rw [hq_z_def]
      congr 1
    rw [hval_xy]
    -- Direction 1: For q' < q_z, Δ.coeff q' = 0.
    have h_Δ_below_qz : ∀ q' < q_z, Δ.coeff q' = 0 := by
      intro q' hq'
      by_contra hne
      -- q' ∈ supp Δ, and Δ ≠ 0.
      have hΔ_ne : Δ ≠ 0 := fun hΔ0 => hne (by rw [hΔ0]; exact rfl)
      have hΔ_supp_ne : Δ.support.Nonempty :=
        ⟨q', (HahnSeries.mem_support Δ q').mpr hne⟩
      set q_Δ : ℚ := Δ.isWF_support.min hΔ_supp_ne with hq_Δ_def
      have hqΔ_le_q' : q_Δ ≤ q' :=
        Δ.isWF_support.min_le hΔ_supp_ne ((HahnSeries.mem_support Δ q').mpr hne)
      have hqΔ_lt_qz : q_Δ < q_z := lt_of_le_of_lt hqΔ_le_q' hq'
      -- Δ.coeff q_Δ ≠ 0 (q_Δ in supp Δ).
      have hΔ_qΔ_ne : Δ.coeff q_Δ ≠ 0 :=
        (HahnSeries.mem_support Δ q_Δ).mp (Δ.isWF_support.min_mem hΔ_supp_ne)
      -- Below q_Δ, Δ.coeff = 0.
      have hΔ_below_qΔ : ∀ q'' < q_Δ, Δ.coeff q'' = 0 := by
        intro q'' hq''
        by_contra hne'
        have hmem : q'' ∈ Δ.support := (HahnSeries.mem_support Δ q'').mpr hne'
        exact absurd (Δ.isWF_support.min_le hΔ_supp_ne hmem) (not_le.mpr hq'')
      -- s_z q_Δ = 0 (q_Δ < q_z).
      have hsz_qΔ : s_z q_Δ = 0 := hsz_below q_Δ hqΔ_lt_qz
      -- Δ.coeff q_Δ = teich(s_x q_Δ) - teich(s_y q_Δ).
      have hΔ_at_qΔ : Δ.coeff q_Δ = teichmuller p (s_x q_Δ) - teichmuller p (s_y q_Δ) := by
        rw [hcoeff_Δ q_Δ, hsz_qΔ, WittVector.teichmuller_zero p, sub_zero]
      -- s_x q_Δ ≠ s_y q_Δ (else Δ.coeff q_Δ = 0).
      have h_sxy_diff : s_x q_Δ ≠ s_y q_Δ := by
        intro h_eq
        apply hΔ_qΔ_ne
        rw [hΔ_at_qΔ, h_eq, sub_self]
      -- Δ.coeff q_Δ is a unit (teich_sub_isUnit).
      have hΔ_qΔ_unit : IsUnit (Δ.coeff q_Δ) := by
        rw [hΔ_at_qΔ]
        exact teich_sub_isUnit h_sxy_diff
      -- Apply null_series_no_unit_leading.
      exact null_series_no_unit_leading hΔ_mem hΔ_qΔ_unit hΔ_below_qΔ
    -- Direction 2: (f_x - f_y).coeff q_z ≠ 0.
    have h_fxy_at_qz : (f_x - f_y).coeff q_z ≠ 0 := by
      intro h0
      -- Δ.coeff q_z = -f_z.coeff q_z = -teich(s_z q_z), a unit.
      have hΔ_at_qz : Δ.coeff q_z = -teichmuller p (s_z q_z) := by
        change (f_x - f_y - f_z).coeff q_z = _
        rw [HahnSeries.coeff_sub']
        change (f_x - f_y).coeff q_z - f_z.coeff q_z = _
        rw [h0, hcoeff_fz, zero_sub]
      have h_teich_unit : IsUnit (teichmuller p (s_z q_z)) :=
        (isUnit_iff_ne_zero.mpr hsz_qz_ne).map (teichmuller p)
      have hΔ_qz_unit : IsUnit (Δ.coeff q_z) := by
        rw [hΔ_at_qz]
        exact h_teich_unit.neg
      exact null_series_no_unit_leading hΔ_mem hΔ_qz_unit h_Δ_below_qz
    -- Direction 1 → for q' < q_z, (f_x - f_y).coeff q' = 0.
    have h_fxy_below_qz : ∀ q' < q_z, (f_x - f_y).coeff q' = 0 := by
      intro q' hq'
      have hΔq' : Δ.coeff q' = 0 := h_Δ_below_qz q' hq'
      have hfzq' : f_z.coeff q' = 0 := by
        rw [hcoeff_fz, hsz_below q' hq', WittVector.teichmuller_zero p]
      have : (f_x - f_y).coeff q' = Δ.coeff q' + f_z.coeff q' := by
        simp only [hΔ_def, HahnSeries.coeff_sub]
        ring
      rw [this, hΔq', hfzq', add_zero]
    -- Now combine: orderTop(f_x - f_y) = ↑q_z.
    have hfxy_ne : f_x - f_y ≠ 0 := by
      intro h0
      apply h_fxy_at_qz
      rw [h0]; rfl
    rw [HahnSeries.orderTop_of_ne_zero hfxy_ne]
    -- (f_x - f_y).isWF_support.min _ = q_z.
    have hfxy_supp_ne : (f_x - f_y).support.Nonempty :=
      ⟨q_z, (HahnSeries.mem_support _ q_z).mpr h_fxy_at_qz⟩
    -- Show (f_x - f_y).isWF_support.min hfxy_supp_ne = q_z by antisymmetry.
    have h_min_le_qz : (f_x - f_y).isWF_support.min hfxy_supp_ne ≤ q_z :=
      (f_x - f_y).isWF_support.min_le hfxy_supp_ne
        ((HahnSeries.mem_support _ q_z).mpr h_fxy_at_qz)
    have h_qz_le_min : q_z ≤ (f_x - f_y).isWF_support.min hfxy_supp_ne := by
      by_contra hlt
      push Not at hlt
      have hcoeff0 : (f_x - f_y).coeff
          ((f_x - f_y).isWF_support.min hfxy_supp_ne) = 0 :=
        h_fxy_below_qz _ hlt
      have hmem : (f_x - f_y).isWF_support.min hfxy_supp_ne ∈ (f_x - f_y).support :=
        (f_x - f_y).isWF_support.min_mem hfxy_supp_ne
      exact (HahnSeries.mem_support _ _).mp hmem hcoeff0
    have h_min_eq : (f_x - f_y).isWF_support.min hfxy_supp_ne = q_z :=
      le_antisymm h_min_le_qz h_qz_le_min
    -- Conclude.
    congr 1

/-- Build a `p`-adic Hahn series in `𝕃_[p]` from a coefficient function `s : ℚ → 𝔽ᵃ_[p]` with
well-ordered support, via the Teichmüller lift `f ↦ ∑ₖ [f(k)] pᵏ` followed by the quotient map. -/
noncomputable def fromCoeff {p : ℕ} [Fact (Nat.Prime p)]
    (s : ℚ → Fpbar p) (hspwo : (Function.support s).IsPWO) :
    (𝕃_[p]) :=
  Ideal.Quotient.mk (NullSeriesIdeal p) (LiftedPAdicHahnSeries.fromCoeff s hspwo)

/-- Round-trip: the coefficient function of the series built from `s` via `fromCoeff` is `s`
itself. -/
theorem coeff_of_fromCoeff_eq_self {p : ℕ} [Fact (Nat.Prime p)]
    (s : ℚ → Fpbar p) (hspwo : s.support.IsPWO) :
    (fromCoeff s hspwo).coeff = s := by
  have hEq :
      ⟨s, hspwo⟩ = (exists_canonical_expansion (fromCoeff s hspwo)).choose := by
    apply (exists_canonical_expansion (fromCoeff s hspwo)).choose_spec.2
    exact Quotient.exact (Quotient.out_eq (fromCoeff s hspwo))
  exact (congrArg Subtype.val hEq).symm

/-- Round-trip (converse): rebuilding a series from its own coefficient function recovers the
series. Together with `coeff_of_fromCoeff_eq_self` this shows `𝕃_[p]` is faithfully described by its
coefficient functions. -/
theorem fromCoeff_of_coeff_eq_self {p : ℕ} [Fact (Nat.Prime p)]
    (x : 𝕃_[p]) :
    fromCoeff x.coeff (support_IsPWO x) = x := by
  simp only [fromCoeff, coeff]
  set s := (exists_canonical_expansion x).choose
  have h := (exists_canonical_expansion x).choose_spec.1
  dsimp at h
  obtain ⟨y, hy⟩ := h
  have : Ideal.Quotient.mk (NullSeriesIdeal p)
      (LiftedPAdicHahnSeries.fromCoeff s.val s.prop) =
    Ideal.Quotient.mk (NullSeriesIdeal p) x.out := by
    apply Quotient.sound
    change (Ideal.Quotient.ringCon (NullSeriesIdeal p))
      (LiftedPAdicHahnSeries.fromCoeff s.val s.prop) x.out
    exact ⟨-y, by dsimp; rw [neg_vadd_eq_iff]; dsimp at hy; exact hy.symm⟩
  rw [this]; exact Quotient.out_eq x

/-- A `p`-adic Hahn series is zero iff all of its coefficients vanish. -/
theorem eq_zero_iff_coeff_zero {p : ℕ} [Fact (Nat.Prime p)] (x : 𝕃_[p]) :
  x = 0 ↔ ∀ q ∈ x.support, x.coeff q = 0 := by
  have hfrom_zero : fromCoeff (p := p) 0 (by simp) = (0 : 𝕃_[p]) := by
    have hlift_zero : LiftedPAdicHahnSeries.fromCoeff (p := p) 0 (by simp) = 0 := by
      simpa [LiftedPAdicHahnSeries.fromCoeff] using Eq.symm (Pi.zero_def : (0 : ℚ → ℤᶜᵘⁿ_[p]) = 0)
    simpa [fromCoeff] using congrArg (Ideal.Quotient.mk (NullSeriesIdeal p)) hlift_zero
  have hcoeff_zero : (0 : 𝕃_[p]).coeff = 0 := by
    rw [← hfrom_zero]
    exact coeff_of_fromCoeff_eq_self 0 (by simp)
  constructor
  · intro hx q _
    simpa [hx] using congrArg (fun f : ℚ → Fpbar p => f q) hcoeff_zero
  · intro hx
    by_contra hne
    rcases support_nonempty_of_nonzero p x hne with ⟨q, hq⟩
    have hq_ne : x.coeff q ≠ 0 := by
      simpa [support, coeff, Function.mem_support] using hq
    exact hq_ne (hx q hq)

/-- The ring embedding `ℤᶜᵘⁿ_[p] → 𝕃_[p]` sending `a` to the class of the constant series
`a · t⁰`. -/
noncomputable def ZpUn_embd {p : ℕ} [Fact (Nat.Prime p)] : ℤᶜᵘⁿ_[p] →+* 𝕃_[p] where
  toFun a := Ideal.Quotient.mk (NullSeriesIdeal p) (HahnSeries.single 0 a)
  map_one' := by simp
  map_mul' := by
    intro a b
    change Ideal.Quotient.mk (NullSeriesIdeal p) (HahnSeries.single 0 (a * b)) =
      Ideal.Quotient.mk (NullSeriesIdeal p) ((HahnSeries.single 0 a) * (HahnSeries.single 0 b))
    rw [HahnSeries.single_mul_single]
    simp
  map_zero' := by simp
  map_add' := by
    intro a b
    change Ideal.Quotient.mk (NullSeriesIdeal p) (HahnSeries.single 0 (a + b)) =
      Ideal.Quotient.mk (NullSeriesIdeal p) (HahnSeries.single 0 a + HahnSeries.single 0 b)
    rw [HahnSeries.single_add]

/-- The embedding `ZpUn_embd : ℤᶜᵘⁿ_[p] → 𝕃_[p]` is injective. -/
lemma ZpUn_embd_injective {p : ℕ} [Fact (Nat.Prime p)] :
  Function.Injective (ZpUn_embd (p := p)) := by
  intro a b hab
  have hmem0 : IsNullSeries (HahnSeries.single (0 : ℚ) a - HahnSeries.single (0 : ℚ) b) := by
    simpa [NullSeriesIdeal, ZpUn_embd, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk] using
      (Ideal.Quotient.eq.mp hab)
  have hsingle : HahnSeries.single (0 : ℚ) a - HahnSeries.single (0 : ℚ) b =
    HahnSeries.single (0 : ℚ) (a - b) := by
    ext q
    by_cases hq : q = 0
    · simp only [HahnSeries.coeff_sub', Pi.sub_apply, HahnSeries.single_sub]
    · simp [HahnSeries.coeff_single_of_ne hq]
  have hmem := hmem0
  rw [hsingle] at hmem
  let s : ℕ → Finset ℤ := fun M =>
    Set.Finite.toFinset (finiteBelow (HahnSeries.single (0 : ℚ) (a - b)) 0 M)
  let f : ℕ → QpCUn p := fun M =>
    Finset.sum (s M).attach fun n =>
      (p : QpCUn p) ^ n.val *
        algebraMap (OQpCUn p) (QpCUn p) ((HahnSeries.single (0 : ℚ) (a - b)).coeff (0 + n))
  have h0 : Filter.Tendsto f Filter.atTop (nhds 0) := by
    simpa [f, s] using hmem 0
  have hconst : f = fun _ : ℕ => algebraMap (OQpCUn p) (QpCUn p) (a - b) := by
    funext M
    classical
    unfold f
    by_cases hsub : a - b = 0
    · simp [hsub, s]
    · have hset : {n : ℤ | (0 : ℚ) + n ≤ M ∧
        (HahnSeries.single (0 : ℚ) (a - b)).coeff ((0 : ℚ) + n) ≠ 0} = {0} := by
        ext n
        constructor
        · intro hn
          have hz := HahnSeries.eq_of_mem_support_single <| (HahnSeries.mem_support _ _).2 hn.2
          have hn0 : n = 0 := by exact_mod_cast (by simpa using hz : (n : ℚ) = 0)
          simp [hn0]
        · intro hn
          rcases Set.mem_singleton_iff.mp hn with rfl
          simp [hsub]
      have hs : s M = ({0} : Finset ℤ) := by
        have hs' := (Set.Finite.toFinset_inj
            (hs := finiteBelow (HahnSeries.single (0 : ℚ) (a - b)) 0 M)
          (ht := Set.finite_singleton (0 : ℤ))).2 hset
        change Set.Finite.toFinset _ = ({0} : Finset ℤ)
        rw [hs', Set.Finite.toFinset_singleton]
      rw [hs]
      have hatt : ({0} : Finset ℤ).attach = {⟨0, by simp⟩} := by
        ext x
        rcases x with ⟨x, hx⟩
        simp at hx
        simp [hx]
      rw [hatt, Finset.sum_singleton]
      -- `↑p ^ (0 : ℤ) = 1` (WithVal's own `Pow ℤ` blocks `simp`/`rw`; close in term mode).
      rw [show ((HahnSeries.single (0 : ℚ) (a - b)).coeff (0 + ((0 : ℤ) : ℚ))) = a - b by
        simp, map_sub]
      rw [show (p : QpCUn p) ^ ((0 : ℤ)) = 1 from zpow_zero _, one_mul]
  have ht : Filter.Tendsto (fun _ : ℕ => algebraMap (OQpCUn p) (QpCUn p) (a - b))
    Filter.atTop (nhds 0) := by
    simpa [hconst] using h0
  have hmap : algebraMap (OQpCUn p) (QpCUn p) (a - b) = 0 := by
    simpa using (tendsto_const_nhds_iff.mp ht)
  exact sub_eq_zero.mp <|
    (IsFractionRing.injective (R := OQpCUn p) (K := QpCUn p)) (by simpa using hmap)

/-- The field embedding `ℚᶜᵘⁿ_[p] → 𝕃_[p]`, extending `ZpUn_embd` to fraction fields. -/
noncomputable def QpCUn_embd {p : ℕ} [Fact (Nat.Prime p)] : ℚᶜᵘⁿ_[p] →+* 𝕃_[p] :=
  IsFractionRing.map (j := ZpUn_embd (p := p)) ZpUn_embd_injective

noncomputable instance (p : ℕ) [Fact (Nat.Prime p)] : Algebra ℚᶜᵘⁿ_[p] 𝕃_[p] := QpCUn_embd.toAlgebra

instance (p : ℕ) [Fact (Nat.Prime p)] : IsScalarTower ℤᶜᵘⁿ_[p] ℚᶜᵘⁿ_[p] 𝕃_[p] := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    change ZpUn_embd x = QpCUn_embd ((algebraMap ℤᶜᵘⁿ_[p] ℚᶜᵘⁿ_[p]) x)
    unfold QpCUn_embd
    exact (IsFractionRing.lift_algebraMap (g := ZpUn_embd) ZpUn_embd_injective x).symm

noncomputable instance (p : ℕ) [Fact (Nat.Prime p)] : Algebra ℚ_[p] 𝕃_[p] :=
  (QpCUn_embd.comp QpCUn.Qp_embd).toAlgebra

noncomputable instance (p : ℕ) [Fact (Nat.Prime p)] : IsScalarTower ℚ_[p] ℚᶜᵘⁿ_[p] 𝕃_[p] :=
  IsScalarTower.of_algebraMap_smul fun _ ↦ congrFun rfl

/-- Algebraicity transfers upward along the base field extension: a `p`-adic Hahn series algebraic
over `ℚ_[p]` is also algebraic over the larger field `ℚᶜᵘⁿ_[p]`. -/
lemma alg_QpCUn_of_alg_Qp (p : ℕ) [Fact (Nat.Prime p)] (f : 𝕃_[p]) :
  IsAlgebraic ℚ_[p] f → IsAlgebraic ℚᶜᵘⁿ_[p] f := by
  intro h
  simpa using h.tower_top (ℚᶜᵘⁿ_[p])

/-- A version of `Ideal.Quotient.mk` returning `𝕃_[p]` directly. -/
private noncomputable def mkLp {p : ℕ} [Fact (Nat.Prime p)]
    (x : LiftedPAdicHahnSeries p) : 𝕃_[p] :=
  Ideal.Quotient.mk (NullSeriesIdeal p) x

private lemma mkLp_add {p : ℕ} [Fact (Nat.Prime p)] (x y : LiftedPAdicHahnSeries p) :
    mkLp (x + y) = (mkLp x : 𝕃_[p]) + mkLp y := by
  change Ideal.Quotient.mk _ _ = Ideal.Quotient.mk _ _ + Ideal.Quotient.mk _ _
  rw [map_add]

private lemma mkLp_sub {p : ℕ} [Fact (Nat.Prime p)] (x y : LiftedPAdicHahnSeries p) :
    mkLp (x - y) = (mkLp x : 𝕃_[p]) - mkLp y := by
  change Ideal.Quotient.mk _ _ = Ideal.Quotient.mk _ _ - Ideal.Quotient.mk _ _
  rw [map_sub]

private lemma mkLp_mul {p : ℕ} [Fact (Nat.Prime p)] (x y : LiftedPAdicHahnSeries p) :
    mkLp (x * y) = (mkLp x : 𝕃_[p]) * mkLp y := by
  change Ideal.Quotient.mk _ _ = Ideal.Quotient.mk _ _ * Ideal.Quotient.mk _ _
  rw [map_mul]

private lemma mkLp_pow {p : ℕ} [Fact (Nat.Prime p)] (x : LiftedPAdicHahnSeries p) (n : ℕ) :
    mkLp (x ^ n) = (mkLp x : 𝕃_[p]) ^ n := by
  change Ideal.Quotient.mk _ _ = (Ideal.Quotient.mk _ _) ^ n
  rw [map_pow]

private lemma mkLp_eq_iff_sub {p : ℕ} [Fact (Nat.Prime p)]
    (x y : LiftedPAdicHahnSeries p) :
    (mkLp x : 𝕃_[p]) = mkLp y ↔ x - y ∈ NullSeriesIdeal p :=
  Ideal.Quotient.eq

/- Helper: `(p : ℤᶜᵘⁿ_[p]) ≠ 0` (nonzero p-adic integer in the unramified ring of integers). -/
private lemma p_OQpCUn_ne_zero (p : ℕ) [Fact (Nat.Prime p)] :
    ((p : ℕ) : OQpCUn p) ≠ 0 := by
  intro h
  have hp_pos : 0 < p := (Fact.out : Nat.Prime p).pos
  have : (p : OQpCUn p) ≠ 0 := WittVector.p_nonzero p (Fpbar p)
  apply this
  exact h

/- Helper: `((p : ℕ) : 𝕃_[p]) ≠ 0`. -/
private lemma p_Lp_ne_zero (p : ℕ) [Fact (Nat.Prime p)] :
    ((p : ℕ) : 𝕃_[p]) ≠ 0 := by
  intro h
  have hp_inO : ((p : ℕ) : OQpCUn p) ≠ 0 := p_OQpCUn_ne_zero p
  apply hp_inO
  have hinj_OQ : Function.Injective (algebraMap (OQpCUn p) (ℚᶜᵘⁿ_[p])) :=
    IsFractionRing.injective _ _
  apply hinj_OQ
  have hpcast_OQ :
    algebraMap (OQpCUn p) (ℚᶜᵘⁿ_[p]) ((p : ℕ) : OQpCUn p) = ((p : ℕ) : ℚᶜᵘⁿ_[p]) := by
    push_cast; rfl
  rw [hpcast_OQ, map_zero]
  have hinj_QL : Function.Injective (algebraMap ℚᶜᵘⁿ_[p] 𝕃_[p]) := RingHom.injective _
  apply hinj_QL
  have hpcast_QL : algebraMap ℚᶜᵘⁿ_[p] 𝕃_[p] ((p : ℕ) : ℚᶜᵘⁿ_[p]) = ((p : ℕ) : 𝕃_[p]) := by
    push_cast; rfl
  rw [hpcast_QL, map_zero]; exact h

/- Helper: `single 1 1 - single 0 p` is a null series in `LiftedPAdicHahnSeries p`. -/
private lemma single_one_sub_p_mem_nullSeries (p : ℕ) [Fact (Nat.Prime p)] :
    HahnSeries.single (1 : ℚ) (1 : ℤᶜᵘⁿ_[p]) -
      HahnSeries.single (0 : ℚ) ((p : ℕ) : ℤᶜᵘⁿ_[p]) ∈ NullSeriesIdeal p := by
  classical
  change IsNullSeries _
  intro g
  set x : LiftedPAdicHahnSeries p :=
    HahnSeries.single (1 : ℚ) (1 : ℤᶜᵘⁿ_[p]) -
      HahnSeries.single (0 : ℚ) ((p : ℕ) : ℤᶜᵘⁿ_[p]) with hx_def
  have hcoeff_at_1 : x.coeff 1 = (1 : ℤᶜᵘⁿ_[p]) := by
    simp [hx_def, HahnSeries.coeff_sub']
  have hcoeff_at_0 : x.coeff 0 = -((p : ℕ) : ℤᶜᵘⁿ_[p]) := by
    simp [hx_def, HahnSeries.coeff_sub']
  have hcoeff_other : ∀ q : ℚ, q ≠ 0 → q ≠ 1 → x.coeff q = 0 := by
    intro q hq0 hq1
    simp [hx_def, HahnSeries.coeff_sub', hq0, hq1]
  have hpz_ne : ((p : ℕ) : ℤᶜᵘⁿ_[p]) ≠ 0 := p_OQpCUn_ne_zero p
  by_cases hgZ : ∃ k₀ : ℤ, g = (k₀ : ℚ)
  · obtain ⟨k₀, hk₀⟩ := hgZ
    apply tendsto_atTop_of_eventually_const (i₀ := 1)
    intro M hM
    set S := Set.Finite.toFinset (finiteBelow x g M)
    have hmem : ∀ n : ℤ, n ∈ S ↔ (n = -k₀ ∨ n = 1 - k₀) := by
      intro n
      simp only [S, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨hle, hne⟩
        by_contra hcases
        push Not at hcases
        obtain ⟨hne1, hne2⟩ := hcases
        have h0 : (g + (n : ℚ)) ≠ 0 := by
          intro h
          have : (n : ℚ) = ((-k₀ : ℤ) : ℚ) := by
            rw [hk₀] at h; push_cast at h ⊢; linarith
          exact hne1 (by exact_mod_cast this)
        have h1 : (g + (n : ℚ)) ≠ 1 := by
          intro h
          have : (n : ℚ) = ((1 - k₀ : ℤ) : ℚ) := by
            rw [hk₀] at h; push_cast at h ⊢; linarith
          exact hne2 (by exact_mod_cast this)
        exact hne (hcoeff_other _ h0 h1)
      · rintro (rfl | rfl)
        · refine ⟨?_, ?_⟩
          · rw [hk₀]; push_cast
            have : (0 : ℚ) ≤ (M : ℚ) := by exact_mod_cast Nat.zero_le M
            linarith
          · have hg_eq : g + ((-k₀ : ℤ) : ℚ) = 0 := by rw [hk₀]; push_cast; ring
            rw [hg_eq, hcoeff_at_0]
            simpa using hpz_ne
        · refine ⟨?_, ?_⟩
          · rw [hk₀]; push_cast
            have h1M : (1 : ℚ) ≤ (M : ℚ) := by exact_mod_cast hM
            linarith
          · have hg_eq : g + ((1 - k₀ : ℤ) : ℚ) = 1 := by rw [hk₀]; push_cast; ring
            rw [hg_eq, hcoeff_at_1]
            exact one_ne_zero
    have hS_eq : S = ({-k₀, 1 - k₀} : Finset ℤ) := by
      ext n
      rw [hmem n]
      simp
    rw [show (∑ n : S, (p : QpCUn p) ^ n.val *
        algebraMap (OQpCUn p) (QpCUn p) (x.coeff (g + n.val))) =
        ∑ n ∈ S, (p : QpCUn p) ^ n *
          algebraMap (OQpCUn p) (QpCUn p) (x.coeff (g + (n : ℚ))) from
      Finset.sum_attach (s := S) (f := fun n : ℤ =>
        (p : QpCUn p) ^ n *
          algebraMap (OQpCUn p) (QpCUn p) (x.coeff (g + (n : ℚ))))]
    rw [hS_eq]
    have hne : (-k₀ : ℤ) ≠ (1 - k₀ : ℤ) := by omega
    have hfs : ({-k₀, 1 - k₀} : Finset ℤ) = insert (-k₀) ({1 - k₀} : Finset ℤ) := rfl
    rw [hfs, Finset.sum_insert (by simp [hne]), Finset.sum_singleton]
    have hg0 : g + ((-k₀ : ℤ) : ℚ) = 0 := by rw [hk₀]; push_cast; ring
    have hg1 : g + ((1 - k₀ : ℤ) : ℚ) = 1 := by rw [hk₀]; push_cast; ring
    rw [hg0, hg1, hcoeff_at_0, hcoeff_at_1]
    have hp_ne_QpCUn : (p : QpCUn p) ≠ 0 := by
      intro h
      have hp_in_O : ((p : ℕ) : OQpCUn p) ≠ 0 := p_OQpCUn_ne_zero p
      apply hp_in_O
      have hinj : Function.Injective (algebraMap (OQpCUn p) (QpCUn p)) :=
        IsFractionRing.injective _ _
      apply hinj
      have hpz_eq : algebraMap (OQpCUn p) (QpCUn p) ((p : ℕ) : OQpCUn p) = (p : QpCUn p) := by
        push_cast; rfl
      rw [hpz_eq, map_zero]; exact h
    rw [map_neg, map_one]
    have hpz_in_QpCUn : algebraMap (OQpCUn p) (QpCUn p) ((p : ℕ) : OQpCUn p) = (p : QpCUn p) := by
      push_cast; rfl
    rw [hpz_in_QpCUn]
    rw [show ((p : QpCUn p) ^ (1 - k₀ : ℤ) : QpCUn p) =
          (p : QpCUn p) ^ (-k₀ : ℤ) * (p : QpCUn p) from by
      rw [show (1 - k₀ : ℤ) = (-k₀ : ℤ) + 1 from by ring,
        zpow_add₀ hp_ne_QpCUn, zpow_one]]
    ring
  · push Not at hgZ
    apply Filter.Tendsto.congr (f₁ := fun _ : ℕ => (0 : QpCUn p)) ?_ tendsto_const_nhds
    intro M
    have hempty : Set.Finite.toFinset (finiteBelow x g M) = (∅ : Finset ℤ) := by
      ext n
      simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, Finset.notMem_empty,
        iff_false, not_and]
      intro hle hne
      have h0 : (g + (n : ℚ)) ≠ 0 := by
        intro h
        apply hgZ (-n)
        push_cast; linarith
      have h1 : (g + (n : ℚ)) ≠ 1 := by
        intro h
        apply hgZ (1 - n)
        push_cast; linarith
      exact hne (hcoeff_other _ h0 h1)
    rw [show (∑ n : Set.Finite.toFinset (finiteBelow x g M),
        (p : QpCUn p) ^ n.val *
          algebraMap (OQpCUn p) (QpCUn p) (x.coeff (g + n.val))) =
        ∑ n ∈ Set.Finite.toFinset (finiteBelow x g M), (p : QpCUn p) ^ n *
          algebraMap (OQpCUn p) (QpCUn p) (x.coeff (g + (n : ℚ))) from
      Finset.sum_attach (s := Set.Finite.toFinset (finiteBelow x g M)) (f := fun n : ℤ =>
        (p : QpCUn p) ^ n *
          algebraMap (OQpCUn p) (QpCUn p) (x.coeff (g + (n : ℚ))))]
    rw [hempty, Finset.sum_empty]

/- Helper: `mkLp(single 1 1) = (p : 𝕃_[p])`. -/
private lemma mk_single_one_eq_p (p : ℕ) [Fact (Nat.Prime p)] :
    (mkLp (HahnSeries.single (1 : ℚ) (1 : ℤᶜᵘⁿ_[p])) : 𝕃_[p]) = ((p : ℕ) : 𝕃_[p]) := by
  have hp_eq : ((p : ℕ) : 𝕃_[p]) =
      (mkLp (HahnSeries.single (0 : ℚ) ((p : ℕ) : ℤᶜᵘⁿ_[p])) : 𝕃_[p]) := by
    change ((p : ℕ) : 𝕃_[p]) = Ideal.Quotient.mk _ _
    have hsingle_eq : HahnSeries.single (0 : ℚ) ((p : ℕ) : ℤᶜᵘⁿ_[p]) =
        ((p : ℕ) : LiftedPAdicHahnSeries p) := by
      rw [HahnSeries.single_zero_natCast]
    rw [hsingle_eq]
    rfl
  rw [hp_eq]
  exact (mkLp_eq_iff_sub _ _).mpr (single_one_sub_p_mem_nullSeries p)

/- Helper: `mkLp(single n 1) = (p : 𝕃_[p])^n` for `n : ℕ`. -/
private lemma mk_single_nat_eq_p_pow (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ) :
    (mkLp (HahnSeries.single ((n : ℕ) : ℚ) (1 : ℤᶜᵘⁿ_[p])) : 𝕃_[p]) = ((p : ℕ) : 𝕃_[p]) ^ n := by
  induction n with
  | zero =>
    show (mkLp _ : 𝕃_[p]) = _
    rw [show ((0 : ℕ) : ℚ) = (0 : ℚ) by norm_cast]
    rw [HahnSeries.single_zero_one]
    change (Ideal.Quotient.mk _ 1 : 𝕃_[p]) = _
    rw [map_one, pow_zero]
  | succ n ih =>
    have hsmm : HahnSeries.single ((n + 1 : ℕ) : ℚ) (1 : ℤᶜᵘⁿ_[p]) =
        HahnSeries.single ((n : ℕ) : ℚ) (1 : ℤᶜᵘⁿ_[p]) * HahnSeries.single (1 : ℚ) 1 := by
      rw [HahnSeries.single_mul_single, mul_one]
      congr 1
      push_cast; rfl
    rw [hsmm, mkLp_mul, ih, mk_single_one_eq_p, pow_succ]

/- Helper: `mkLp(single n 1) = (p : 𝕃_[p])^n` for `n : ℤ`. -/
private lemma mk_single_int_eq_p_zpow (p : ℕ) [Fact (Nat.Prime p)] (n : ℤ) :
    (mkLp (HahnSeries.single ((n : ℤ) : ℚ) (1 : ℤᶜᵘⁿ_[p])) : 𝕃_[p]) = ((p : ℕ) : 𝕃_[p]) ^ n := by
  obtain ⟨k, hk⟩ := Int.eq_nat_or_neg n
  rcases hk with hk | hk
  · subst hk
    rw [show ((k : ℕ) : ℤ) = (k : ℤ) by rfl] at *
    rw [show (((k : ℕ) : ℤ) : ℚ) = ((k : ℕ) : ℚ) by push_cast; rfl]
    rw [zpow_natCast]
    exact mk_single_nat_eq_p_pow p k
  · subst hk
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · subst hk0
      simp only [Nat.cast_zero, neg_zero, Int.cast_zero, zpow_zero]
      change (mkLp (HahnSeries.single (0 : ℚ) (1 : ℤᶜᵘⁿ_[p])) : 𝕃_[p]) = 1
      rw [HahnSeries.single_zero_one]
      change (Ideal.Quotient.mk _ 1 : 𝕃_[p]) = 1
      exact map_one _
    · have hprod : HahnSeries.single ((-(k : ℤ) : ℤ) : ℚ) (1 : ℤᶜᵘⁿ_[p]) *
          HahnSeries.single ((k : ℕ) : ℚ) (1 : ℤᶜᵘⁿ_[p]) = HahnSeries.single 0 1 := by
        rw [HahnSeries.single_mul_single, mul_one]
        congr 1
        push_cast
        simp only [neg_add_cancel]
      have hp_pow_ne : ((p : ℕ) : 𝕃_[p]) ^ k ≠ 0 := pow_ne_zero _ (p_Lp_ne_zero p)
      have hmkprod :
          (mkLp (HahnSeries.single ((-(k : ℤ) : ℤ) : ℚ) (1 : ℤᶜᵘⁿ_[p])) : 𝕃_[p]) *
          (mkLp (HahnSeries.single ((k : ℕ) : ℚ) (1 : ℤᶜᵘⁿ_[p])) : 𝕃_[p]) = 1 := by
        rw [← mkLp_mul, hprod]
        show (mkLp (HahnSeries.single (0 : ℚ) (1 : ℤᶜᵘⁿ_[p])) : 𝕃_[p]) = 1
        rw [HahnSeries.single_zero_one]
        change (Ideal.Quotient.mk _ 1 : 𝕃_[p]) = 1
        exact map_one _
      rw [mk_single_nat_eq_p_pow p k] at hmkprod
      have heq :
          (mkLp (HahnSeries.single ((-(k : ℤ) : ℤ) : ℚ) (1 : ℤᶜᵘⁿ_[p])) : 𝕃_[p]) =
            (((p : ℕ) : 𝕃_[p]) ^ k)⁻¹ :=
        (inv_eq_of_mul_eq_one_left hmkprod).symm
      rw [heq, zpow_neg, zpow_natCast]

/- Helper: For `q : ℚ` and `a : ℤᶜᵘⁿ_[p]`,
`(mkLp(single q a))^q.den = (p : 𝕃_[p])^q.num * mkLp(single 0 (a^q.den))`. -/
private lemma mkLp_single_pow_den (p : ℕ) [Fact (Nat.Prime p)] (q : ℚ) (a : ℤᶜᵘⁿ_[p]) :
    (mkLp (HahnSeries.single q a) : 𝕃_[p]) ^ (q.den : ℕ) =
      ((p : ℕ) : 𝕃_[p]) ^ q.num *
        (mkLp (HahnSeries.single (0 : ℚ) (a ^ (q.den : ℕ))) : 𝕃_[p]) := by
  rw [← mkLp_pow, HahnSeries.single_pow]
  have hq_smul : (q.den : ℕ) • q = ((q.num : ℤ) : ℚ) := by
    rw [nsmul_eq_mul, Rat.den_mul_eq_num]
  rw [hq_smul]
  have hsingle_split : HahnSeries.single ((q.num : ℤ) : ℚ) (a ^ (q.den : ℕ)) =
      HahnSeries.single ((q.num : ℤ) : ℚ) (1 : ℤᶜᵘⁿ_[p]) *
        HahnSeries.single (0 : ℚ) (a ^ (q.den : ℕ)) := by
    rw [HahnSeries.single_mul_single]
    congr 1
    · simp only [add_zero]
    · rw [one_mul]
  rw [hsingle_split, mkLp_mul, mk_single_int_eq_p_zpow]

/- Helper: For `a : Fpbar p`, there exists `n ≥ 1` with `a ^ (p ^ n) = a`.
This uses that `Fpbar p = AlgebraicClosure (ZMod p)`, so `a` lies in a finite
intermediate field of cardinality `p ^ d`. -/
private lemma exists_pow_p_eq_self_Fpbar (p : ℕ) [Fact (Nat.Prime p)] (a : Fpbar p) :
    ∃ n : ℕ, 0 < n ∧ a ^ (p ^ n) = a := by
  classical
  have hint : IsIntegral (ZMod p) a := Algebra.IsIntegral.isIntegral a
  let K : IntermediateField (ZMod p) (Fpbar p) :=
    IntermediateField.adjoin (ZMod p) ({a} : Set (Fpbar p))
  have : FiniteDimensional (ZMod p) K :=
    IntermediateField.adjoin.finiteDimensional hint
  have : Finite K := Module.finite_of_finite (ZMod p)
  have : Fintype K := Fintype.ofFinite _
  have ha_in_K : a ∈ K :=
    IntermediateField.subset_adjoin _ _ (Set.mem_singleton _)
  set d := Fintype.card K with hd_def
  have hd_pow : ∃ n, 0 < n ∧ d = p ^ n := by
    have hcard : (Fintype.card K : ℕ) =
        (Fintype.card (ZMod p)) ^ Module.finrank (ZMod p) K :=
      Module.card_eq_pow_finrank
    rw [ZMod.card] at hcard
    exact ⟨_, Module.finrank_pos, hcard⟩
  obtain ⟨n, hn_pos, hn_eq⟩ := hd_pow
  refine ⟨n, hn_pos, ?_⟩
  have h_inK : (⟨a, ha_in_K⟩ : K) ^ d = ⟨a, ha_in_K⟩ := FiniteField.pow_card _
  rw [hn_eq] at h_inK
  exact congrArg Subtype.val h_inK

/- Helper: `ZpUn_embd (teichmuller p a)` (the image of the Teichmüller lift in `𝕃_[p]`)
is algebraic over `ℚ_[p]`. The witness is the polynomial `X^(p^n) - X ∈ ℤ ⊂ ℚ_[p][X]`,
where `n` comes from `exists_pow_p_eq_self_Fpbar`. -/
private lemma teich_isAlgebraic_Qp (p : ℕ) [Fact (Nat.Prime p)] (a : Fpbar p) :
    IsAlgebraic ℚ_[p] (ZpUn_embd (teichmuller p a) : 𝕃_[p]) := by
  obtain ⟨n, hn_pos, han⟩ := exists_pow_p_eq_self_Fpbar p a
  set x : 𝕃_[p] := ZpUn_embd (teichmuller p a) with hx_def
  have hteich_pow : (teichmuller p a) ^ (p ^ n) = teichmuller p a := by
    rw [← map_pow]; exact congrArg _ han
  have hx_pow : x ^ (p ^ n) = x := by
    rw [hx_def, ← map_pow, hteich_pow]
  refine ⟨Polynomial.X ^ (p ^ n) - Polynomial.X, ?_, ?_⟩
  · intro hpoly_zero
    have hp_pos : 0 < p := (Fact.out : Nat.Prime p).pos
    have hp_ge_two : 2 ≤ p := (Fact.out : Nat.Prime p).two_le
    have hpn_ge_two : 2 ≤ p ^ n := by
      calc 2 ≤ p := hp_ge_two
        _ = p ^ 1 := (pow_one p).symm
        _ ≤ p ^ n := Nat.pow_le_pow_right (by omega) hn_pos
    have hdeg :
        (Polynomial.X ^ (p ^ n) - Polynomial.X : Polynomial ℚ_[p]).natDegree = p ^ n := by
      rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt]
      · exact Polynomial.natDegree_X_pow _
      · rw [Polynomial.natDegree_X_pow, Polynomial.natDegree_X]; omega
    rw [hpoly_zero, Polynomial.natDegree_zero] at hdeg
    omega
  · simp [hx_pow]

/- Helper: For `q : ℚ` and `a : Fpbar p`,
`mkLp(single q (teich a))` is algebraic over `ℚ_[p]`. -/
private lemma alg_of_single (p : ℕ) [Fact (Nat.Prime p)] (q : ℚ) (a : Fpbar p) :
    IsAlgebraic ℚ_[p]
      (mkLp (HahnSeries.single q (teichmuller p a)) : 𝕃_[p]) := by
  set f : 𝕃_[p] := mkLp (HahnSeries.single q (teichmuller p a)) with hf_def
  have hfN := mkLp_single_pow_den p q (teichmuller p a)
  rw [← hf_def] at hfN
  -- `f^q.den = (p^q.num) * mkLp(single 0 (teich(a)^q.den))`.
  -- First factor lies in image of `ℚ_[p]`, hence algebraic over `ℚ_[p]`.
  -- Second factor equals `(ZpUn_embd (teich a))^q.den`, algebraic by `teich_isAlgebraic_Qp.pow`.
  have h_factor_alg : IsAlgebraic ℚ_[p] (((p : ℕ) : 𝕃_[p]) ^ q.num) := by
    have h_in_range : ((p : ℕ) : 𝕃_[p]) ^ q.num ∈
        Set.range (algebraMap ℚ_[p] 𝕃_[p]) := by
      refine ⟨((p : ℕ) : ℚ_[p]) ^ q.num, ?_⟩
      rw [map_zpow₀, map_natCast]
    obtain ⟨c, hc⟩ := h_in_range
    rw [← hc]; exact isAlgebraic_algebraMap c
  have h_teich_alg : IsAlgebraic ℚ_[p]
      ((mkLp (HahnSeries.single (0 : ℚ) ((teichmuller p a) ^ (q.den : ℕ))) : 𝕃_[p])) := by
    -- `mkLp(single 0 b) = ZpUn_embd b` for any `b : ℤᶜᵘⁿ_[p]`.
    have hLHS : (mkLp (HahnSeries.single (0 : ℚ) ((teichmuller p a) ^ (q.den : ℕ))) : 𝕃_[p]) =
        ZpUn_embd ((teichmuller p a) ^ (q.den : ℕ)) := rfl
    have hPow : ZpUn_embd ((teichmuller p a) ^ (q.den : ℕ)) =
        (ZpUn_embd (teichmuller p a)) ^ (q.den : ℕ) := by rw [map_pow]
    rw [hLHS, hPow]
    exact (teich_isAlgebraic_Qp p a).pow q.den
  have hfN_alg : IsAlgebraic ℚ_[p] (f ^ (q.den : ℕ)) := by
    rw [hfN]; exact h_factor_alg.mul h_teich_alg
  exact hfN_alg.of_pow q.pos

/- Helper: `(f - mkLp(single q (teich (f.coeff q)))).coeff = Function.update f.coeff q 0`. -/
private lemma sub_single_coeff (p : ℕ) [Fact (Nat.Prime p)]
    (f : 𝕃_[p]) (q : ℚ) :
    ((f - (mkLp (HahnSeries.single q (teichmuller p (f.coeff q))) : 𝕃_[p])).coeff) =
      Function.update f.coeff q 0 := by
  have hfeq : f = fromCoeff f.coeff (support_IsPWO f) := (fromCoeff_of_coeff_eq_self f).symm
  have hpwo : (Function.update f.coeff q 0).support.IsPWO := by
    apply Set.IsPWO.mono (support_IsPWO f)
    intro n hn
    rw [Function.mem_support] at hn
    by_cases hnq : n = q
    · subst hnq
      simp [Function.update_self] at hn
    · rw [Function.update_of_ne hnq] at hn
      exact hn
  have hfrom_sub :
      LiftedPAdicHahnSeries.fromCoeff f.coeff (support_IsPWO f) -
        HahnSeries.single q ((teichmuller p) (f.coeff q)) =
      LiftedPAdicHahnSeries.fromCoeff (Function.update f.coeff q 0) hpwo := by
    apply HahnSeries.ext
    funext n
    rw [HahnSeries.coeff_sub']
    change (teichmuller p) (f.coeff n) -
              (HahnSeries.single q ((teichmuller p) (f.coeff q))).coeff n =
            (teichmuller p) (Function.update f.coeff q 0 n)
    by_cases hnq : n = q
    · subst hnq
      rw [HahnSeries.coeff_single_same, Function.update_self,
        WittVector.teichmuller_zero]
      ring
    · rw [HahnSeries.coeff_single_of_ne hnq, Function.update_of_ne hnq]
      ring
  have hsub_eq :
      f - (mkLp (HahnSeries.single q ((teichmuller p) (f.coeff q))) : 𝕃_[p]) =
      fromCoeff (Function.update f.coeff q 0) hpwo := by
    have key : f - (mkLp (HahnSeries.single q ((teichmuller p) (f.coeff q))) : 𝕃_[p]) =
        (mkLp (LiftedPAdicHahnSeries.fromCoeff f.coeff (support_IsPWO f)) : 𝕃_[p]) -
        (mkLp (HahnSeries.single q ((teichmuller p) (f.coeff q))) : 𝕃_[p]) := by
      congr 1
    rw [key, ← mkLp_sub, hfrom_sub]
    rfl
  rw [hsub_eq]
  exact coeff_of_fromCoeff_eq_self _ _

/- Helper: For `q ∈ f.support`,
`(f - mkLp(single q (teich (f.coeff q)))).support ⊂ f.support`. -/
private lemma support_sub_single_ssubset (p : ℕ) [Fact (Nat.Prime p)]
    (f : 𝕃_[p]) (q : ℚ) (hq : q ∈ f.support) :
    (f - (mkLp (HahnSeries.single q (teichmuller p (f.coeff q))) : 𝕃_[p])).support ⊂
      f.support := by
  set g := f - (mkLp (HahnSeries.single q (teichmuller p (f.coeff q))) : 𝕃_[p]) with hg_def
  have hgcoeff := sub_single_coeff p f q
  have hg_support : g.support = (Function.update f.coeff q 0).support := by
    change (g.coeff).support = _
    rw [hgcoeff]
  refine ⟨?_, ?_⟩
  · intro q' hq'
    rw [hg_support] at hq'
    rw [Function.mem_support] at hq'
    by_cases hcase : q' = q
    · subst hcase
      simp [Function.update_self] at hq'
    · rw [Function.update_of_ne hcase] at hq'
      change f.coeff q' ≠ 0
      exact hq'
  · intro hsub
    have hq_in_g : q ∈ g.support := hsub hq
    rw [hg_support] at hq_in_g
    rw [Function.mem_support] at hq_in_g
    simp [Function.update_self] at hq_in_g

/-- A `p`-adic Hahn series with finite support is algebraic over `ℚ_[p]`: a finite-support series is
a `ℚ_[p]`-linear combination of finitely many Teichmüller monomials, each algebraic over `ℚ_[p]`. -/
lemma alg_of_fin_supp (p : ℕ) [Fact (Nat.Prime p)] (f : 𝕃_[p]) (hf : f.support.Finite) :
  IsAlgebraic ℚ_[p] f := by
  classical
  generalize hn : hf.toFinset.card = n
  induction n using Nat.strong_induction_on generalizing f with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · subst hn0
      have hempty : hf.toFinset = ∅ := Finset.card_eq_zero.mp hn
      have hsupp_empty : f.support = ∅ := by
        have hcoe : (hf.toFinset : Set ℚ) = ((∅ : Finset ℚ) : Set ℚ) := by
          rw [hempty]
        rw [Set.Finite.coe_toFinset] at hcoe
        simp only [Finset.coe_empty] at hcoe
        exact hcoe
      have hf_zero : f = 0 := by
        apply (eq_zero_iff_coeff_zero f).mpr
        intro q hq
        rw [hsupp_empty] at hq
        exact absurd hq (id (Set.notMem_empty q))
      rw [hf_zero]
      exact isAlgebraic_zero
    · have hnonempty : hf.toFinset.Nonempty := Finset.card_pos.mp (by rw [hn]; exact hnpos)
      obtain ⟨q, hq⟩ := hnonempty
      rw [Set.Finite.mem_toFinset] at hq
      set h : 𝕃_[p] := mkLp (HahnSeries.single q (teichmuller p (f.coeff q))) with hh_def
      set g : 𝕃_[p] := f - h with hg_def
      have hg_supp_ssub : g.support ⊂ f.support := support_sub_single_ssubset p f q hq
      have hg_supp_fin : g.support.Finite := hf.subset hg_supp_ssub.subset
      have hg_card : hg_supp_fin.toFinset.card < n := by
        rw [← hn]
        apply Finset.card_lt_card
        rw [Finset.ssubset_iff_subset_ne]
        refine ⟨?_, ?_⟩
        · intro x hx
          rw [Set.Finite.mem_toFinset] at hx ⊢
          exact hg_supp_ssub.subset hx
        · intro hheq
          have h_eq : g.support = f.support := by
            apply Set.eq_of_subset_of_subset hg_supp_ssub.subset
            intro x hx
            have hx' : x ∈ hf.toFinset := (Set.Finite.mem_toFinset _).mpr hx
            rw [← hheq] at hx'
            exact (Set.Finite.mem_toFinset _).mp hx'
          exact hg_supp_ssub.ne h_eq
      have hg_alg : IsAlgebraic ℚ_[p] g :=
        ih hg_supp_fin.toFinset.card hg_card g hg_supp_fin rfl
      have hh_alg : IsAlgebraic ℚ_[p] h := alg_of_single p q (f.coeff q)
      have hfeq : f = g + h := by rw [hg_def]; ring
      rw [hfeq]
      exact hg_alg.add hh_alg

end pAdicHahnSeries

end TrustworthyKedlaya
