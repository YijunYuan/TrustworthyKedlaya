/-
Copyright (c) 2026 Shanwen Wang, Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.RingTheory.HahnSeries.Multiplication
public import Mathlib.FieldTheory.Perfect
public import Mathlib.Algebra.CharP.Algebra

/-!
# Frobenius acts coefficientwise on Hahn series over `ℚ`

Over a commutative ring `R` of characteristic `p`, the `p`-th power map on
`HahnSeries ℚ R` is computed coefficientwise together with the support scaling
`i ↦ p·i`:

- `TrustworthyKedlaya.coeff_pow_char`: `(x ^ p).coeff g = (x.coeff (g / p)) ^ p`.

No multinomial or orbit-counting combinatorics is needed: for a *fixed* exponent `g`,
split `x = x_{< g/p} + x_{g/p} + x_{> g/p}` (restriction of the coefficient function).
The `p`-th power is additive in characteristic `p` (`add_pow_char`), the `p`-th powers
of the outer parts are supported strictly below resp. above `g`, and the middle single
term contributes exactly `(x.coeff (g/p))^p`.

From the formula we obtain the inverse Frobenius:

- `TrustworthyKedlaya.invFrobeniusHahn`: for `R` perfect, the preimage of `x` under the
  `p`-th power map, with `invFrobeniusHahn_pow : invFrobeniusHahn p x ^ p = x`;
- `TrustworthyKedlaya.pow_char_bijective`: the Frobenius of `HahnSeries ℚ R` is
  bijective when `R` is perfect.

The restriction-of-support construction `TrustworthyKedlaya.hahnRestrict` is shared
infrastructure (it also implements truncation of Hahn series at a point).
-/

@[expose] public section

namespace TrustworthyKedlaya

open HahnSeries

variable {R : Type*}

/-! ### Restricting the coefficient function to a set of exponents -/

/-- Restriction of a Hahn series to a set `S` of exponents: keep the coefficients with
exponent in `S`, zero out the rest. -/
noncomputable def hahnRestrict [Zero R] (S : Set ℚ) (x : HahnSeries ℚ R) :
    HahnSeries ℚ R where
  coeff := S.indicator x.coeff
  isPWO_support' := x.isPWO_support'.mono fun g hg => by
    rw [Function.mem_support] at hg ⊢
    intro h0
    apply hg
    by_cases hgS : g ∈ S
    · rw [Set.indicator_of_mem hgS, h0]
    · exact Set.indicator_of_notMem hgS _

theorem coeff_hahnRestrict_of_mem [Zero R] {S : Set ℚ} (x : HahnSeries ℚ R) {g : ℚ}
    (h : g ∈ S) : (hahnRestrict S x).coeff g = x.coeff g :=
  Set.indicator_of_mem h _

theorem coeff_hahnRestrict_of_notMem [Zero R] {S : Set ℚ} (x : HahnSeries ℚ R) {g : ℚ}
    (h : g ∉ S) : (hahnRestrict S x).coeff g = 0 :=
  Set.indicator_of_notMem h _

theorem support_hahnRestrict_subset [Zero R] (S : Set ℚ) (x : HahnSeries ℚ R) :
    (hahnRestrict S x).support ⊆ x.support := fun g hg => by
  rw [HahnSeries.mem_support] at hg ⊢
  intro h0
  apply hg
  by_cases hgS : g ∈ S
  · rw [coeff_hahnRestrict_of_mem x hgS, h0]
  · exact coeff_hahnRestrict_of_notMem x hgS

theorem support_hahnRestrict_subset_set [Zero R] (S : Set ℚ) (x : HahnSeries ℚ R) :
    (hahnRestrict S x).support ⊆ S := fun g hg => by
  rw [HahnSeries.mem_support] at hg
  by_contra h
  exact hg (coeff_hahnRestrict_of_notMem x h)

/-- Three-way decomposition of a Hahn series at a point `θ` of the exponent line:
the part strictly below `θ`, the single term at `θ`, and the part strictly above `θ`. -/
theorem hahnRestrict_tridecomp [AddCommMonoid R] (θ : ℚ) (x : HahnSeries ℚ R) :
    x = hahnRestrict (Set.Iio θ) x + single θ (x.coeff θ)
        + hahnRestrict (Set.Ioi θ) x := by
  ext g
  rw [HahnSeries.coeff_add, HahnSeries.coeff_add]
  rcases lt_trichotomy g θ with h | rfl | h
  · rw [coeff_hahnRestrict_of_mem x (Set.mem_Iio.mpr h),
      coeff_single_of_ne h.ne,
      coeff_hahnRestrict_of_notMem x (by simp [Set.mem_Ioi, not_lt_of_gt h]),
      add_zero, add_zero]
  · rw [coeff_hahnRestrict_of_notMem x (by simp),
      coeff_hahnRestrict_of_notMem x (by simp),
      coeff_single_same, zero_add, add_zero]
  · rw [coeff_hahnRestrict_of_mem x (Set.mem_Ioi.mpr h),
      coeff_single_of_ne h.ne',
      coeff_hahnRestrict_of_notMem x (by simp [Set.mem_Iio, not_lt_of_gt h]),
      zero_add, zero_add]

/-! ### Support bounds for powers -/

/-- If every exponent of `y` is `< θ`, every exponent of `y ^ n` (`n ≥ 1`) is `< n·θ`. -/
theorem support_pow_lt [CommRing R] {y : HahnSeries ℚ R} {θ : ℚ}
    (hy : ∀ i ∈ y.support, i < θ) :
    ∀ n : ℕ, 1 ≤ n → ∀ g ∈ (y ^ n).support, g < n * θ := by
  intro n
  induction n with
  | zero => omega
  | succ n ih =>
    intro _ g hg
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [pow_one] at hg
      simpa using hy g hg
    · rw [pow_succ] at hg
      obtain ⟨g₁, hg₁, g₂, hg₂, rfl⟩ := support_mul_subset hg
      have h1 := ih hn g₁ hg₁
      have h2 := hy g₂ hg₂
      push_cast
      linarith

/-- If every exponent of `y` is `> θ`, every exponent of `y ^ n` (`n ≥ 1`) is `> n·θ`. -/
theorem support_pow_gt [CommRing R] {y : HahnSeries ℚ R} {θ : ℚ}
    (hy : ∀ i ∈ y.support, θ < i) :
    ∀ n : ℕ, 1 ≤ n → ∀ g ∈ (y ^ n).support, n * θ < g := by
  intro n
  induction n with
  | zero => omega
  | succ n ih =>
    intro _ g hg
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [pow_one] at hg
      simpa using hy g hg
    · rw [pow_succ] at hg
      obtain ⟨g₁, hg₁, g₂, hg₂, rfl⟩ := support_mul_subset hg
      have h1 := ih hn g₁ hg₁
      have h2 := hy g₂ hg₂
      push_cast
      linarith

/-- Powers of single terms. -/
theorem single_pow [CommRing R] (a : ℚ) (r : R) :
    ∀ n : ℕ, (single a r : HahnSeries ℚ R) ^ n = single (n * a) (r ^ n) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, single_mul_single, pow_succ]
    push_cast
    ring_nf

/-! ### The coefficientwise formula for the Frobenius -/

variable [CommRing R]

instance instCharPHahnSeries (p : ℕ) [CharP R p] : CharP (HahnSeries ℚ R) p :=
  charP_of_injective_ringHom (f := HahnSeries.C (Γ := ℚ) (R := R))
    (fun _ _ h => by simpa using congrArg (fun z => z.coeff 0) h) p

variable {p : ℕ} [hp : Fact p.Prime] [CharP R p]

/-- **The Frobenius of `HahnSeries ℚ R` acts coefficientwise**, with the support
scaling `i ↦ p·i`:  `(x ^ p).coeff g = (x.coeff (g / p)) ^ p` for every `g`.
(When `g/p` is not in the support both sides are `0`.) -/
theorem coeff_pow_char (x : HahnSeries ℚ R) (g : ℚ) :
    (x ^ p).coeff g = x.coeff (g / p) ^ p := by
  have : ExpChar (HahnSeries ℚ R) p := .prime hp.out
  have hp0 : (0 : ℚ) < (p : ℚ) := by exact_mod_cast hp.out.pos
  have hp1 : 1 ≤ p := hp.out.one_lt.le
  set θ : ℚ := g / p with hθ
  have hgθ : (p : ℚ) * θ = g := mul_div_cancel₀ g hp0.ne'
  -- Split `x` at the exponent `θ` and take `p`-th powers additively.
  rw [show x ^ p = (hahnRestrict (Set.Iio θ) x + single θ (x.coeff θ)
      + hahnRestrict (Set.Ioi θ) x) ^ p from by rw [← hahnRestrict_tridecomp],
    add_pow_char, add_pow_char, HahnSeries.coeff_add, HahnSeries.coeff_add]
  -- The part below `θ` contributes nothing at `g = p·θ`.
  have hlo : ((hahnRestrict (Set.Iio θ) x) ^ p).coeff g = 0 := by
    by_contra h0
    have := support_pow_lt
      (fun i hi => support_hahnRestrict_subset_set _ x hi) p hp1 g h0
    rw [hgθ] at this
    exact lt_irrefl g this
  -- The part above `θ` contributes nothing at `g = p·θ`.
  have hhi : ((hahnRestrict (Set.Ioi θ) x) ^ p).coeff g = 0 := by
    by_contra h0
    have := support_pow_gt
      (fun i hi => support_hahnRestrict_subset_set _ x hi) p hp1 g h0
    rw [hgθ] at this
    exact lt_irrefl g this
  -- The single term at `θ` contributes exactly `(x.coeff θ)^p`.
  rw [hlo, hhi, single_pow, hgθ, zero_add, add_zero, coeff_single_same]

/-! ### The inverse Frobenius -/

section Perfect

variable [PerfectRing R p]

/-- The inverse Frobenius of a Hahn series over a perfect ring: coefficientwise inverse
Frobenius together with the support scaling `i ↦ i / p`. -/
noncomputable def invFrobeniusHahn (p : ℕ) [Fact p.Prime] [CharP R p] [PerfectRing R p]
    (x : HahnSeries ℚ R) : HahnSeries ℚ R where
  coeff g := (frobeniusEquiv R p).symm (x.coeff (p * g))
  isPWO_support' := by
    have hp0 : (0 : ℚ) < (p : ℚ) := by exact_mod_cast (Fact.out : p.Prime).pos
    have hmono : Monotone fun i : ℚ => i / p := fun i j hij =>
      div_le_div_of_nonneg_right hij hp0.le
    refine (x.isPWO_support'.image_of_monotone hmono).mono ?_
    intro g hg
    rw [Function.mem_support] at hg
    refine ⟨p * g, ?_, by field_simp⟩
    rw [Function.mem_support]
    intro h0
    rw [h0, map_zero] at hg
    exact hg rfl

@[simp] theorem coeff_invFrobeniusHahn (x : HahnSeries ℚ R) (g : ℚ) :
    (invFrobeniusHahn p x).coeff g = (frobeniusEquiv R p).symm (x.coeff (p * g)) := rfl

/-- The inverse Frobenius is a right inverse of the `p`-th power map. -/
theorem invFrobeniusHahn_pow (x : HahnSeries ℚ R) : invFrobeniusHahn p x ^ p = x := by
  ext g
  rw [coeff_pow_char, coeff_invFrobeniusHahn]
  have hp0 : ((p : ℚ)) ≠ 0 := by exact_mod_cast hp.out.pos.ne'
  rw [mul_div_cancel₀ g hp0]
  exact frobeniusEquiv_symm_pow_p R p _

/-- **The Frobenius `x ↦ x^p` of `HahnSeries ℚ R` is bijective** for `R` perfect. -/
theorem pow_char_bijective :
    Function.Bijective fun x : HahnSeries ℚ R => x ^ p := by
  constructor
  · intro x y hxy
    ext g
    have hcoeff := congrArg (fun z : HahnSeries ℚ R => z.coeff (p * g)) hxy
    simp only [coeff_pow_char] at hcoeff
    have hp0 : ((p : ℚ)) ≠ 0 := by exact_mod_cast hp.out.pos.ne'
    rw [mul_div_cancel_left₀ g hp0] at hcoeff
    exact (frobeniusEquiv R p).injective
      (by simpa [frobeniusEquiv_apply, frobenius_def] using hcoeff)
  · intro x
    exact ⟨invFrobeniusHahn p x, invFrobeniusHahn_pow x⟩

end Perfect

end TrustworthyKedlaya
