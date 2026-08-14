/-
Copyright (c) 2026 Shanwen Wang, Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import TrustworthyKedlaya.ArtinSchreierPos
public import TrustworthyKedlaya.Truncation

/-!
# UP is closed under Artin-Schreier roots

If `y ∈ 𝔽̄_p((t^ℚ))` is uniformly periodic and `x^p - x = y`, then `x` is uniformly
periodic (Kedlaya (2001a), Lemma 4).

Present `y` by a slice witness `(a, b, c, M, N)` and truncate at `0`:
`y = y₋ + y₀ + y₊` with `y₋, y₊` inheriting the witness verbatim
(`TrustworthyKedlaya.Truncation`) and `y₀` a constant.  The three parts admit UP
Artin-Schreier roots — `ArtinSchreierNeg`, algebraic closedness of `𝔽̄_p`, and
`ArtinSchreierPos` respectively — whose sum `x'` is a UP root of `X^p - X = y` by
additivity of the Frobenius.  Any other root `x` differs from `x'` by a fixed point
of the Frobenius, and those are the constants in `𝔽_p`: if `z^p = z` then the
coefficientwise Frobenius formula shows the support of `z` is invariant under
scaling by `p`, forcing its minimum to be `0`.

## Main statements

- `TrustworthyKedlaya.eq_single_zero_of_pow_char_eq_self`: fixed points of the
  Frobenius of `𝔽̄_p((t^ℚ))` are the constants (with value in `𝔽_p`).
- `TrustworthyKedlaya.UP.exists_artinSchreier_root_isUP`: every UP series has a
  UP Artin-Schreier root (the construction).
- `TrustworthyKedlaya.UP.isUP_of_artinSchreier_root`: the packaged closure
  statement.

## References

- K. S. Kedlaya, *The algebraic closure of the power series field in positive
  characteristic*, Proc. Amer. Math. Soc. 129 (2001) [Ked01a], proof of Lemma 4.
-/

@[expose] public section

namespace TrustworthyKedlaya

open HahnSeries

variable {p : ℕ} [hp : Fact (Nat.Prime p)]

/-- **Fixed points of the Frobenius of `𝔽̄_p((t^ℚ))` are constants**: if `z^p = z`
then `z` is the single term `z₀ t^0` (and `z₀^p = z₀`, i.e. `z₀ ∈ 𝔽_p`).  The
coefficientwise Frobenius formula makes the support invariant under scaling by `p`,
so a nonzero fixed point with the constant term removed would have a support minimum
`m` with both `m ≤ m/p` and `m ≤ p·m`, forcing `m = 0` — a contradiction. -/
theorem eq_single_zero_of_pow_char_eq_self {z : HahnSeries ℚ (𝔽ᵃ_[p])}
    (hz : z ^ p = z) : z = single (0 : ℚ) (z.coeff 0) := by
  have hcoeff : ∀ g : ℚ, z.coeff g = z.coeff (g / p) ^ p := by
    intro g
    conv_lhs => rw [← hz]
    exact coeff_pow_char z g
  -- the constant term is fixed by the Frobenius of the values
  have hfp0 : z.coeff 0 ^ p = z.coeff 0 := by
    conv_rhs => rw [hcoeff 0, zero_div]
  -- removing the constant term leaves another Frobenius fixed point
  set w := z - single (0 : ℚ) (z.coeff 0) with hw
  have hwfix : w ^ p = w := by
    rw [hw, sub_pow_char, hz, single_pow, mul_zero, hfp0]
  have hw0 : w.coeff 0 = 0 := by
    rw [hw, HahnSeries.coeff_sub, coeff_single_same, sub_self]
  have hwcoeff : ∀ g : ℚ, w.coeff g = w.coeff (g / p) ^ p := by
    intro g
    conv_lhs => rw [← hwfix]
    exact coeff_pow_char w g
  -- a nonzero remainder would have support minimum 0, contradicting `hw0`
  have hwzero : w = 0 := by
    by_contra hne
    have hp1 : (1 : ℚ) < (p : ℚ) := by exact_mod_cast hp.out.one_lt
    have hordc : w.coeff w.order ≠ 0 := fun h0 => hne (coeff_order_eq_zero.mp h0)
    -- `order ≤ order / p`
    have hdiv : w.order ≤ w.order / p := by
      refine order_le_of_coeff_ne_zero fun h0 => hordc ?_
      rw [hwcoeff w.order, h0, zero_pow hp.out.ne_zero]
    -- `order ≤ p * order`
    have hmul : w.order ≤ (p : ℚ) * w.order := by
      refine order_le_of_coeff_ne_zero fun h0 => ?_
      rw [hwcoeff ((p : ℚ) * w.order), mul_div_cancel_left₀ _ (by positivity : (p : ℚ) ≠ 0)]
        at h0
      exact hordc (pow_eq_zero_iff hp.out.ne_zero |>.mp h0)
    -- hence `order = 0`, contradicting `w.coeff 0 = 0`
    rw [le_div_iff₀ (by positivity : (0 : ℚ) < (p : ℚ))] at hdiv
    have h3 : ((p : ℚ) - 1) * w.order = 0 :=
      le_antisymm (by linarith) (by linarith)
    have horder : w.order = 0 :=
      (mul_eq_zero.mp h3).resolve_left (by linarith)
    exact hordc (by rw [horder]; exact hw0)
  exact sub_eq_zero.mp (hw ▸ hwzero)

namespace UP

variable (p : ℕ) [hp : Fact (Nat.Prime p)]

variable {p} in
/-- **Every UP series has a UP Artin-Schreier root** (the construction half of the
closure property): if `y` is uniformly periodic then `X^p - X = y` has a root in
`𝔽̄_p((t^ℚ))`, and one such root is uniformly periodic.  Truncate a witness of `y`
at `0` and take the three roots (`ArtinSchreierNeg`, constants, `ArtinSchreierPos`). -/
theorem exists_artinSchreier_root_isUP {y : HahnSeries ℚ (𝔽ᵃ_[p])} (hy : IsUP p y) :
    ∃ x : HahnSeries ℚ (𝔽ᵃ_[p]), x ^ p - x = y ∧ IsUP p x := by
  obtain ⟨a, b, c, M, N, hsupp, hper⟩ := isUP_iff_exists_sliceWitness.mp hy
  -- truncate the witness at `0`
  have hwneg : SliceWitness p (hahnRestrict (Set.Iio 0) y) a b c M N :=
    ⟨fun g hg => hsupp (support_hahnRestrict_subset _ y hg),
      fun m _ => isTwistPeriodic_slice_hahnRestrict_Iio hsupp hper m⟩
  have hwpos : SliceWitness p (hahnRestrict (Set.Ioi 0) y) a b c M N :=
    ⟨fun g hg => hsupp (support_hahnRestrict_subset _ y hg),
      fun m _ => isTwistPeriodic_slice_hahnRestrict_Ioi hsupp hper m⟩
  -- roots of the three truncated parts
  obtain ⟨xneg, hASneg, -, hUPneg, -⟩ := exists_artinSchreier_root_of_support_neg p
    (support_hahnRestrict_subset_set _ y) hwneg
  obtain ⟨xpos, hASpos, -, hUPpos, -⟩ := exists_artinSchreier_root_of_support_pos p
    (support_hahnRestrict_subset_set _ y) hwpos
  obtain ⟨μ, hμ⟩ := exists_artinSchreier_root (y.coeff 0)
  have hASμ : HahnSeries.single (0 : ℚ) μ ^ p - HahnSeries.single (0 : ℚ) μ
      = HahnSeries.single (0 : ℚ) (y.coeff 0) := by
    rw [single_pow, mul_zero, ← hμ]
    ext g
    rcases eq_or_ne g 0 with rfl | hg
    · simp
    · simp [HahnSeries.coeff_single_of_ne hg]
  -- their sum is a UP root of `X^p - X = y`
  refine ⟨xneg + HahnSeries.single (0 : ℚ) μ + xpos, ?_,
    (hUPneg.add (isUP_single_zero p μ)).add hUPpos⟩
  have hsplit : (xneg + HahnSeries.single (0 : ℚ) μ + xpos) ^ p
      - (xneg + HahnSeries.single (0 : ℚ) μ + xpos)
      = (xneg ^ p - xneg)
        + (HahnSeries.single (0 : ℚ) μ ^ p - HahnSeries.single (0 : ℚ) μ)
        + (xpos ^ p - xpos) := by
    rw [add_pow_char, add_pow_char]
    ring
  rw [hsplit, hASneg, hASμ, hASpos, ← hahnRestrict_tridecomp]

variable {p} in
/-- **UP is closed under Artin-Schreier roots**: if `y` is
uniformly periodic and `x^p - x = y`, then `x` is uniformly periodic.  `x` differs
from the constructed UP root by a Frobenius fixed point, i.e. an `𝔽_p`-constant. -/
theorem isUP_of_artinSchreier_root {x y : HahnSeries ℚ (𝔽ᵃ_[p])} (hy : IsUP p y)
    (hxy : x ^ p - x = y) : IsUP p x := by
  obtain ⟨x', hAS', hUP'⟩ := exists_artinSchreier_root_isUP hy
  -- any root differs from `x'` by a Frobenius fixed point, i.e. an `𝔽_p`-constant
  have hfix : (x - x') ^ p = x - x' := by
    have hx1 : x ^ p = y + x := by rw [← hxy]; ring
    have hx2 : x' ^ p = y + x' := by rw [← hAS']; ring
    rw [sub_pow_char, hx1, hx2]
    ring
  have hxeq : x = x' + HahnSeries.single (0 : ℚ) ((x - x').coeff 0) := by
    rw [← eq_single_zero_of_pow_char_eq_self hfix]
    ring
  rw [hxeq]
  exact hUP'.add (isUP_single_zero p _)

end UP

end TrustworthyKedlaya
