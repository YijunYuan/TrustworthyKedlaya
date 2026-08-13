/-
Copyright (c) 2026 Shanwen Wang, Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import TrustworthyKedlaya.ShadowCalculus
public import TrustworthyKedlaya.RootMatching
public import Mathlib.RingTheory.HahnSeries.Valuation

/-!
# Shadowing the coefficients of a split polynomial

The shadow map `S : 𝔽̄_p((t^ℚ)) → 𝕃_[p]` is neither additive nor multiplicative, but its
carries are `p`-divisible.  This file transports that calculus from elements to the
coefficients of split polynomials (blueprint `lem:shadow-symmetric-congruence`): the
coefficients of `∏_{y ∈ Y}(X - S(y))` agree with the shadows of the coefficients of
`∏_{y ∈ Y}(X - y)` to depth `σ_{n-i}(W) + 1`, where `W` is the valuation multiset of
`Y` and `σ_j` the sum of the `j` smallest elements (encoded by minimal witnesses as in
`TrustworthyKedlaya.RootMatching`).

The `WithTop`-valued wrappers `le_val_shadow_mul_sub'`, `le_val_shadow_neg_add'`,
`le_val_shadow_add_sub'` restate the carry bounds of `ShadowCalculus` with `orderTop`
floors, absorbing the zero-series cases.

## References

- K. S. Kedlaya, *Power series and p-adic algebraic closures*, J. Number Theory 89
  (2001) [Ked01b], Section 3.
-/

@[expose] public section

namespace TrustworthyKedlaya.pAdicHahnSeries

open WittVector Polynomial HahnSeries

variable {p : ℕ} [hp : Fact (Nat.Prime p)]

/-- The shadow of the constant series `1` is `1`. -/
@[simp]
theorem shadow_one : shadow (1 : HahnSeries ℚ (𝔽ᵃ_[p])) = 1 := by
  rw [shadow_eq_mkLp]
  have h : LiftedPAdicHahnSeries.fromCoeff (p := p)
      (1 : HahnSeries ℚ (𝔽ᵃ_[p])).coeff (1 : HahnSeries ℚ (𝔽ᵃ_[p])).isPWO_support' = 1 := by
    apply HahnSeries.ext
    funext q
    change teichmuller p ((1 : HahnSeries ℚ (𝔽ᵃ_[p])).coeff q) = (1 : LiftedPAdicHahnSeries p).coeff q
    rw [HahnSeries.coeff_one, HahnSeries.coeff_one]
    split
    · exact map_one _
    · exact WittVector.teichmuller_zero p
  rw [h, map_one]

/-! ### `WithTop`-valued carry bounds -/

/-- Multiplication carry with `orderTop` floors:
`val (S(y·y') - S(y)·S(y')) ≥ orderTop y + orderTop y' + 1`. -/
theorem le_val_shadow_mul_sub' (y y' : HahnSeries ℚ (𝔽ᵃ_[p])) :
    y.orderTop + y'.orderTop + 1 ≤ val p (shadow (y * y') - shadow y * shadow y') := by
  by_cases hy : y = 0
  · simp [hy]
  by_cases hy' : y' = 0
  · simp [hy']
  obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.mp (orderTop_ne_top.mpr hy)
  obtain ⟨b, hb⟩ := WithTop.ne_top_iff_exists.mp (orderTop_ne_top.mpr hy')
  have h := le_val_shadow_mul_sub y y' a b
    (fun q hq => by
      rw [← WithTop.coe_le_coe (α := ℚ), ha]; exact orderTop_le_of_coeff_ne_zero hq)
    (fun q hq => by
      rw [← WithTop.coe_le_coe (α := ℚ), hb]; exact orderTop_le_of_coeff_ne_zero hq)
  rw [← ha, ← hb]
  calc ((a : WithTop ℚ)) + (b : WithTop ℚ) + 1
      = ((a + b + 1 : ℚ) : WithTop ℚ) := by norm_cast
    _ ≤ _ := h

/-- Negation carry with an `orderTop` floor:
`val (S(-y) + S(y)) ≥ orderTop y + 1`. -/
theorem le_val_shadow_neg_add' (y : HahnSeries ℚ (𝔽ᵃ_[p])) :
    y.orderTop + 1 ≤ val p (shadow (-y) + shadow y) := by
  by_cases hy : y = 0
  · simp [hy]
  obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.mp (orderTop_ne_top.mpr hy)
  have h := le_val_shadow_neg_add y a
    (fun q hq => by
      rw [← WithTop.coe_le_coe (α := ℚ), ha]; exact orderTop_le_of_coeff_ne_zero hq)
  rw [← ha]
  calc ((a : WithTop ℚ)) + 1 = ((a + 1 : ℚ) : WithTop ℚ) := by norm_cast
    _ ≤ _ := h

/-- Addition carry with `orderTop` floors:
`val (S(y+y') - S(y) - S(y')) ≥ min (orderTop y) (orderTop y') + 1`. -/
theorem le_val_shadow_add_sub' (y y' : HahnSeries ℚ (𝔽ᵃ_[p])) :
    min y.orderTop y'.orderTop + 1 ≤ val p (shadow (y + y') - shadow y - shadow y') := by
  rcases le_total y.orderTop y'.orderTop with hmin | hmin
  · rw [min_eq_left hmin]
    by_cases hy : y = 0
    · simp [hy]
    obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.mp (orderTop_ne_top.mpr hy)
    have h := le_val_shadow_add_sub y y' a
      (fun q hq _ => by
        rw [← WithTop.coe_le_coe (α := ℚ), ha]; exact orderTop_le_of_coeff_ne_zero hq)
    rw [← ha]
    calc ((a : WithTop ℚ)) + 1 = ((a + 1 : ℚ) : WithTop ℚ) := by norm_cast
      _ ≤ _ := h
  · rw [min_eq_right hmin]
    by_cases hy' : y' = 0
    · simp [hy']
    obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.mp (orderTop_ne_top.mpr hy')
    have h := le_val_shadow_add_sub y y' a
      (fun q _ hq => by
        rw [← WithTop.coe_le_coe (α := ℚ), ha]; exact orderTop_le_of_coeff_ne_zero hq)
    rw [← ha]
    calc ((a : WithTop ℚ)) + 1 = ((a + 1 : ℚ) : WithTop ℚ) := by norm_cast
      _ ≤ _ := h

end TrustworthyKedlaya.pAdicHahnSeries
