/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Miscellaneous helpers for the `p`-adic absolute value

This file collects small helper results used elsewhere in the development, most importantly the
monoid-with-zero homomorphism `WithZeroRat.toNNReal`. It sends the value group
`WithZero (Multiplicative ℚ)` of the `p`-adic valuation into `ℝ≥0`, which is what lets us turn the
`ℚ`-valued valuation on the field of `p`-adic Hahn series into a genuine `ℝ≥0`-valued absolute
value.

## Main definitions

- `WithZeroRat.toNNReal`: the map `WithZero (Multiplicative ℚ) →*₀ ℝ≥0` sending `0 ↦ 0` and
  `q ↦ e ^ q` for a fixed base `e`.

## Main statements

- `WithZeroRat.toNNReal_strictMono`: `toNNReal` is strictly monotone whenever `1 < e`.
-/

@[expose] public section

namespace WithZeroRat

open Multiplicative WithZero
open scoped NNReal

/-- Send `WithZero (Multiplicative ℚ)` to `ℝ≥0` by `0 ↦ 0` and `q ↦ e ^ q`. -/
noncomputable def toNNReal {e : ℝ≥0} (he : e ≠ 0) : WithZero (Multiplicative ℚ) →*₀ ℝ≥0 where
  toFun := fun x ↦ if hx : x = 0 then 0 else e ^ (((WithZero.unzero hx).toAdd : ℚ) : ℝ)
  map_zero' := by simp
  map_one' := by
    simp only [dif_neg one_ne_zero]
    have hunzero_one : WithZero.unzero (α := Multiplicative ℚ) one_ne_zero = 1 := by
      apply WithZero.coe_inj.mp
      rfl
    rw [hunzero_one, toAdd_one]
    simp
  map_mul' x y := by
    by_cases hxy : x * y = 0
    · rcases mul_eq_zero.mp hxy with hx | hy
      · simp [hx]
      · simp [hy]
    · obtain ⟨hx, hy⟩ := mul_ne_zero_iff.mp hxy
      suffices
          e ^ (((WithZero.unzero hxy).toAdd : ℚ) : ℝ) =
            e ^ (((WithZero.unzero hx).toAdd : ℚ) : ℝ) *
              e ^ (((WithZero.unzero hy).toAdd : ℚ) : ℝ) by
        simpa [hxy, hx, hy]
      rw [← NNReal.rpow_add he]
      congr 1
      rw [← Rat.cast_add]
      have hunzero_mul : WithZero.unzero hxy = WithZero.unzero hx * WithZero.unzero hy := by
        apply WithZero.coe_inj.mp
        simp [coe_unzero hx, coe_unzero hy, coe_unzero hxy]
      exact congrArg Rat.cast <| by
        simpa [toAdd_mul] using congrArg Multiplicative.toAdd hunzero_mul

/-- The map `toNNReal` is strictly monotone whenever `1 < e`. -/
theorem toNNReal_strictMono {e : ℝ≥0} (he : 1 < e) :
    StrictMono (toNNReal (ne_zero_of_lt he)) := by
  intro x y hxy
  simp only [toNNReal, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk]
  split_ifs with hx hy hy
  · simp only [hy, not_lt_zero] at hxy
  · exact NNReal.rpow_pos (zero_lt_one.trans he)
  · simp only [hy, not_lt_zero] at hxy
  · rw [← NNReal.coe_lt_coe, NNReal.coe_rpow, NNReal.coe_rpow,
      Real.rpow_lt_rpow_left_iff (by exact_mod_cast he : (1 : ℝ) < (e : ℝ))]
    rw [Rat.cast_lt, Multiplicative.toAdd_lt, ← WithZero.coe_lt_coe,
      coe_unzero hx, coe_unzero hy]
    exact hxy

end WithZeroRat

/-- The reciprocal `1 / p` of a prime `p` is nonzero in `ℝ≥0`. -/
@[simp]
lemma pInv_ne_zero (p : ℕ) [Fact (Nat.Prime p)] : (1 / (p : NNReal)) ≠ 0 := by
  simpa using NeZero.ne p

/-- A prime `p` is nonzero in `ℝ≥0`. -/
lemma p_ne_zero (p : ℕ) [Fact (Nat.Prime p)] : (p : NNReal) ≠ 0 := by
  simpa using NeZero.ne p
