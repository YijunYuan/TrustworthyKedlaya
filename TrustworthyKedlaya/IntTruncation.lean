/-
Copyright (c) 2026 Shanwen Wang, Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import TrustworthyKedlaya.Truncation
public import TrustworthyKedlaya.Multiplicative
public import TrustworthyKedlaya.Rescale

/-!
# Truncation at an arbitrary integer point preserves UP

Truncation at the point `0` preserves UP (`TrustworthyKedlaya.Truncation`); this
file transports that statement to an arbitrary integer cutoff `θ` by conjugating
with the exponent shift `x ↦ t^{-θ}·x`.  Monomials with
integer exponents are UP, multiplication by them preserves UP
(`TrustworthyKedlaya.Multiplicative`), and restriction windows translate along
the shift, so
`x|_{(-∞,θ)} = t^θ·((t^{-θ}·x)|_{(-∞,0)})` is UP whenever `x` is; the
complementary restriction is the difference `x - x|_{(-∞,θ)}`.

## Main statements

- `TrustworthyKedlaya.UP.isUP_single_intCast`: integer-exponent monomials are UP.
- `TrustworthyKedlaya.UP.hahnRestrict_Iio_eq_single_mul`: the shift conjugation
  identity for restriction windows.
- `TrustworthyKedlaya.UP.IsUP.hahnRestrict_Iio_intCast` /
  `TrustworthyKedlaya.UP.IsUP.hahnRestrict_Ici_intCast`: truncations of a UP
  series below and at-or-above an integer point are UP.

## References

- K. S. Kedlaya, *The algebraic closure of the power series field in positive
  characteristic*, Proc. Amer. Math. Soc. 129 (2001) [Ked01a], proof of Lemma 4.
-/

@[expose] public section

namespace TrustworthyKedlaya.UP

variable (p : ℕ) [hp : Fact (Nat.Prime p)]

/-- Monomials with integer exponent are UP: the support is a single integer. -/
theorem isUP_single_intCast (θ : ℤ) (r : 𝔽ᵃ_[p]) :
    IsUP p (HahnSeries.single (θ : ℚ) r) :=
  isUP_of_support_int_div 1 fun s hs =>
    ⟨θ, by simpa using HahnSeries.support_single_subset hs⟩

variable {p}

/-- Restriction windows translate along multiplication by a monomial:
`x|_{(-∞,θ)} = t^θ·((t^{-θ}·x)|_{(-∞,0)})`. -/
theorem hahnRestrict_Iio_eq_single_mul (θ : ℚ) (x : HahnSeries ℚ (𝔽ᵃ_[p])) :
    hahnRestrict (Set.Iio θ) x
      = HahnSeries.single θ 1 *
        hahnRestrict (Set.Iio 0) (HahnSeries.single (-θ) 1 * x) := by
  ext q
  rw [HahnSeries.coeff_single_mul, one_mul]
  by_cases hq : q < θ
  · rw [coeff_hahnRestrict_of_mem x (Set.mem_Iio.mpr hq),
      coeff_hahnRestrict_of_mem _ (Set.mem_Iio.mpr (by linarith)),
      HahnSeries.coeff_single_mul, one_mul, sub_neg_eq_add, sub_add_cancel]
  · rw [coeff_hahnRestrict_of_notMem x (by simpa using hq),
      coeff_hahnRestrict_of_notMem _ (by simp [Set.mem_Iio]; linarith)]

/-- **Truncation below an arbitrary integer point preserves UP**. -/
theorem IsUP.hahnRestrict_Iio_intCast {x : HahnSeries ℚ (𝔽ᵃ_[p])} (hx : IsUP p x)
    (θ : ℤ) : IsUP p (hahnRestrict (Set.Iio (θ : ℚ)) x) := by
  rw [hahnRestrict_Iio_eq_single_mul]
  have hneg : IsUP p (HahnSeries.single (-(θ : ℚ)) (1 : 𝔽ᵃ_[p])) := by
    have h := isUP_single_intCast p (-θ) (1 : 𝔽ᵃ_[p])
    rwa [Int.cast_neg] at h
  obtain ⟨a, b, c, hs, M, N, hper⟩ := hneg.mul hx
  exact (isUP_single_intCast p θ 1).mul (isUP_hahnRestrict_Iio hs hper)

/-- **Truncation at-or-above an arbitrary integer point preserves UP**. -/
theorem IsUP.hahnRestrict_Ici_intCast {x : HahnSeries ℚ (𝔽ᵃ_[p])} (hx : IsUP p x)
    (θ : ℤ) : IsUP p (hahnRestrict (Set.Ici (θ : ℚ)) x) := by
  have hdecomp : hahnRestrict (Set.Ici (θ : ℚ)) x
      = x - hahnRestrict (Set.Iio (θ : ℚ)) x := by
    ext q
    rw [HahnSeries.coeff_sub]
    by_cases hq : (θ : ℚ) ≤ q
    · rw [coeff_hahnRestrict_of_mem x (Set.mem_Ici.mpr hq),
        coeff_hahnRestrict_of_notMem x (by simp [Set.mem_Iio]; linarith), sub_zero]
    · rw [coeff_hahnRestrict_of_notMem x (by simpa using hq),
        coeff_hahnRestrict_of_mem x (Set.mem_Iio.mpr (by linarith)), sub_self]
  rw [hdecomp]
  exact hx.sub (hx.hahnRestrict_Iio_intCast θ)

end TrustworthyKedlaya.UP
