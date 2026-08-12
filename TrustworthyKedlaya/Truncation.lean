/-
Copyright (c) 2026 Shanwen Wang, Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import TrustworthyKedlaya.Frobenius
public import TrustworthyKedlaya.SupportSets

/-!
# Truncation at an integer point preserves UP

For a series with support data `(1, b, c)` — slice width `1` — truncation at the
integer point `0` keeps or discards each slice wholesale: for the slice at `m`, every
twist evaluation point `z` satisfies `z ∈ (-1, 0]`, so the sampled exponent `m + z`
lies in `(m - 1, m]`, which is entirely `< 0` for `m ≤ 0` (except the single point
`z = 0` of the slice `m = 0`, reachable only by the zero digit string, whose twist
sequences are constant) and entirely `> 0` for `m ≥ 1`.  Hence every twist sequence of
a slice of a truncation of `x` is a twist sequence of the corresponding slice of `x`,
or identically zero, or constant — and `(M, N)`-periodicity is inherited unchanged.

## Main statements

- `TrustworthyKedlaya.UP.isTwistPeriodic_slice_hahnRestrict_Iio` /
  `..._Ioi`: the slices of the truncations of `x` to exponents in `(-∞, 0)` resp.
  `(0, ∞)` inherit `(M, N)`-periodicity at level `c` from those of `x`, for *every*
  slice index `m : ℤ`.
- `TrustworthyKedlaya.UP.isUP_hahnRestrict_Iio` / `..._Ioi`: the packaged `IsUP`
  conclusions.
- `TrustworthyKedlaya.UP.isUP_single_zero`: the `{0}`-part `single 0 (x.coeff 0)` is
  UP (a special case of `isUP_of_support_int_div`).

Together with the decomposition `hahnRestrict_tridecomp` (at `θ = 0`) these give the
truncation step of Kedlaya (2001a), Lemma 4: `x = x_- + x_0 + x_+` with all three
parts UP.

## References

- K. S. Kedlaya, *The algebraic closure of the power series field in positive
  characteristic*, Proc. Amer. Math. Soc. 129 (2001) [Ked01a], proof of Lemma 4.
-/

@[expose] public section

namespace TrustworthyKedlaya.UP

variable (p : ℕ) [hp : Fact (Nat.Prime p)]

variable {p} in
/-- Twist sequences of any slice of the restriction of `x` to the negative exponents
are `(M, N)`-periodic at level `c`, given support data `(1, b, c)` for `x` with
`(M, N)`-periodic slices.  For `m ≤ 0` the twist points of the slice are sampled where
the restriction agrees with `x` (or, for the zero digit string, the sequence is
constant); for `m ≥ 1` they are sampled where the restriction vanishes. -/
theorem isTwistPeriodic_slice_hahnRestrict_Iio {x : HahnSeries ℚ (𝔽ᵃ_[p])} {b c : ℕ}
    {M N : ℕ+} (hsupp : x.support ⊆ Sabc p 1 b c)
    (hper : ∀ m : ℤ, -(b : ℤ) ≤ m →
      IsTwistPeriodic p (fun z => x.coeff (((m : ℚ) + z) / ((1 : ℕ+) : ℚ))) c M N)
    (m : ℤ) :
    IsTwistPeriodic p
      (fun z => (hahnRestrict (Set.Iio 0) x).coeff (((m : ℚ) + z) / ((1 : ℕ+) : ℚ)))
      c M N := by
  have hone : ((1 : ℕ+) : ℚ) = 1 := by norm_num
  have hall := isTwistPeriodic_slice_upgrade p hsupp hper c
  intro j dig hj hdig hsum n hn
  rcases eq_or_ne dig 0 with rfl | hdig0
  · simp [twistSeq]
  -- Nonzero digits: every twist point is `-w` with `0 < w < 1`.
  obtain ⟨i₁, hi₁⟩ : ∃ i₁, dig i₁ ≠ 0 := by
    by_contra h
    push Not at h
    exact hdig0 (Finsupp.ext h)
  have hsumpos : 0 < dig.sum fun _ v => v :=
    lt_of_lt_of_le (Nat.pos_of_ne_zero hi₁)
      (Finset.single_le_sum (f := fun i => dig i) (fun _ _ => Nat.zero_le _)
        (Finsupp.mem_support_iff.mpr hi₁))
  have hgd : ∀ n' : ℕ, (0 : ℚ) < fracVal p (gapDig j n' dig) := by
    intro n'
    refine fracVal_pos p hp.out.pos fun h0 => ?_
    have hs := gapDig_sum j n' dig
    rw [h0, Finsupp.sum_zero_index] at hs
    omega
  have hlt : ∀ n' : ℕ, fracVal p (gapDig j n' dig) < 1 := fun n' =>
    fracVal_lt_one p hp.out.one_lt (gapDig_lt p hdig hp.out.pos j n')
  simp only [twistSeq_eq_neg_fracVal_gapDig]
  rcases le_or_gt m 0 with hm | hm
  · -- `m ≤ 0`: the sampled exponents are `< 0`, where the restriction agrees with `x`.
    have hmem : ∀ n' : ℕ,
        ((m : ℚ) + -fracVal p (gapDig j n' dig)) / ((1 : ℕ+) : ℚ) ∈ Set.Iio 0 := by
      intro n'
      rw [hone, div_one, Set.mem_Iio]
      have h1 := hgd n'
      have hm' : (m : ℚ) ≤ 0 := by exact_mod_cast hm
      linarith
    rw [coeff_hahnRestrict_of_mem x (hmem _), coeff_hahnRestrict_of_mem x (hmem _)]
    have hx := hall m j dig hj hdig hsum n hn
    simpa only [twistSeq_eq_neg_fracVal_gapDig] using hx
  · -- `m ≥ 1`: the sampled exponents are `> 0`, where the restriction vanishes.
    have hmem : ∀ n' : ℕ,
        ((m : ℚ) + -fracVal p (gapDig j n' dig)) / ((1 : ℕ+) : ℚ) ∉ Set.Iio 0 := by
      intro n'
      rw [hone, div_one, Set.mem_Iio, not_lt]
      have h1 := hlt n'
      have hm' : (1 : ℚ) ≤ (m : ℚ) := by exact_mod_cast hm
      linarith
    rw [coeff_hahnRestrict_of_notMem x (hmem _), coeff_hahnRestrict_of_notMem x (hmem _)]

variable {p} in
/-- Twist sequences of any slice of the restriction of `x` to the positive exponents
are `(M, N)`-periodic at level `c`, given support data `(1, b, c)` for `x` with
`(M, N)`-periodic slices. -/
theorem isTwistPeriodic_slice_hahnRestrict_Ioi {x : HahnSeries ℚ (𝔽ᵃ_[p])} {b c : ℕ}
    {M N : ℕ+} (hsupp : x.support ⊆ Sabc p 1 b c)
    (hper : ∀ m : ℤ, -(b : ℤ) ≤ m →
      IsTwistPeriodic p (fun z => x.coeff (((m : ℚ) + z) / ((1 : ℕ+) : ℚ))) c M N)
    (m : ℤ) :
    IsTwistPeriodic p
      (fun z => (hahnRestrict (Set.Ioi 0) x).coeff (((m : ℚ) + z) / ((1 : ℕ+) : ℚ)))
      c M N := by
  have hone : ((1 : ℕ+) : ℚ) = 1 := by norm_num
  have hall := isTwistPeriodic_slice_upgrade p hsupp hper c
  intro j dig hj hdig hsum n hn
  rcases eq_or_ne dig 0 with rfl | hdig0
  · simp [twistSeq]
  obtain ⟨i₁, hi₁⟩ : ∃ i₁, dig i₁ ≠ 0 := by
    by_contra h
    push Not at h
    exact hdig0 (Finsupp.ext h)
  have hsumpos : 0 < dig.sum fun _ v => v :=
    lt_of_lt_of_le (Nat.pos_of_ne_zero hi₁)
      (Finset.single_le_sum (f := fun i => dig i) (fun _ _ => Nat.zero_le _)
        (Finsupp.mem_support_iff.mpr hi₁))
  have hgd : ∀ n' : ℕ, (0 : ℚ) < fracVal p (gapDig j n' dig) := by
    intro n'
    refine fracVal_pos p hp.out.pos fun h0 => ?_
    have hs := gapDig_sum j n' dig
    rw [h0, Finsupp.sum_zero_index] at hs
    omega
  have hlt : ∀ n' : ℕ, fracVal p (gapDig j n' dig) < 1 := fun n' =>
    fracVal_lt_one p hp.out.one_lt (gapDig_lt p hdig hp.out.pos j n')
  simp only [twistSeq_eq_neg_fracVal_gapDig]
  rcases le_or_gt m 0 with hm | hm
  · -- `m ≤ 0`: the sampled exponents are `< 0`, where the restriction vanishes.
    have hmem : ∀ n' : ℕ,
        ((m : ℚ) + -fracVal p (gapDig j n' dig)) / ((1 : ℕ+) : ℚ) ∉ Set.Ioi 0 := by
      intro n'
      rw [hone, div_one, Set.mem_Ioi, not_lt]
      have h1 := hgd n'
      have hm' : (m : ℚ) ≤ 0 := by exact_mod_cast hm
      linarith
    rw [coeff_hahnRestrict_of_notMem x (hmem _), coeff_hahnRestrict_of_notMem x (hmem _)]
  · -- `m ≥ 1`: the sampled exponents are `> 0`, where the restriction agrees with `x`.
    have hmem : ∀ n' : ℕ,
        ((m : ℚ) + -fracVal p (gapDig j n' dig)) / ((1 : ℕ+) : ℚ) ∈ Set.Ioi 0 := by
      intro n'
      rw [hone, div_one, Set.mem_Ioi]
      have h1 := hlt n'
      have hm' : (1 : ℚ) ≤ (m : ℚ) := by exact_mod_cast hm
      linarith
    rw [coeff_hahnRestrict_of_mem x (hmem _), coeff_hahnRestrict_of_mem x (hmem _)]
    have hx := hall m j dig hj hdig hsum n hn
    simpa only [twistSeq_eq_neg_fracVal_gapDig] using hx

variable {p} in
/-- **Truncation to the negative exponents preserves UP** (with the same data): if `x`
has support in `S_{1,b,c}` and `(M, N)`-periodic slices, so does its restriction to
exponents in `(-∞, 0)`; in particular that restriction is UP. -/
theorem isUP_hahnRestrict_Iio {x : HahnSeries ℚ (𝔽ᵃ_[p])} {b c : ℕ} {M N : ℕ+}
    (hsupp : x.support ⊆ Sabc p 1 b c)
    (hper : ∀ m : ℤ, -(b : ℤ) ≤ m →
      IsTwistPeriodic p (fun z => x.coeff (((m : ℚ) + z) / ((1 : ℕ+) : ℚ))) c M N) :
    IsUP p (hahnRestrict (Set.Iio 0) x) :=
  ⟨1, b, c, fun _ hg => hsupp (support_hahnRestrict_subset _ x hg), M, N,
    fun m _ => isTwistPeriodic_slice_hahnRestrict_Iio hsupp hper m⟩

variable {p} in
/-- **Truncation to the positive exponents preserves UP** (with the same data): if `x`
has support in `S_{1,b,c}` and `(M, N)`-periodic slices, so does its restriction to
exponents in `(0, ∞)`; in particular that restriction is UP. -/
theorem isUP_hahnRestrict_Ioi {x : HahnSeries ℚ (𝔽ᵃ_[p])} {b c : ℕ} {M N : ℕ+}
    (hsupp : x.support ⊆ Sabc p 1 b c)
    (hper : ∀ m : ℤ, -(b : ℤ) ≤ m →
      IsTwistPeriodic p (fun z => x.coeff (((m : ℚ) + z) / ((1 : ℕ+) : ℚ))) c M N) :
    IsUP p (hahnRestrict (Set.Ioi 0) x) :=
  ⟨1, b, c, fun _ hg => hsupp (support_hahnRestrict_subset _ x hg), M, N,
    fun m _ => isTwistPeriodic_slice_hahnRestrict_Ioi hsupp hper m⟩

/-- The `{0}`-part of the truncation, a constant single term, is UP. -/
theorem isUP_single_zero (r : 𝔽ᵃ_[p]) : IsUP p (HahnSeries.single (0 : ℚ) r) :=
  isUP_of_support_int_div 1 fun s hs =>
    ⟨0, by simpa using HahnSeries.support_single_subset hs⟩

end TrustworthyKedlaya.UP
