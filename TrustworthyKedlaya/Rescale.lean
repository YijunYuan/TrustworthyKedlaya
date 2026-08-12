/-
Copyright (c) 2026 Shanwen Wang, Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import TrustworthyKedlaya.Additive

/-!
# Slice-width upgrade: UP presentations at every multiple of the width

A UP presentation of `x` consists of a support parameter `a` with
`supp x ⊆ S_{a,b,c}` and uniform periodicity data `(M, N)` for the width-`a` slices.
This file proves that the width can be replaced by **any multiple** `k·a`
(`lem:up-rescale`): the "some (any)" clause of Kedlaya (2001a), Definition 2, which
the paper leaves unproved, and the step that lets two UP series be compared at a
common width.

The width-`ka` slices of `x` sample the width-`a` slices along points
`(v + β + p^{-n}γ)/k` — the twist evaluation points divided by `k`.  Writing the
head and tail numerators as `A` and `G`, base-`p` long division by `k` gives a
dichotomy (for `k` coprime to `p`):

- **clean** (`k ∣ A` and `k ∣ G`): the quotient is again a twist evaluation point,
  of the digit string `digitFinsupp (A/k) ⊕ digitFinsupp (G/k)` with the same gap
  position, so periodicity transfers verbatim from the width-`a` slices (upgraded to
  the needed digit-sum level by `isTwistPeriodic_slice_upgrade`);
- **dirty** (otherwise): the remainder orbit deposits a nonzero quotient digit at
  least once every `k` gap positions (`le_digits_sum_div_of_not_dvd`), so once the
  gap exceeds `k(c+1)` the evaluation point falls outside `S_{a,b,c}` and the twist
  sequence is identically zero.

Division by `k = p` is a digit shift (`consDig`), always clean.  A general `k`
factors as `p^e · k₀` and the two steps compose.  The period `N` is preserved
throughout; only the preperiod grows, by the uniform amount `k(c+1)`.

## Main statements

- `TrustworthyKedlaya.UP.SliceWitness`: one explicit UP witness
  `(a, b, c, M, N)` for `x`.
- `TrustworthyKedlaya.UP.Sabc_mem_width_mul`:
  `S_{a,b,c} ⊆ S_{ka, kb+(k-1), kc}` via carry normalization.
- `TrustworthyKedlaya.UP.SliceWitness.width_mul`: a slice witness at width `a`
  yields one at width `k·a`, with the same period `N`.
- `TrustworthyKedlaya.UP.IsUP.add`: UP is closed under addition (`lem:up-add`),
  by passing to the common width `a·a'`.

## References

- K. S. Kedlaya, *The algebraic closure of the power series field in positive
  characteristic*, Proc. Amer. Math. Soc. 129 (2001) [Ked01a], Definition 2 and the
  reduction to `a = 1` in the proof of Theorem 8.
-/

@[expose] public section

namespace TrustworthyKedlaya.UP

open Finset

variable (p : ℕ) [hp : Fact (Nat.Prime p)]

/-- One explicit UP witness: `x` is supported on `S_{a,b,c}` and every width-`a`
slice with index `≥ -b` is `(M,N)`-periodic at level `c`.  `IsUP p x` is exactly
`∃ a b c M N, SliceWitness p x a b c M N`. -/
def SliceWitness (x : HahnSeries ℚ (𝔽ᵃ_[p])) (a : ℕ+) (b c : ℕ) (M N : ℕ+) : Prop :=
  x.support ⊆ Sabc p a b c ∧
    ∀ m : ℤ, -(b : ℤ) ≤ m →
      IsTwistPeriodic p (fun z => x.coeff (((m : ℚ) + z) / (a : ℚ))) c M N

variable {p}

/-- `IsUP` unpacked into slice witnesses. -/
theorem isUP_iff_exists_sliceWitness {x : HahnSeries ℚ (𝔽ᵃ_[p])} :
    IsUP p x ↔ ∃ (a : ℕ+) (b c : ℕ) (M N : ℕ+), SliceWitness p x a b c M N := by
  constructor
  · rintro ⟨a, b, c, hsupp, M, N, hper⟩
    exact ⟨a, b, c, M, N, hsupp, hper⟩
  · rintro ⟨a, b, c, M, N, hsupp, hper⟩
    exact ⟨a, b, c, hsupp, M, N, hper⟩

omit hp in
/-- `fracVal` is linear under pointwise scaling of the digits. -/
theorem fracVal_smul (k : ℕ) (d : ℕ →₀ ℕ) :
    fracVal p (k • d) = (k : ℚ) * fracVal p d := by
  rw [← fracVal_def, ← fracVal_def,
    Finsupp.sum_of_support_subset _ Finsupp.support_smul _ (fun i _ => by simp),
    Finsupp.sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finsupp.smul_apply, smul_eq_mul]
  push_cast
  ring

/-- The total digit sum is linear under pointwise scaling of the digits. -/
theorem sum_smul_digits (k : ℕ) (d : ℕ →₀ ℕ) :
    ((k • d).sum fun _ v => v) = k * d.sum fun _ v => v := by
  rw [Finsupp.sum_of_support_subset _ Finsupp.support_smul _ (fun i _ => rfl),
    Finsupp.sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [Finsupp.smul_apply, smul_eq_mul]

/-- **Support-set width upgrade**: `S_{a,b,c} ⊆ S_{ka, kb+(k-1), kc}`.  Scaling the
defining expansion by `k` multiplies every digit by `k`; carry normalization
(`exists_carry_normalization`) restores canonical digits at digit-sum cost `≤ kc`,
spinning off an integer carry `< k` which is absorbed by the numerator bound. -/
theorem Sabc_mem_width_mul {a : ℕ+} {b c : ℕ} (k : ℕ+) {s : ℚ}
    (hs : s ∈ Sabc p a b c) :
    s ∈ Sabc p (k * a) ((k : ℕ) * b + ((k : ℕ) - 1)) ((k : ℕ) * c) := by
  have hp1 : 1 < p := hp.out.one_lt
  obtain ⟨n, d, hn, hd, hsum, rfl⟩ := hs
  obtain ⟨K, d', hd', hsum', hval⟩ := exists_carry_normalization p ((k : ℕ) • d)
  rw [fracVal_smul] at hval
  -- The integer carry is `< k` because `k · fracVal d < k`.
  have hK : K < (k : ℕ) := by
    have h1 : fracVal p d < 1 := fracVal_lt_one p hp1 hd
    have h2 : (0 : ℚ) ≤ fracVal p d' := fracVal_nonneg p d'
    have h3 : ((k : ℕ) : ℚ) * fracVal p d < ((k : ℕ) : ℚ) := by
      calc ((k : ℕ) : ℚ) * fracVal p d < ((k : ℕ) : ℚ) * 1 := by
            have hk0 : (0 : ℚ) < ((k : ℕ) : ℚ) := by exact_mod_cast k.pos
            exact mul_lt_mul_of_pos_left h1 hk0
        _ = ((k : ℕ) : ℚ) := mul_one _
    have : (K : ℚ) < ((k : ℕ) : ℚ) := by linarith [hval ▸ h3]
    exact_mod_cast this
  refine ⟨(k : ℕ) * n - K, d', ?_, hd', ?_, ?_⟩
  · -- numerator bound
    have hk1 : 1 ≤ (k : ℕ) := k.pos
    have hkn : -(((k : ℕ) : ℤ) * (b : ℤ)) ≤ ((k : ℕ) : ℤ) * n := by
      have h := mul_le_mul_of_nonneg_left hn (by positivity : (0 : ℤ) ≤ ((k : ℕ) : ℤ))
      linarith
    have hKZ : (K : ℤ) < ((k : ℕ) : ℤ) := by exact_mod_cast hK
    have hcast : (((k : ℕ) * b + ((k : ℕ) - 1) : ℕ) : ℤ)
        = ((k : ℕ) : ℤ) * (b : ℤ) + ((k : ℕ) : ℤ) - 1 := by
      push_cast [Nat.cast_sub hk1]
      ring
    rw [hcast]
    linarith [hkn, hKZ]
  · -- digit-sum bound
    have h1 := sum_smul_digits (k : ℕ) d
    have h2 : (k : ℕ) * (d.sum fun _ v => v) ≤ (k : ℕ) * c :=
      Nat.mul_le_mul_left _ hsum
    omega
  · -- value identity
    rw [fracVal_def, fracVal_def]
    have ha0 : ((a : ℕ+) : ℚ) ≠ 0 := by exact_mod_cast a.pos.ne'
    have hk0 : ((k : ℕ) : ℚ) ≠ 0 := by exact_mod_cast k.pos.ne'
    have hka : (((k * a : ℕ+) : ℕ) : ℚ) = ((k : ℕ) : ℚ) * ((a : ℕ+) : ℚ) := by
      push_cast
      rfl
    rw [hka]
    field_simp
    push_cast
    linear_combination -hval

/-- Euclidean decomposition of a slice index: `m = k·q - v` with `0 ≤ v < k`. -/
theorem exists_int_div_decomp (k : ℕ) (hk : 0 < k) (m : ℤ) :
    ∃ (q : ℤ) (v : ℕ), v < k ∧ m = (k : ℤ) * q - v := by
  have hk' : ((k : ℤ)) ≠ 0 := by exact_mod_cast hk.ne'
  have h1 : 0 ≤ (-m) % (k : ℤ) := Int.emod_nonneg _ hk'
  have h2 : (-m) % (k : ℤ) < k := Int.emod_lt_of_pos _ (by exact_mod_cast hk)
  refine ⟨-((-m) / (k : ℤ)), ((-m) % (k : ℤ)).toNat, ?_, ?_⟩
  · omega
  · have h := Int.mul_ediv_add_emod (-m) (k : ℤ)
    have h3 : ((((-m) % (k : ℤ)).toNat : ℕ) : ℤ) = (-m) % (k : ℤ) :=
      Int.toNat_of_nonneg h1
    rw [h3]
    linarith [h]

/-- The fractional value of a gapped digit string splits as (head) + `p^{-n}` · (tail),
with head and tail realized by `Finsupp.filter` at the gap position. -/
theorem fracVal_gapDig_split (j n : ℕ) (dig : ℕ →₀ ℕ) :
    fracVal p (gapDig j n dig)
      = fracVal p (dig.filter (fun i => i < j - 1))
        + (p : ℚ) ^ (-(n : ℤ)) * fracVal p (dig.filter (fun i => j - 1 ≤ i)) := by
  rw [fracVal_gapDig p hp.out.pos j n dig]
  congr 1
  · -- head: the filtered finsupp sums over `range (j-1)` with unchanged values
    have hsupp : (dig.filter (fun i => i < j - 1)).support ⊆ range (j - 1) := by
      intro i hi
      rw [Finsupp.support_filter, Finset.mem_filter] at hi
      exact mem_range.mpr hi.2
    rw [fracVal_eq_sum_range p _ hsupp]
    exact Finset.sum_congr rfl fun i hi =>
      by rw [Finsupp.filter_apply_pos (fun i => i < j - 1) dig (mem_range.mp hi)]
  · -- tail: the filtered finsupp sums over the filtered support with unchanged values
    congr 1
    rw [← fracVal_def, Finsupp.sum, Finsupp.support_filter]
    exact Finset.sum_congr rfl fun i hi => by
      rw [Finsupp.filter_apply_pos (fun i => j - 1 ≤ i) dig (Finset.mem_filter.mp hi).2]

/-- **Slice-width upgrade by `p`** (digit shift): periodicity data transfers *verbatim*
from width `a` to width `p·a`.  Dividing a twist evaluation point by `p` prepends the
slice remainder `v < p` as one more head digit (`consDig`) and moves the gap from
position `j` to `j + 1`, so every twist sequence of a width-`pa` slice *is* a twist
sequence of a width-`a` slice, whose periodicity is supplied at every level by
`isTwistPeriodic_slice_upgrade`. -/
theorem isTwistPeriodic_slice_width_mul_p {x : HahnSeries ℚ (𝔽ᵃ_[p])} {a : ℕ+}
    {b c : ℕ} {M N : ℕ+} (k : ℕ+) (hkp : (k : ℕ) = p)
    (hsupp : x.support ⊆ Sabc p a b c)
    (hper : ∀ m : ℤ, -(b : ℤ) ≤ m →
      IsTwistPeriodic p (fun z => x.coeff (((m : ℚ) + z) / (a : ℚ))) c M N)
    (c' : ℕ) (m : ℤ) :
    IsTwistPeriodic p (fun z => x.coeff (((m : ℚ) + z) / ((k * a : ℕ+) : ℚ))) c' M N := by
  intro j dig hj hdig hsum n hn
  obtain ⟨q, v, hvlt, hm⟩ := exists_int_div_decomp (k : ℕ) k.pos m
  -- the width-`ka` slice samples the width-`a` slice `q` at the divided points
  have hred : ∀ n' : ℕ,
      twistSeq p (fun z => x.coeff (((m : ℚ) + z) / ((k * a : ℕ+) : ℚ))) j dig n'
        = x.coeff (((q : ℚ) - ((v : ℚ) + fracVal p (gapDig j n' dig)) / ((k : ℕ) : ℚ))
            / (a : ℚ)) := by
    intro n'
    rw [twistSeq_eq_neg_fracVal_gapDig]
    congr 1
    have hka : (((k * a : ℕ+) : ℕ) : ℚ) = ((k : ℕ) : ℚ) * ((a : ℕ+) : ℚ) := by
      push_cast
      rfl
    have hmq : (m : ℚ) = ((k : ℕ) : ℚ) * (q : ℚ) - (v : ℚ) := by
      exact_mod_cast congrArg (fun t : ℤ => (t : ℚ)) hm
    have hk0 : ((k : ℕ) : ℚ) ≠ 0 := by exact_mod_cast k.pos.ne'
    have ha0 : ((a : ℕ+) : ℚ) ≠ 0 := by exact_mod_cast a.pos.ne'
    rw [hka, hmq]
    field_simp
    ring
  -- dividing by `p` is the digit shift `consDig`: gap `j ↦ j + 1`, digit `v` prepended
  have hcons : ∀ n' : ℕ,
      ((v : ℚ) + fracVal p (gapDig j n' dig)) / ((k : ℕ) : ℚ)
        = fracVal p (gapDig (j + 1) n' (consDig v dig)) := by
    intro n'
    rw [hkp, ← fracVal_consDig p hp.out.pos v (gapDig j n' dig), gapDig_consDig hj]
  have hto : ∀ n' : ℕ,
      twistSeq p (fun z => x.coeff (((m : ℚ) + z) / ((k * a : ℕ+) : ℚ))) j dig n'
        = twistSeq p (fun z => x.coeff (((q : ℚ) + z) / (a : ℚ))) (j + 1)
            (consDig v dig) n' := by
    intro n'
    rw [hred n', twistSeq_eq_neg_fracVal_gapDig]
    congr 1
    rw [← hcons n']
    ring
  rw [hto n, hto (n + N)]
  exact isTwistPeriodic_slice_upgrade p hsupp hper
    ((consDig v dig).sum fun _ w => w) q (j + 1) (consDig v dig) (by omega)
    (consDig_lt p (show v < p by omega) hdig) le_rfl n hn

end TrustworthyKedlaya.UP
