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

/-- A twist term of a width-`ka` slice `m = kq - v` evaluates `x` at the width-`a`
slice `q`, at the twist evaluation point divided by `k` and shifted by `v`. -/
theorem twistSeq_slice_width_mul {x : HahnSeries ℚ (𝔽ᵃ_[p])} {a : ℕ+} (k : ℕ+)
    {m q : ℤ} {v : ℕ} (hm : m = ((k : ℕ) : ℤ) * q - v) (j : ℕ) (dig : ℕ →₀ ℕ)
    (n' : ℕ) :
    twistSeq p (fun z => x.coeff (((m : ℚ) + z) / ((k * a : ℕ+) : ℚ))) j dig n'
      = x.coeff (((q : ℚ) - ((v : ℚ) + fracVal p (gapDig j n' dig)) / ((k : ℕ) : ℚ))
          / (a : ℚ)) := by
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
  have hred : ∀ n' : ℕ,
      twistSeq p (fun z => x.coeff (((m : ℚ) + z) / ((k * a : ℕ+) : ℚ))) j dig n'
        = x.coeff (((q : ℚ) - ((v : ℚ) + fracVal p (gapDig j n' dig)) / ((k : ℕ) : ℚ))
            / (a : ℚ)) := fun n' => twistSeq_slice_width_mul k hm j dig n'
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

/-- **Slice-width upgrade by `k` coprime to `p`** (long division): the width-`ka`
slices of `x` remain uniformly periodic with the *same period* `N`, after growing the
preperiod by `k(c+1)`.  Each twist sequence of a width-`ka` slice samples a width-`a`
slice along the twist evaluation points divided by `k`; writing the head and tail
numerators of the digit string as `A` and `G`, either `k` divides both — then the
divided points form the twist family of the quotient digit string with the same gap,
and periodicity transfers from the width-`a` slice via
`isTwistPeriodic_slice_upgrade` — or the remainder orbit forces a digit sum `> c`
across the gap (`le_digits_sum_div_of_not_dvd`), the evaluation points leave
`S_{a,b,c}`, and the twist sequence vanishes identically beyond the new preperiod. -/
theorem isTwistPeriodic_slice_width_mul_coprime {x : HahnSeries ℚ (𝔽ᵃ_[p])} {a : ℕ+}
    {b c : ℕ} {M N : ℕ+} (k : ℕ+) (hcop : Nat.Coprime p k)
    (hsupp : x.support ⊆ Sabc p a b c)
    (hper : ∀ m : ℤ, -(b : ℤ) ≤ m →
      IsTwistPeriodic p (fun z => x.coeff (((m : ℚ) + z) / (a : ℚ))) c M N)
    (c' : ℕ) (m : ℤ) :
    IsTwistPeriodic p (fun z => x.coeff (((m : ℚ) + z) / ((k * a : ℕ+) : ℚ))) c'
      (M + ⟨(k : ℕ) * (c + 1), Nat.mul_pos k.pos (Nat.succ_pos c)⟩) N := by
  have hp1 : 1 < p := hp.out.one_lt
  have hp0 : 0 < p := hp.out.pos
  have hpQ0 : ((p : ℕ) : ℚ) ≠ 0 := by exact_mod_cast hp0.ne'
  have hk0 : ((k : ℕ) : ℚ) ≠ 0 := by exact_mod_cast k.pos.ne'
  intro j dig hj hdig hsum n hn
  have hn' : (M : ℕ) + (k : ℕ) * (c + 1) ≤ n := by exact_mod_cast hn
  obtain ⟨q, v, hvlt, hm⟩ := exists_int_div_decomp (k : ℕ) k.pos m
  -- window bound for the digit string
  obtain ⟨W, hWsupp, hjW⟩ : ∃ W : ℕ, dig.support ⊆ range W ∧ j - 1 ≤ W := by
    obtain ⟨W₀, hW₀⟩ := dig.support.exists_nat_subset_range
    refine ⟨max W₀ (j - 1), fun i hi => ?_, le_max_right _ _⟩
    rw [mem_range]
    have := mem_range.mp (hW₀ hi)
    omega
  -- head and tail of the digit string at the gap
  set dHead : ℕ →₀ ℕ := dig.filter (fun i => i < j - 1) with hdHead
  set dTail : ℕ →₀ ℕ := dig.filter (fun i => j - 1 ≤ i) with hdTail
  have hheadsupp : dHead.support ⊆ range (j - 1) := by
    intro i hi
    rw [hdHead, Finsupp.support_filter, Finset.mem_filter] at hi
    exact mem_range.mpr hi.2
  have htailsupp : dTail.support ⊆ range W := by
    intro i hi
    rw [hdTail, Finsupp.support_filter, Finset.mem_filter] at hi
    exact hWsupp hi.1
  have hheadlt : ∀ i, dHead i < p := by
    intro i
    rw [hdHead, Finsupp.filter_apply]
    split
    · exact hdig i
    · exact hp0
  have htaillt : ∀ i, dTail i < p := by
    intro i
    rw [hdTail, Finsupp.filter_apply]
    split
    · exact hdig i
    · exact hp0
  -- head numerator
  obtain ⟨B, hBval⟩ : ∃ B : ℕ, fracVal p dHead * (p : ℚ) ^ (j - 1) = (B : ℚ) :=
    ⟨_, fracVal_mul_pow p hp0 dHead hheadsupp⟩
  set A : ℕ := v * p ^ (j - 1) + B with hAdef
  -- tail numerator, with its size bound
  obtain ⟨G, hGlt, hGval⟩ : ∃ G : ℕ, G < p ^ (W - (j - 1)) ∧
      fracVal p dTail * (p : ℚ) ^ W = (G : ℚ) := by
    refine ⟨Nat.ofDigits p ((List.range W).map fun i => dTail (W - 1 - i)), ?_,
      fracVal_mul_pow p hp0 dTail htailsupp⟩
    set l : List ℕ := (List.range W).map fun i => dTail (W - 1 - i) with hldef
    have hllen : l.length = W := by rw [hldef]; simp
    have hgetD : ∀ i, i < W → l.getD i 0 = dTail (W - 1 - i) := by
      intro i hi
      rw [hldef]
      exact getD_range_map _ hi
    rw [ofDigits_eq_sum_getD p l (le_of_eq hllen)]
    have hsub : range (W - (j - 1)) ⊆ range W := by
      intro i hi
      rw [mem_range] at hi ⊢
      omega
    rw [← Finset.sum_subset hsub (fun i hi hni => by
      rw [mem_range] at hi hni
      rw [hgetD i hi, hdTail,
        Finsupp.filter_apply_neg (fun i' => j - 1 ≤ i') dig (by omega), zero_mul])]
    have hlist2 : ∀ y ∈ (List.range (W - (j - 1))).map (fun i => l.getD i 0), y < p := by
      intro y hy
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hy
      rw [List.mem_range] at hi
      rw [hgetD i (by omega)]
      exact htaillt _
    have hb := Nat.ofDigits_lt_base_pow_length hp1 hlist2
    rw [ofDigits_map_range] at hb
    simpa using hb
  -- head numerator in ℚ
  have hAcast : ((v : ℚ) + fracVal p dHead) * (p : ℚ) ^ (j - 1) = (A : ℚ) := by
    rw [hAdef]
    push_cast
    linear_combination hBval
  -- master numerator identity for the divided twist points
  have hu : ∀ n' : ℕ, ((v : ℚ) + fracVal p (gapDig j n' dig)) * (p : ℚ) ^ (W + n')
      = (A : ℚ) * (p : ℚ) ^ ((W - (j - 1)) + n') + (G : ℚ) := by
    intro n'
    rw [fracVal_gapDig_split j n' dig, ← hdHead, ← hdTail]
    have e1 : (p : ℚ) ^ (W + n') = (p : ℚ) ^ (j - 1) * (p : ℚ) ^ ((W - (j - 1)) + n') := by
      rw [← pow_add]
      congr 1
      omega
    have e2 : (p : ℚ) ^ (-(n' : ℤ)) * (p : ℚ) ^ (W + n') = (p : ℚ) ^ W := by
      rw [← zpow_natCast (p : ℚ) (W + n'), ← zpow_add₀ hpQ0, ← zpow_natCast (p : ℚ) W]
      congr 1
      push_cast
      ring
    linear_combination ((p : ℚ) ^ ((W - (j - 1)) + n')) * hAcast + hGval
      + ((v : ℚ) + fracVal p dHead) * e1 + (fracVal p dTail) * e2
  -- the divided twist points lie in `[0, 1)`
  have hu01 : ∀ n' : ℕ,
      0 ≤ ((v : ℚ) + fracVal p (gapDig j n' dig)) / ((k : ℕ) : ℚ)
        ∧ ((v : ℚ) + fracVal p (gapDig j n' dig)) / ((k : ℕ) : ℚ) < 1 := by
    intro n'
    have h1 : (0 : ℚ) ≤ fracVal p (gapDig j n' dig) := fracVal_nonneg p _
    have h2 : fracVal p (gapDig j n' dig) < 1 :=
      fracVal_lt_one p hp1 (gapDig_lt p hdig hp0 j n')
    have hkpos : (0 : ℚ) < ((k : ℕ) : ℚ) := by exact_mod_cast k.pos
    have hv1 : (v : ℚ) + 1 ≤ ((k : ℕ) : ℚ) := by exact_mod_cast hvlt
    refine ⟨div_nonneg (by positivity) hkpos.le, (div_lt_one hkpos).mpr (by linarith)⟩
  -- dirty case: beyond the new preperiod the slice values vanish
  have hvanish : ∀ n' : ℕ, ¬((k : ℕ) ∣ A ∧ (k : ℕ) ∣ G) → (k : ℕ) * (c + 1) ≤ n' →
      x.coeff (((q : ℚ) - ((v : ℚ) + fracVal p (gapDig j n' dig)) / ((k : ℕ) : ℚ))
        / (a : ℚ)) = 0 := by
    intro n' hnc hn''
    obtain ⟨hu0, hu1⟩ := hu01 n'
    by_contra hne
    have hmem := hsupp (HahnSeries.mem_support _ _ |>.mpr hne)
    obtain ⟨n₀, e, hn₀, helt, hesum, heq⟩ := hmem
    rw [fracVal_def] at heq
    have ha0 : ((a : ℕ+) : ℚ) ≠ 0 := by exact_mod_cast a.pos.ne'
    have heq3 : (q : ℚ) - ((v : ℚ) + fracVal p (gapDig j n' dig)) / ((k : ℕ) : ℚ)
        = (n₀ : ℚ) - fracVal p e := by
      calc (q : ℚ) - ((v : ℚ) + fracVal p (gapDig j n' dig)) / ((k : ℕ) : ℚ)
          = ((a : ℕ+) : ℚ) * (((q : ℚ) - ((v : ℚ) + fracVal p (gapDig j n' dig))
              / ((k : ℕ) : ℚ)) / ((a : ℕ+) : ℚ)) := by field_simp
        _ = ((a : ℕ+) : ℚ) * (1 / ((a : ℕ+) : ℚ) * ((n₀ : ℚ) - fracVal p e)) := by
            rw [heq]
        _ = (n₀ : ℚ) - fracVal p e := by field_simp
    -- integer and fractional parts match separately
    have h2 : (0 : ℚ) ≤ fracVal p e := fracVal_nonneg p e
    have h3 : fracVal p e < 1 := fracVal_lt_one p hp1 helt
    have h4 : ((q - n₀ : ℤ) : ℚ)
        = ((v : ℚ) + fracVal p (gapDig j n' dig)) / ((k : ℕ) : ℚ) - fracVal p e := by
      push_cast
      linarith
    have h5 : q = n₀ := by
      have habs : |((q - n₀ : ℤ) : ℚ)| < 1 := by
        rw [h4, abs_lt]
        exact ⟨by linarith, by linarith⟩
      have habs' : |q - n₀| < 1 := by exact_mod_cast habs
      rw [abs_lt] at habs'
      omega
    have hfrac : ((v : ℚ) + fracVal p (gapDig j n' dig)) / ((k : ℕ) : ℚ)
        = fracVal p e := by
      have h5' : (q : ℚ) = (n₀ : ℚ) := by exact_mod_cast h5
      linarith
    -- clear denominators: the all-ℕ master equation
    obtain ⟨L, hLsupp⟩ := e.support.exists_nat_subset_range
    have hDval := fracVal_mul_pow p hp0 e hLsupp
    set D : ℕ := Nat.ofDigits p ((List.range L).map fun i => e (L - 1 - i)) with hDdef
    have h6 : (v : ℚ) + fracVal p (gapDig j n' dig) = ((k : ℕ) : ℚ) * fracVal p e := by
      rw [← hfrac]
      field_simp
    have hkey : (k : ℕ) * D * p ^ (W + n') = (A * p ^ ((W - (j - 1)) + n') + G) * p ^ L := by
      have hkeyQ : (((k : ℕ) * D * p ^ (W + n') : ℕ) : ℚ)
          = (((A * p ^ ((W - (j - 1)) + n') + G) * p ^ L : ℕ) : ℚ) := by
        push_cast
        linear_combination (-(((k : ℕ) : ℚ)) * (p : ℚ) ^ (W + n')) * hDval
          + ((p : ℚ) ^ L) * (hu n')
          - ((p : ℚ) ^ L * (p : ℚ) ^ (W + n')) * h6
      exact_mod_cast hkeyQ
    have hdvdE : (k : ℕ) ∣ A * p ^ ((W - (j - 1)) + n') + G := by
      have h7 : (k : ℕ) ∣ (A * p ^ ((W - (j - 1)) + n') + G) * p ^ L :=
        ⟨D * p ^ (W + n'), by rw [← hkey]; ring⟩
      exact (Nat.Coprime.pow_right L hcop.symm).dvd_of_dvd_mul_right h7
    by_cases hkA : (k : ℕ) ∣ A
    · -- then `k ∣ G` too, contradicting the dirty hypothesis
      have h8 : (k : ℕ) ∣ A * p ^ ((W - (j - 1)) + n') := hkA.mul_right _
      exact hnc ⟨hkA, (Nat.dvd_add_right h8).mp hdvdE⟩
    · -- digit-sum growth beats the level bound `c`
      obtain ⟨E', hE'⟩ := hdvdE
      have hgrow := le_digits_sum_div_of_not_dvd p hp1 hcop hkA hGlt hn''
      have hEk : (A * p ^ ((W - (j - 1)) + n') + G) / (k : ℕ) = E' := by
        rw [hE']
        exact Nat.mul_div_cancel_left E' k.pos
      have h9 : E' * p ^ L = D * p ^ (W + n') := by
        refine Nat.eq_of_mul_eq_mul_left k.pos ?_
        calc (k : ℕ) * (E' * p ^ L) = ((k : ℕ) * E') * p ^ L := by ring
          _ = (A * p ^ ((W - (j - 1)) + n') + G) * p ^ L := by rw [← hE']
          _ = (k : ℕ) * D * p ^ (W + n') := hkey.symm
          _ = (k : ℕ) * (D * p ^ (W + n')) := by ring
      have h10 : (p.digits E').sum = (p.digits D).sum := by
        have h9' : p ^ L * E' = p ^ (W + n') * D := by
          rw [mul_comm (p ^ L) E', mul_comm (p ^ (W + n')) D]
          exact h9
        calc (p.digits E').sum = (p.digits (p ^ L * E')).sum :=
              (sum_digits_pow_mul p hp1 L E').symm
          _ = (p.digits (p ^ (W + n') * D)).sum := by rw [h9']
          _ = (p.digits D).sum := sum_digits_pow_mul p hp1 _ D
      have h11 : (p.digits D).sum ≤ (e.sum fun _ w => w) := by
        rw [hDdef]
        refine (sum_digits_ofDigits_le p _).trans (le_of_eq ?_)
        rw [← Nat.ofDigits_one, ofDigits_map_range 1]
        simp only [one_pow, mul_one]
        rw [Finset.sum_range_reflect]
        exact (Finsupp.sum_of_support_subset e hLsupp (fun _ w => w)
          (fun _ _ => rfl)).symm
      rw [hEk] at hgrow
      omega
  by_cases hclean : (k : ℕ) ∣ A ∧ (k : ℕ) ∣ G
  · -- clean case: divide the digit string by `k` and transfer periodicity
    obtain ⟨⟨A', hA'⟩, ⟨G', hG'⟩⟩ := hclean
    have hppos : (0 : ℚ) < (p : ℚ) ^ (j - 1) := by
      have : (0 : ℚ) < (p : ℚ) := by exact_mod_cast hp0
      positivity
    have hBlt : B < p ^ (j - 1) := by
      have h1 : fracVal p dHead < 1 := fracVal_lt_one p hp1 hheadlt
      have h2 : (B : ℚ) < (p : ℚ) ^ (j - 1) := by
        rw [← hBval]
        nlinarith [fracVal_nonneg p dHead]
      exact_mod_cast h2
    have hAlt : A < (k : ℕ) * p ^ (j - 1) := by
      rw [hAdef]
      calc v * p ^ (j - 1) + B < v * p ^ (j - 1) + p ^ (j - 1) := by omega
        _ = (v + 1) * p ^ (j - 1) := by ring
        _ ≤ (k : ℕ) * p ^ (j - 1) := Nat.mul_le_mul_right _ (by omega)
    have hA'lt : A' < p ^ (j - 1) := by
      have h := hAlt
      rw [hA'] at h
      exact Nat.lt_of_mul_lt_mul_left h
    have hG'lt : G' < p ^ (W - (j - 1)) := by
      have h : G' ≤ G := by
        rw [hG']
        exact Nat.le_mul_of_pos_left G' k.pos
      omega
    set dfA : ℕ →₀ ℕ := digitFinsupp p A' (j - 1) with hdfAdef
    set dfG : ℕ →₀ ℕ := digitFinsupp p G' W with hdfGdef
    set dig' : ℕ →₀ ℕ := dfA + dfG with hdig'def
    have hdfAsupp : dfA.support ⊆ range (j - 1) := digitFinsupp_support_subset p A' (j - 1)
    have hdfGsupp : dfG.support ⊆ Finset.Ico (j - 1) W :=
      digitFinsupp_support_subset_Ico p hp1 hG'lt
    have hdfGlow : ∀ i, i < j - 1 → dfG i = 0 := fun i hi =>
      Finsupp.notMem_support_iff.mp (fun hmem => by
        have h := hdfGsupp hmem
        rw [Finset.mem_Ico] at h
        omega)
    have hdfAhigh : ∀ i, j - 1 ≤ i → dfA i = 0 := fun i hi =>
      Finsupp.notMem_support_iff.mp (fun hmem => by
        have h := hdfAsupp hmem
        rw [mem_range] at h
        omega)
    have hdig'lt : ∀ i, dig' i < p := by
      intro i
      rw [hdig'def, Finsupp.add_apply]
      by_cases hij : i < j - 1
      · rw [hdfGlow i hij, add_zero, hdfAdef]
        exact digitFinsupp_lt p hp0 A' (j - 1) i
      · rw [hdfAhigh i (by omega), zero_add, hdfGdef]
        exact digitFinsupp_lt p hp0 G' W i
    have hfilA : dig'.filter (fun i => i < j - 1) = dfA := by
      ext i
      rw [Finsupp.filter_apply]
      split
      · rename_i hi
        rw [hdig'def, Finsupp.add_apply, hdfGlow i hi, add_zero]
      · rename_i hi
        exact (hdfAhigh i (by omega)).symm
    have hfilG : dig'.filter (fun i => j - 1 ≤ i) = dfG := by
      ext i
      rw [Finsupp.filter_apply]
      split
      · rename_i hi
        rw [hdig'def, Finsupp.add_apply, hdfAhigh i hi, zero_add]
      · rename_i hi
        exact (hdfGlow i (by omega)).symm
    have hdfAval : fracVal p dfA * (p : ℚ) ^ (j - 1) = (A' : ℚ) :=
      fracVal_digitFinsupp_mul_pow p hp1 hA'lt
    have hdfGval : fracVal p dfG * (p : ℚ) ^ W = (G' : ℚ) :=
      fracVal_digitFinsupp_mul_pow p hp1
        (lt_of_lt_of_le hG'lt (Nat.pow_le_pow_right hp0 (by omega)))
    have hh : (v : ℚ) + fracVal p dHead = ((k : ℕ) : ℚ) * fracVal p dfA := by
      have h1 : ((v : ℚ) + fracVal p dHead) * (p : ℚ) ^ (j - 1)
          = (((k : ℕ) : ℚ) * fracVal p dfA) * (p : ℚ) ^ (j - 1) := by
        rw [hAcast, mul_assoc, hdfAval]
        exact_mod_cast congrArg (Nat.cast : ℕ → ℚ) hA'
      exact mul_right_cancel₀ hppos.ne' h1
    have hPW : ((p : ℚ) ^ W) ≠ 0 := by positivity
    have ht : fracVal p dTail = ((k : ℕ) : ℚ) * fracVal p dfG := by
      have h1 : fracVal p dTail * (p : ℚ) ^ W
          = (((k : ℕ) : ℚ) * fracVal p dfG) * (p : ℚ) ^ W := by
        rw [hGval, mul_assoc, hdfGval]
        exact_mod_cast congrArg (Nat.cast : ℕ → ℚ) hG'
      exact mul_right_cancel₀ hPW h1
    have hclean_eq : ∀ n' : ℕ,
        ((v : ℚ) + fracVal p (gapDig j n' dig)) / ((k : ℕ) : ℚ)
          = fracVal p (gapDig j n' dig') := by
      intro n'
      rw [fracVal_gapDig_split j n' dig', hfilA, hfilG,
        fracVal_gapDig_split j n' dig, ← hdHead, ← hdTail]
      field_simp
      linear_combination hh + ((p : ℚ) ^ (-(n' : ℤ))) * ht
    have hto : ∀ n' : ℕ,
        twistSeq p (fun z => x.coeff (((m : ℚ) + z) / ((k * a : ℕ+) : ℚ))) j dig n'
          = twistSeq p (fun z => x.coeff (((q : ℚ) + z) / (a : ℚ))) j dig' n' := by
      intro n'
      rw [twistSeq_slice_width_mul k hm j dig n', twistSeq_eq_neg_fracVal_gapDig]
      congr 1
      rw [← hclean_eq n']
      ring
    rw [hto n, hto (n + N)]
    exact isTwistPeriodic_slice_upgrade p hsupp hper (dig'.sum fun _ w => w) q
      j dig' hj hdig'lt le_rfl n (by omega)
  · -- dirty case: both terms vanish beyond the preperiod
    rw [twistSeq_slice_width_mul k hm j dig n, twistSeq_slice_width_mul k hm j dig (n + N),
      hvanish n hclean (by omega), hvanish (n + N) hclean (by omega)]

end TrustworthyKedlaya.UP
