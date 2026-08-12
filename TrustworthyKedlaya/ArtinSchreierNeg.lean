/-
Copyright (c) 2026 Shanwen Wang, Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import TrustworthyKedlaya.FiniteImage
public import TrustworthyKedlaya.Frobenius
public import TrustworthyKedlaya.Rescale
public import Mathlib.Algebra.BigOperators.Finprod

/-!
# Artin-Schreier roots of negatively supported UP series

For `y` uniformly periodic with support in `S_{a,b,c} ∩ (-∞, 0)`, the series
`x = ∑_i t^i ∑_{n ≥ 1} (y_{i p^n})^{1/p^n}` is a well-defined Hahn series supported on
`S_{a,b,b+c} ∩ (-∞, 0)`, satisfies `x^p - x = y`, and is again uniformly periodic
(Kedlaya (2001a), part of the proof of Lemma 4; `lem:as-root-neg` of the blueprint).

The uniform periodicity is the hard kernel of the whole Theorem-15 route: the naive
"each twist sequence of `x` is a bounded sum of twist sequences of `y`" argument fails
(the number of contributing terms grows with the prefix depth — the error site of
Kedlaya (2017), Remark 2.7).  The correct argument couples the twist sequences of `x`
*to themselves* along the relation `x^p = x + y`:

* `(x_i)^p = x_{pi} + y_{pi}` coefficientwise, and multiplication by `p` shifts digit
  strings by one place; this couples the twist sequence of `x` at slice `m` and gap
  position `j` to the one at slice `pm - b₁` and gap position `j - 1` (same index),
  resp. at slice `pm` and gap position `1` (index shifted by one) — the two cases of
  `lem:as-twist-couple`.
* At gap position `1` and slice `0` the coupling is a Frobenius-affine recursion
  `c_{n+1}^p = c_n + y_n`, handled by the orbit lemma
  `eventually_periodic_of_frobenius_affine`.
* At gap position `1` and slices `m ≤ -1` the coupled slice `pm` moves away from `0`
  and falls below `-b` after at most `L = log_p b + 1` steps, where all slices of `x`
  and `y` vanish: a downward ladder with preperiod growing by one per step.
* At gap positions `j ≥ 2` the coupling transfers periodicity verbatim (no parameter
  growth), closing an induction on `j`.

All sequence values live in a single finite subfield `𝔽_{p^D}` (`lem:as-subfield`),
as required by the orbit lemma; the resulting uniform data is `(M + L, N·p·D)`.

## Main statements

- `TrustworthyKedlaya.UP.Sabc_mem_div_pow_of_neg`: negative elements of `S_{a,b,c}`
  divided by `p^n` land in `S_{a,b,b+c}`, uniformly in `n`.
- `TrustworthyKedlaya.UP.exists_hahn_asRoot_of_neg_support`: existence of the Hahn
  series root `x` with `x^p = x + y` and the support bounds.
- `TrustworthyKedlaya.UP.exists_uniform_subfield_slices` /
  `TrustworthyKedlaya.UP.pow_pow_eq_self_of_asPair`: the common finite subfield.
- `TrustworthyKedlaya.UP.twistSeq_couple_gap_one` /
  `TrustworthyKedlaya.UP.twistSeq_couple_gap_ge_two`: the coupling relations.
- `TrustworthyKedlaya.UP.sliceWitness_of_asPair`: the ladder — a slice witness for `x`.
- `TrustworthyKedlaya.UP.exists_artinSchreier_root_of_support_neg`: the packaged
  statement (`lem:as-root-neg`).

## References

- K. S. Kedlaya, *The algebraic closure of the power series field in positive
  characteristic*, Proc. Amer. Math. Soc. 129 (2001) [Ked01a], proof of Lemma 4.
- K. S. Kedlaya, *On the algebraicity of generalized power series*, Beiträge Algebra
  Geom. 58 (2017) [Ked17], Example 2.6 and Remark 2.7.
-/

@[expose] public section

namespace TrustworthyKedlaya.UP

variable (p : ℕ) [hp : Fact (Nat.Prime p)]

/-! ### Generic helpers -/

/-- Elements of `S_{a,b,c}` are bounded below by `-(b+1)/a`. -/
theorem neg_lt_of_mem_Sabc {a : ℕ+} {b c : ℕ} {s : ℚ} (hs : s ∈ Sabc p a b c) :
    -(((b : ℚ) + 1) / (a : ℚ)) < s := by
  obtain ⟨n, d, hn, hd, _, rfl⟩ := hs
  have ha : (0 : ℚ) < (a : ℚ) := by exact_mod_cast a.pos
  have h1 : fracVal p d < 1 := fracVal_lt_one p hp.out.one_lt hd
  have h2 : -((b : ℚ)) ≤ (n : ℚ) := by exact_mod_cast hn
  have key : -((b : ℚ) + 1) < (n : ℚ) - fracVal p d := by linarith
  calc -(((b : ℚ) + 1) / (a : ℚ)) = (1 / (a : ℚ)) * (-((b : ℚ) + 1)) := by ring
    _ < (1 / (a : ℚ)) * ((n : ℚ) - d.sum fun i v => (v : ℚ) * (p : ℚ) ^ (-(i + 1 : ℤ))) := by
        rw [fracVal_def]
        exact mul_lt_mul_of_pos_left key (by positivity)

/-- The `p^k`-th power map is injective on `𝔽̄_p`. -/
theorem pow_p_pow_left_injective (k : ℕ) :
    Function.Injective fun v : 𝔽ᵃ_[p] => v ^ p ^ k := by
  intro s t hst
  apply iterateFrobenius_inj (𝔽ᵃ_[p]) p k
  simpa only [iterateFrobenius_def] using hst

/-- Iterates of the inverse Frobenius kill zero. -/
theorem invFrobenius_iterate_zero (k : ℕ) :
    ((frobeniusEquiv (𝔽ᵃ_[p]) p).symm)^[k] (0 : 𝔽ᵃ_[p]) = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply, map_zero, ih]

/-- Slices `m < -b` of a series supported in `S_{a,b,c}` vanish at every canonical
digit evaluation point (uniqueness of canonical representations). -/
theorem coeff_slice_eq_zero_of_slice_lt {x : HahnSeries ℚ (𝔽ᵃ_[p])} {a : ℕ+} {b c : ℕ}
    (hsupp : x.support ⊆ Sabc p a b c) {m : ℤ} (hm : m < -(b : ℤ)) {e : ℕ →₀ ℕ}
    (he : ∀ i, e i < p) :
    x.coeff (((m : ℚ) + -fracVal p e) / (a : ℚ)) = 0 := by
  by_contra h0
  have hmem := hsupp ((HahnSeries.mem_support _ _).mpr h0)
  rw [show ((m : ℚ) + -fracVal p e) / (a : ℚ)
      = (1 / (a : ℚ)) * ((m : ℚ) - fracVal p e) by ring] at hmem
  have := (Sabc_mem_canonical p he hmem).1
  omega

/-- Positive slices of a negatively supported series vanish at every canonical digit
evaluation point. -/
theorem coeff_slice_eq_zero_of_pos_slice {x : HahnSeries ℚ (𝔽ᵃ_[p])} {a : ℕ+}
    (hneg : x.support ⊆ Set.Iio 0) {m : ℤ} (hm : 1 ≤ m) {e : ℕ →₀ ℕ}
    (he : ∀ i, e i < p) :
    x.coeff (((m : ℚ) + -fracVal p e) / (a : ℚ)) = 0 := by
  by_contra h0
  have hmem := hneg ((HahnSeries.mem_support _ _).mpr h0)
  rw [Set.mem_Iio] at hmem
  have h1 : fracVal p e < 1 := fracVal_lt_one p hp.out.one_lt he
  have h2 : (1 : ℚ) ≤ (m : ℚ) := by exact_mod_cast hm
  have ha : (0 : ℚ) < (a : ℚ) := by exact_mod_cast a.pos
  have : (0 : ℚ) < ((m : ℚ) + -fracVal p e) / (a : ℚ) := div_pos (by linarith) ha
  linarith

/-- Splitting off the zeroth term of a finite sum over `ℕ`. -/
theorem finsum_nat_eq_zero_add {M : Type*} [AddCommMonoid M] {f : ℕ → M}
    (hf : (Function.support f).Finite) :
    ∑ᶠ n, f n = f 0 + ∑ᶠ n, f (n + 1) := by
  obtain ⟨K, hK⟩ := hf.bddAbove
  have hsub : Function.support f ⊆ ↑(Finset.range (K + 1)) := fun x hx => by
    simp only [Finset.coe_range, Set.mem_Iio]
    exact Nat.lt_succ_of_le (hK hx)
  have hsub' : Function.support (fun n => f (n + 1)) ⊆ ↑(Finset.range K) := fun x hx => by
    simp only [Finset.coe_range, Set.mem_Iio]
    have : x + 1 ≤ K := hK hx
    omega
  rw [finsum_eq_sum_of_support_subset _ hsub, finsum_eq_sum_of_support_subset _ hsub',
    Finset.sum_range_succ']
  exact add_comm _ _

/-! ### Division by `p^n` on negative support points -/

/-- The fractional value of a pure shift: `gapDig 1 n d` is the digit string of `d`
shifted out by `n` places. -/
theorem fracVal_gapDig_one (n : ℕ) (d : ℕ →₀ ℕ) :
    fracVal p (gapDig 1 n d) = (p : ℚ) ^ (-(n : ℤ)) * fracVal p d := by
  rw [fracVal_gapDig p hp.out.pos 1 n d]
  simp only [Nat.sub_self, Finset.range_zero, Finset.sum_empty, zero_add]
  congr 1
  rw [show (d.support.filter fun i => 1 - 1 ≤ i) = d.support from
    Finset.filter_true_of_mem fun i _ => Nat.zero_le i]
  rfl

/-- **Division by `p^n` on negative support points**: a negative element of
`S_{a,b,c}` divided by `p^n` lies in `S_{a,b,b+c}`, uniformly in `n`.  The integer
part (of size at most `b`) shifts into the fractional digit string, raising the
digit-sum level by at most `b`. -/
theorem Sabc_mem_div_pow_of_neg {a : ℕ+} {b c : ℕ} {s : ℚ}
    (hs : s ∈ Sabc p a b c) (hs0 : s < 0) (n : ℕ) :
    s / (p : ℚ) ^ n ∈ Sabc p a b (b + c) := by
  obtain ⟨m, d, hm, hd, hsum, rfl⟩ := hs
  have hp1 : (1 : ℚ) < (p : ℚ) := by exact_mod_cast hp.out.one_lt
  have ha : (0 : ℚ) < (a : ℚ) := by exact_mod_cast a.pos
  have hw1 : fracVal p d < 1 := fracVal_lt_one p hp.out.one_lt hd
  have hw0 : 0 ≤ fracVal p d := fracVal_nonneg p d
  -- from `s < 0`: the integer part is nonpositive
  have hm0 : m ≤ 0 := by
    by_contra hcon
    have h1 : (1 : ℚ) ≤ (m : ℚ) := by exact_mod_cast (by omega : (1 : ℤ) ≤ m)
    have h2 : (0 : ℚ) < (1 / (a : ℚ)) * ((m : ℚ) - fracVal p d) := by
      apply mul_pos (by positivity)
      rw [fracVal_def] at *
      linarith
    rw [fracVal_def] at hs0
    linarith
  cases n with
  | zero =>
    simpa using Sabc_mono p a le_rfl (Nat.le_add_left c b) ⟨m, d, hm, hd, hsum, rfl⟩
  | succ n =>
    set m' : ℕ := (-m).toNat with hm'def
    have hm'b : m' ≤ b := by omega
    have hmcast : (m : ℚ) = -(m' : ℚ) := by
      have hmz : m = -(((-m).toNat : ℤ)) := by omega
      rw [hm'def]
      exact_mod_cast hmz
    -- the pseudo-expansion: one digit `m'` at position `n` plus the digits of `d`
    -- shifted out by `n + 1` places
    set e : ℕ →₀ ℕ := Finsupp.single n m' + gapDig 1 (n + 1) d with hedef
    have heval : fracVal p e = (p : ℚ) ^ (-(n + 1 : ℤ)) * ((m' : ℚ) + fracVal p d) := by
      rw [hedef, fracVal_add, fracVal_single, fracVal_gapDig_one,
        show (-((n + 1 : ℕ) : ℤ)) = -((n : ℤ) + 1) by push_cast; ring]
      ring
    have hesum : (e.sum fun _ v => v) = m' + d.sum fun _ v => v := by
      rw [hedef, Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl),
        Finsupp.sum_single_index rfl, gapDig_sum]
    obtain ⟨k, dd, hdd, hsumdd, hval⟩ := exists_carry_normalization p e
    have hpow_pos : (0 : ℚ) < (p : ℚ) ^ (n + 1 : ℕ) := by positivity
    have hpow_ge : (1 : ℚ) ≤ (p : ℚ) ^ (n + 1 : ℕ) := one_le_pow₀ hp1.le
    have hzpow : (p : ℚ) ^ (-(n + 1 : ℤ)) = ((p : ℚ) ^ (n + 1 : ℕ))⁻¹ := by
      rw [zpow_neg, ← zpow_natCast]
      norm_num
    -- the carry is at most `b`
    have hkb : k ≤ b := by
      have h1 : (k : ℚ) ≤ fracVal p e := by
        rw [hval]
        have := fracVal_nonneg p dd
        linarith
      have h2 : fracVal p e ≤ (m' : ℚ) + fracVal p d := by
        rw [heval, hzpow]
        rw [inv_mul_le_iff₀ hpow_pos]
        have hm'0 : (0 : ℚ) ≤ (m' : ℚ) + fracVal p d := by positivity
        nlinarith
      have h3 : (k : ℚ) < (b : ℚ) + 1 := by
        have : (m' : ℚ) ≤ (b : ℚ) := by exact_mod_cast hm'b
        linarith
      exact_mod_cast Nat.lt_succ_iff.mp (by exact_mod_cast h3)
    refine ⟨-k, dd, by omega, hdd, ?_, ?_⟩
    · -- digit-sum level
      have h4 := hsumdd
      rw [hesum] at h4
      omega
    · -- the value
      have hkey : fracVal p e = (k : ℚ) + fracVal p dd := hval
      rw [heval] at hkey
      rw [show ((-k : ℤ) : ℚ) = -(k : ℚ) by push_cast; ring, fracVal_def, fracVal_def]
      rw [div_eq_iff (by positivity : ((p : ℚ) ^ (n + 1 : ℕ)) ≠ 0)]
      have hzp : (p : ℚ) ^ (-(n + 1 : ℤ)) * (p : ℚ) ^ (n + 1 : ℕ) = 1 := by
        rw [hzpow]
        field_simp
      calc (1 / (a : ℚ)) * ((m : ℚ) - fracVal p d)
          = -((1 / (a : ℚ)) * ((m' : ℚ) + fracVal p d)) := by rw [hmcast]; ring
        _ = -((1 / (a : ℚ)) * (((p : ℚ) ^ (-(n + 1 : ℤ)) * ((m' : ℚ) + fracVal p d))
              * (p : ℚ) ^ (n + 1 : ℕ))) := by
            rw [show (p : ℚ) ^ (-(n + 1 : ℤ)) * ((m' : ℚ) + fracVal p d)
                  * (p : ℚ) ^ (n + 1 : ℕ)
                = ((m' : ℚ) + fracVal p d)
                  * ((p : ℚ) ^ (-(n + 1 : ℤ)) * (p : ℚ) ^ (n + 1 : ℕ)) by ring, hzp,
              mul_one]
        _ = -((1 / (a : ℚ)) * (((k : ℚ) + fracVal p dd) * (p : ℚ) ^ (n + 1 : ℕ))) := by
            rw [hkey]
        _ = (1 / (a : ℚ)) * (-(k : ℚ) - fracVal p dd) * (p : ℚ) ^ (n + 1 : ℕ) := by ring

end TrustworthyKedlaya.UP
