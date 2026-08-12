/-
Copyright (c) 2026 Shanwen Wang, Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import TrustworthyKedlaya.Digits

/-!
# Column addition of fractional digit expansions

Adding two canonical fractional base-`p` expansions columnwise produces a string `w`
with digits `≤ 2(p-1)`.  This file reduces such a `w` back to canonical form *column
by column*: the carry bit out of column `j` is read off the tail sum from column `j`
on (`carryBit`), the resulting digit is `r_j = w_j + ε_{j+1} - p·ε_j` (`carryDigit`),
and the values satisfy `κ + fracVal r = fracVal w` with `κ = ε_0 ∈ {0,1}` the integer
carry (`exists_carrySum`).

The zero-column case analysis is the engine of the no-carries-across-a-widening-gap
lemma of Kedlaya (2001a): a carry entering a zero column of the result propagates
out and pins the column of `w` to `p - 1` (`carryBit_propagate`); a zero column
emitting a carry consumes at least `p - 1` of the digit budget of `w`
(`le_apply_of_carryDigit_eq_zero`); and a zero column with no carries on either side
is a zero column of `w` (`apply_eq_zero_of_carryDigit_eq_zero`).

## Main statements

- `TrustworthyKedlaya.UP.carryTail` / `carryBit` / `carryDigit`: tail sums, carry
  bits, and result digits of the column reduction.
- `TrustworthyKedlaya.UP.carryDigit_add_eq`: the exact column identity
  `r_j + p·ε_j = w_j + ε_{j+1}`.
- `TrustworthyKedlaya.UP.exists_carrySum`: the packaged reduction, producing the
  canonical string `r` with `κ + fracVal r = fracVal w`.

## References

- K. S. Kedlaya, *The algebraic closure of the power series field in positive
  characteristic*, Proc. Amer. Math. Soc. 129 (2001) [Ked01a], proof of Theorem 8.
-/

@[expose] public section

namespace TrustworthyKedlaya.UP

open Finset

variable (p : ℕ) [hp : Fact (Nat.Prime p)]

/-! ### Tail sums -/

/-- The tail value `∑_{k ≥ j} w_k · p^{-(k+1)}` of a digit string from column `j` on. -/
def carryTail (w : ℕ →₀ ℕ) (j : ℕ) : ℚ :=
  ∑ k ∈ w.support.filter (fun k => j ≤ k), (w k : ℚ) * (p : ℚ) ^ (-(k + 1 : ℤ))

omit hp in
/-- The tail from column `0` is the full fractional value. -/
theorem carryTail_zero_eq (w : ℕ →₀ ℕ) : carryTail p w 0 = fracVal p w := by
  rw [carryTail, fracVal, Finsupp.sum,
    Finset.filter_true_of_mem fun _ _ => Nat.zero_le _]

omit hp in
theorem carryTail_nonneg (w : ℕ →₀ ℕ) (j : ℕ) : 0 ≤ carryTail p w j :=
  Finset.sum_nonneg fun _ _ =>
    mul_nonneg (Nat.cast_nonneg _) (zpow_nonneg (Nat.cast_nonneg _) _)

omit hp in
/-- Column identity: the tail from `j` is the digit at `j` plus the tail from `j+1`. -/
theorem carryTail_succ (w : ℕ →₀ ℕ) (j : ℕ) :
    carryTail p w j = (w j : ℚ) * (p : ℚ) ^ (-(j + 1 : ℤ)) + carryTail p w (j + 1) := by
  have hsplit : w.support.filter (fun k => j ≤ k)
      = w.support.filter (fun k => k = j) ∪ w.support.filter (fun k => j + 1 ≤ k) := by
    ext k
    by_cases hk : k ∈ w.support
    · simp only [mem_filter, mem_union, hk, true_and]
      omega
    · simp [hk]
  have hdisj : Disjoint (w.support.filter (fun k => k = j))
      (w.support.filter (fun k => j + 1 ≤ k)) := by
    rw [Finset.disjoint_left]
    intro k h1 h2
    rw [mem_filter] at h1 h2
    omega
  rw [carryTail, hsplit, Finset.sum_union hdisj, carryTail]
  congr 1
  rw [Finset.sum_filter, Finset.sum_ite_eq' w.support j
    (fun k => (w k : ℚ) * (p : ℚ) ^ (-(k + 1 : ℤ)))]
  by_cases hj : j ∈ w.support
  · rw [if_pos hj]
  · rw [if_neg hj, Finsupp.notMem_support_iff.mp hj]
    simp

omit hp in
/-- Beyond the support the tails vanish. -/
theorem carryTail_eq_zero (w : ℕ →₀ ℕ) {L j : ℕ} (hL : w.support ⊆ range L)
    (hj : L ≤ j) : carryTail p w j = 0 := by
  rw [carryTail]
  refine Finset.sum_eq_zero fun k hk => ?_
  rw [mem_filter] at hk
  exact absurd (mem_range.mp (hL hk.1)) (by omega)

/-- Tail sums of a string with digits `≤ 2(p-1)` stay below `2·p^{-j}`. -/
theorem carryTail_lt_two_mul (w : ℕ →₀ ℕ) (hw : ∀ i, w i ≤ 2 * p - 2) (j : ℕ) :
    carryTail p w j < 2 * (p : ℚ) ^ (-(j : ℤ)) := by
  obtain ⟨L, hL⟩ := w.support.exists_nat_subset_range
  have hp0 : (0 : ℚ) < (p : ℚ) := by exact_mod_cast hp.out.pos
  have hdig : ∀ i : ℕ, (w i : ℚ) ≤ 2 * (p : ℚ) - 2 := by
    intro i
    have h2p : (2 : ℕ) ≤ 2 * p := by have := hp.out.two_le; omega
    have h1 : (w i : ℚ) ≤ ((2 * p - 2 : ℕ) : ℚ) := by exact_mod_cast hw i
    have h2 : ((2 * p - 2 : ℕ) : ℚ) = 2 * (p : ℚ) - 2 := by
      push_cast [Nat.cast_sub h2p]
      ring
    rwa [h2] at h1
  have key : ∀ n j : ℕ, L ≤ j + n → carryTail p w j < 2 * (p : ℚ) ^ (-(j : ℤ)) := by
    intro n
    induction n with
    | zero =>
      intro j hj
      rw [carryTail_eq_zero p w hL (by omega)]
      have := zpow_pos hp0 (-(j : ℤ))
      linarith
    | succ n ih =>
      intro j hj
      by_cases hLj : L ≤ j
      · rw [carryTail_eq_zero p w hL hLj]
        have := zpow_pos hp0 (-(j : ℤ))
        linarith
      · have hstep := carryTail_succ p w j
        have htail := ih (j + 1) (by omega)
        have hq0 : (0 : ℚ) < (p : ℚ) ^ (-(j + 1 : ℤ)) := zpow_pos hp0 _
        have hzp : (p : ℚ) ^ (-(j : ℤ)) = (p : ℚ) ^ (-(j + 1 : ℤ)) * (p : ℚ) := by
          rw [← zpow_add_one₀ hp0.ne']
          congr 1
          ring
        have hcast : (-(↑(j + 1) : ℤ)) = -(j + 1 : ℤ) := by push_cast; ring
        rw [hcast] at htail
        have h5 : (w j : ℚ) * (p : ℚ) ^ (-(j + 1 : ℤ))
            ≤ (2 * (p : ℚ) - 2) * (p : ℚ) ^ (-(j + 1 : ℤ)) :=
          mul_le_mul_of_nonneg_right (hdig j) hq0.le
        rw [hstep, hzp]
        nlinarith [htail, h5, hq0]
  exact key L j (by omega)

/-! ### Carry bits -/

/-- The carry bit out of column `j`: `1` exactly when the tail from column `j` reaches
`p^{-j}`, so that the columns `≥ j` overflow into column `j - 1`.  `carryBit w 0` is
the integer carry of the whole string. -/
def carryBit (w : ℕ →₀ ℕ) (j : ℕ) : ℕ :=
  if (p : ℚ) ^ (-(j : ℤ)) ≤ carryTail p w j then 1 else 0

omit hp in
theorem carryBit_le_one (w : ℕ →₀ ℕ) (j : ℕ) : carryBit p w j ≤ 1 := by
  rw [carryBit]
  split <;> omega

omit hp in
/-- The lower remainder bound: the announced carry is really contained in the tail. -/
theorem carryBit_le (w : ℕ →₀ ℕ) (j : ℕ) :
    (carryBit p w j : ℚ) * (p : ℚ) ^ (-(j : ℤ)) ≤ carryTail p w j := by
  rw [carryBit]
  split_ifs with h
  · rwa [Nat.cast_one, one_mul]
  · rw [Nat.cast_zero, zero_mul]
    exact carryTail_nonneg p w j

/-- The upper remainder bound: after removing the carry, less than `p^{-j}` remains. -/
theorem lt_carryBit (w : ℕ →₀ ℕ) (hw : ∀ i, w i ≤ 2 * p - 2) (j : ℕ) :
    carryTail p w j < (carryBit p w j : ℚ) * (p : ℚ) ^ (-(j : ℤ)) + (p : ℚ) ^ (-(j : ℤ)) := by
  have h2 := carryTail_lt_two_mul p w hw j
  rw [carryBit]
  split_ifs with h
  · rw [Nat.cast_one, one_mul]
    linarith
  · push Not at h
    rw [Nat.cast_zero, zero_mul, zero_add]
    exact h

/-- No carry emerges from a column outside the support: the tail from an empty column
is too small to overflow. -/
theorem carryBit_eq_zero_of_notMem (w : ℕ →₀ ℕ) (hw : ∀ i, w i ≤ 2 * p - 2) {j : ℕ}
    (hj : j ∉ w.support) : carryBit p w j = 0 := by
  have hp0 : (0 : ℚ) < (p : ℚ) := by exact_mod_cast hp.out.pos
  have hq0 : (0 : ℚ) < (p : ℚ) ^ (-(j + 1 : ℤ)) := zpow_pos hp0 _
  have hzp : (p : ℚ) ^ (-(j : ℤ)) = (p : ℚ) ^ (-(j + 1 : ℤ)) * (p : ℚ) := by
    rw [← zpow_add_one₀ hp0.ne']
    congr 1
    ring
  have h2 := carryTail_lt_two_mul p w hw (j + 1)
  have hcast : (-(↑(j + 1) : ℤ)) = -(j + 1 : ℤ) := by push_cast; ring
  rw [hcast] at h2
  have hp2 : (2 : ℚ) ≤ (p : ℚ) := by exact_mod_cast hp.out.two_le
  rw [carryBit, if_neg]
  push Not
  rw [carryTail_succ, Finsupp.notMem_support_iff.mp hj, Nat.cast_zero, zero_mul,
    zero_add, hzp]
  nlinarith [h2, hq0, hp2]

/-! ### The column digits -/

/-- The result digit of column `j`: the column of `w` plus the incoming carry minus
`p` times the outgoing carry. -/
def carryDigit (w : ℕ →₀ ℕ) (j : ℕ) : ℕ :=
  w j + carryBit p w (j + 1) - p * carryBit p w j

/-- The two-sided column bound `p·ε_j ≤ w_j + ε_{j+1} < p·ε_j + p`: the outgoing
carry is forced by the column and the incoming carry, with a genuine digit left. -/
theorem carryBit_bounds (w : ℕ →₀ ℕ) (hw : ∀ i, w i ≤ 2 * p - 2) (j : ℕ) :
    p * carryBit p w j ≤ w j + carryBit p w (j + 1) ∧
      w j + carryBit p w (j + 1) < p * carryBit p w j + p := by
  have hp0 : (0 : ℚ) < (p : ℚ) := by exact_mod_cast hp.out.pos
  have hq0 : (0 : ℚ) < (p : ℚ) ^ (-(j + 1 : ℤ)) := zpow_pos hp0 _
  have hzp : (p : ℚ) ^ (-(j : ℤ)) = (p : ℚ) ^ (-(j + 1 : ℤ)) * (p : ℚ) := by
    rw [← zpow_add_one₀ hp0.ne']
    congr 1
    ring
  have hcast : (-(↑(j + 1) : ℤ)) = -(j + 1 : ℤ) := by push_cast; ring
  have hcol := carryTail_succ p w j
  have hlo := carryBit_le p w j
  have hhi := lt_carryBit p w hw j
  have hlo' := carryBit_le p w (j + 1)
  have hhi' := lt_carryBit p w hw (j + 1)
  rw [hcast] at hlo' hhi'
  rw [hzp] at hlo hhi
  -- lower bound: `p·ε_j < w_j + ε_{j+1} + 1` in ℚ
  have hA : ((p : ℚ) * carryBit p w j) * (p : ℚ) ^ (-(j + 1 : ℤ))
      < ((w j : ℚ) + carryBit p w (j + 1) + 1) * (p : ℚ) ^ (-(j + 1 : ℤ)) := by
    nlinarith [hcol, hlo, hhi']
  have hA' : (p : ℚ) * carryBit p w j < (w j : ℚ) + carryBit p w (j + 1) + 1 :=
    lt_of_mul_lt_mul_right (by linarith [hA]) hq0.le
  -- upper bound: `w_j + ε_{j+1} < p·ε_j + p` in ℚ
  have hB : ((w j : ℚ) + carryBit p w (j + 1)) * (p : ℚ) ^ (-(j + 1 : ℤ))
      < ((p : ℚ) * carryBit p w j + p) * (p : ℚ) ^ (-(j + 1 : ℤ)) := by
    nlinarith [hcol, hhi, hlo']
  have hB' : (w j : ℚ) + carryBit p w (j + 1) < (p : ℚ) * carryBit p w j + p :=
    lt_of_mul_lt_mul_right (by linarith [hB]) hq0.le
  constructor
  · have : (p * carryBit p w j : ℕ) < w j + carryBit p w (j + 1) + 1 := by
      exact_mod_cast hA'
    omega
  · exact_mod_cast hB'

/-- Column digits are digits. -/
theorem carryDigit_lt (w : ℕ →₀ ℕ) (hw : ∀ i, w i ≤ 2 * p - 2) (j : ℕ) :
    carryDigit p w j < p := by
  have h := carryBit_bounds p w hw j
  rw [carryDigit]
  omega

/-- The exact column identity `r_j + p·ε_j = w_j + ε_{j+1}` (subtraction-free form). -/
theorem carryDigit_add_eq (w : ℕ →₀ ℕ) (hw : ∀ i, w i ≤ 2 * p - 2) (j : ℕ) :
    carryDigit p w j + p * carryBit p w j = w j + carryBit p w (j + 1) := by
  have h := carryBit_bounds p w hw j
  rw [carryDigit]
  omega

/-- The column identity in values: the `j`-th result term telescopes the remainders. -/
theorem carryDigit_column (w : ℕ →₀ ℕ) (hw : ∀ i, w i ≤ 2 * p - 2) (j : ℕ) :
    (carryDigit p w j : ℚ) * (p : ℚ) ^ (-(j + 1 : ℤ))
      = (carryTail p w j - (carryBit p w j : ℚ) * (p : ℚ) ^ (-(j : ℤ)))
        - (carryTail p w (j + 1)
            - (carryBit p w (j + 1) : ℚ) * (p : ℚ) ^ (-(j + 1 : ℤ))) := by
  have hp0 : (0 : ℚ) < (p : ℚ) := by exact_mod_cast hp.out.pos
  have hzp : (p : ℚ) ^ (-(j : ℤ)) = (p : ℚ) ^ (-(j + 1 : ℤ)) * (p : ℚ) := by
    rw [← zpow_add_one₀ hp0.ne']
    congr 1
    ring
  have hcol := carryTail_succ p w j
  have hadd := carryDigit_add_eq p w hw j
  have hq : (carryDigit p w j : ℚ) + (p : ℚ) * carryBit p w j
      = (w j : ℚ) + carryBit p w (j + 1) := by
    exact_mod_cast congrArg (fun n : ℕ => (n : ℚ)) hadd
  have hqA : ((carryDigit p w j : ℚ) + (p : ℚ) * carryBit p w j) * (p : ℚ) ^ (-(j + 1 : ℤ))
      = ((w j : ℚ) + (carryBit p w (j + 1) : ℚ)) * (p : ℚ) ^ (-(j + 1 : ℤ)) := by
    rw [hq]
  rw [hzp, hcol]
  nlinarith [hqA]

/-- Beyond the support (of both the column and its right neighbour) the result digit
vanishes. -/
theorem carryDigit_eq_zero_of_notMem (w : ℕ →₀ ℕ) (hw : ∀ i, w i ≤ 2 * p - 2) {j : ℕ}
    (hj : j ∉ w.support) (hj1 : j + 1 ∉ w.support) : carryDigit p w j = 0 := by
  rw [carryDigit, carryBit_eq_zero_of_notMem p w hw hj,
    carryBit_eq_zero_of_notMem p w hw hj1, Finsupp.notMem_support_iff.mp hj]
  omega

/-! ### The zero-column case analysis

At a column `j` where the result digit `r_j = 0`, the column identity
`r_j + p·ε_j = w_j + ε_{j+1}` leaves three cases according to the carries: these are
the engine of the gap-confinement argument (`lem:digit-carry-gap`). -/

/-- A carry entering a zero column of the result propagates out, and pins the column
to `w_j = p - 1`. -/
theorem carryBit_propagate (w : ℕ →₀ ℕ) (hw : ∀ i, w i ≤ 2 * p - 2) {j : ℕ}
    (hr : carryDigit p w j = 0) (hin : carryBit p w (j + 1) = 1) :
    carryBit p w j = 1 ∧ w j = p - 1 := by
  have hid := carryDigit_add_eq p w hw j
  have hb := carryBit_le_one p w j
  have hp2 := hp.out.two_le
  rw [hr, hin] at hid
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hb with h0 | h1
  · rw [h0] at hid
    omega
  · rw [h1] at hid
    exact ⟨h1, by omega⟩

/-- A zero column of the result emitting a carry that did not come in from the right
consumes `w_j = p` of the digit budget. -/
theorem apply_eq_of_carryDigit_eq_zero (w : ℕ →₀ ℕ) (hw : ∀ i, w i ≤ 2 * p - 2) {j : ℕ}
    (hr : carryDigit p w j = 0) (hin : carryBit p w (j + 1) = 0)
    (hout : carryBit p w j = 1) : w j = p := by
  have hid := carryDigit_add_eq p w hw j
  rw [hr, hin, hout] at hid
  omega

/-- A zero column of the result emitting a carry consumes at least `p - 1` of the
digit budget of `w`, whichever way the incoming carry went. -/
theorem le_apply_of_carryDigit_eq_zero (w : ℕ →₀ ℕ) (hw : ∀ i, w i ≤ 2 * p - 2) {j : ℕ}
    (hr : carryDigit p w j = 0) (hout : carryBit p w j = 1) : p - 1 ≤ w j := by
  have hid := carryDigit_add_eq p w hw j
  have hb := carryBit_le_one p w (j + 1)
  rw [hr, hout] at hid
  omega

/-- A zero column of the result with no outgoing carry has no incoming carry and is a
zero column of `w`. -/
theorem apply_eq_zero_of_carryDigit_eq_zero (w : ℕ →₀ ℕ) (hw : ∀ i, w i ≤ 2 * p - 2)
    {j : ℕ} (hr : carryDigit p w j = 0) (hout : carryBit p w j = 0) :
    w j = 0 ∧ carryBit p w (j + 1) = 0 := by
  have hid := carryDigit_add_eq p w hw j
  rw [hr, hout] at hid
  omega

/-! ### The packaged column reduction -/

/-- **Column addition of digit strings** (`lem:carry-seq`): a string `w` of columns
`≤ 2(p-1)` — e.g. the columnwise sum of two canonical strings — reduces to a canonical
string `r` given columnwise by `carryDigit`, plus an integer carry
`κ = carryBit w 0 ∈ {0,1}`, with `κ + fracVal r = fracVal w`.  By
`eq_of_fracVal_eq`, `r` is *the* canonical expansion of `fracVal w - κ`. -/
theorem exists_carrySum (w : ℕ →₀ ℕ) (hw : ∀ i, w i ≤ 2 * p - 2) :
    ∃ r : ℕ →₀ ℕ, (∀ j, r j = carryDigit p w j) ∧ (∀ j, r j < p) ∧
      (carryBit p w 0 : ℚ) + fracVal p r = fracVal p w := by
  obtain ⟨L, hL⟩ := w.support.exists_nat_subset_range
  have hvanish : ∀ j : ℕ, carryDigit p w j ≠ 0 → j ∈ range L := by
    intro j hj
    rw [mem_range]
    by_contra hjL
    push Not at hjL
    refine hj (carryDigit_eq_zero_of_notMem p w hw ?_ ?_)
    · exact fun hmem => absurd (mem_range.mp (hL hmem)) (by omega)
    · exact fun hmem => absurd (mem_range.mp (hL hmem)) (by omega)
  refine ⟨Finsupp.onFinset (range L) (fun j => carryDigit p w j) hvanish,
    fun j => rfl, fun j => carryDigit_lt p w hw j, ?_⟩
  set r : ℕ →₀ ℕ := Finsupp.onFinset (range L) (fun j => carryDigit p w j) hvanish
    with hr
  have hrsupp : r.support ⊆ range L := Finsupp.support_onFinset_subset
  rw [fracVal_eq_sum_range p r hrsupp]
  set g : ℕ → ℚ :=
    fun j => carryTail p w j - (carryBit p w j : ℚ) * (p : ℚ) ^ (-(j : ℤ)) with hg
  have hterm : ∀ j ∈ range L, (r j : ℚ) * (p : ℚ) ^ (-(j + 1 : ℤ)) = g j - g (j + 1) := by
    intro j _
    have hcast : (-(↑(j + 1) : ℤ)) = -(j + 1 : ℤ) := by push_cast; ring
    rw [hg]
    simp only [hcast]
    exact carryDigit_column p w hw j
  rw [Finset.sum_congr rfl hterm, Finset.sum_range_sub' g L]
  have hbitL : carryBit p w L = 0 :=
    carryBit_eq_zero_of_notMem p w hw
      (fun hmem => absurd (mem_range.mp (hL hmem)) (by omega))
  have htailL : carryTail p w L = 0 := carryTail_eq_zero p w hL le_rfl
  have hg0 : g 0 = fracVal p w - (carryBit p w 0 : ℚ) := by
    rw [hg]
    simp only []
    rw [carryTail_zero_eq]
    norm_num
  have hgL : g L = 0 := by
    rw [hg]
    simp only []
    rw [hbitL, htailL]
    norm_num
  rw [hg0, hgL]
  ring


/-! ### Gap confinement

If the result digits vanish on a widening gap `[j, j+n)` and the total column sum of
`w` is bounded by `s < (K+1)(p-1)`, carries die out within the first `K` gap columns:
from `j+K` on, `w` is zero on the gap and no carry crosses.  This is the confinement
half of `lem:digit-carry-gap`. -/

/-- Carry bits propagate leftwards through a run of zero result digits: a carry at
gap column `d + m` forces carries at all gap columns down to `d`. -/
theorem carryBit_eq_one_of_gap (w : ℕ →₀ ℕ) (hw : ∀ i, w i ≤ 2 * p - 2) {j n : ℕ}
    (hgap : ∀ d, j ≤ d → d < j + n → carryDigit p w d = 0) :
    ∀ m d, j ≤ d → d + m < j + n → carryBit p w (d + m) = 1 → carryBit p w d = 1 := by
  intro m
  induction m with
  | zero => intro d _ _ h; simpa using h
  | succ m ih =>
    intro d hd hdm h1
    have hbit : carryBit p w (d + m) = 1 := by
      have hstep := carryBit_propagate p w hw
        (hgap (d + m) (by omega) (by omega)) (by rwa [show d + m + 1 = d + (m + 1) by ring])
      exact hstep.1
    exact ih d hd (by omega) hbit

/-- **Gap confinement**: suppose the result digits of the column reduction of `w`
vanish on the gap columns `[j, j+n)`, the total column sum of `w` is at most `s`, and
`s < (K+1)(p-1)` with `K < n`.  Then no carry crosses any column in `[j+K, j+n]`, and
the columns of `w` in `[j+K, j+n)` vanish outright. -/
theorem gap_confinement (w : ℕ →₀ ℕ) (hw : ∀ i, w i ≤ 2 * p - 2) {s K j n : ℕ}
    (hs : (w.sum fun _ v => v) ≤ s) (hK : s < (K + 1) * (p - 1))
    (hgap : ∀ d, j ≤ d → d < j + n → carryDigit p w d = 0) (hKn : K < n) :
    (∀ d, j + K ≤ d → d ≤ j + n → carryBit p w d = 0) ∧
      (∀ d, j + K ≤ d → d < j + n → w d = 0) := by
  -- the carry bit dies at column `j + K`, else `K+1` gap columns each eat `p-1`
  have hbitJK : carryBit p w (j + K) = 0 := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (carryBit_le_one p w (j + K)) with h0 | h1
    · exact h0
    exfalso
    have hall : ∀ d, j ≤ d → d ≤ j + K → carryBit p w d = 1 := by
      intro d hd hdK
      exact carryBit_eq_one_of_gap p w hw hgap (j + K - d) d hd (by omega)
        (by rw [show d + (j + K - d) = j + K by omega]; exact h1)
    have hbig : ∀ d ∈ Finset.Ico j (j + K + 1), p - 1 ≤ w d := by
      intro d hd
      rw [Finset.mem_Ico] at hd
      exact le_apply_of_carryDigit_eq_zero p w hw
        (hgap d hd.1 (by omega)) (hall d hd.1 (by omega))
    have hsum : ∑ d ∈ Finset.Ico j (j + K + 1), w d ≤ (w.sum fun _ v => v) := by
      rw [Finsupp.sum, ← Finset.sum_filter_ne_zero (Finset.Ico j (j + K + 1))]
      exact Finset.sum_le_sum_of_subset fun d hd =>
        Finsupp.mem_support_iff.mpr (Finset.mem_filter.mp hd).2
    have hlow : (K + 1) * (p - 1) ≤ ∑ d ∈ Finset.Ico j (j + K + 1), w d := by
      calc (K + 1) * (p - 1)
          = ∑ _d ∈ Finset.Ico j (j + K + 1), (p - 1) := by
            rw [Finset.sum_const, Nat.card_Ico, smul_eq_mul]
            congr 1
            omega
        _ ≤ ∑ d ∈ Finset.Ico j (j + K + 1), w d := Finset.sum_le_sum hbig
    omega
  -- rightward death: zero bit + zero result digit kill the column and the next bit
  have hfwd : ∀ m, j + K + m ≤ j + n → carryBit p w (j + K + m) = 0 := by
    intro m
    induction m with
    | zero => intro _; simpa using hbitJK
    | succ m ih =>
      intro h
      have hprev := ih (by omega)
      have hkill := apply_eq_zero_of_carryDigit_eq_zero p w hw
        (hgap (j + K + m) (by omega) (by omega)) hprev
      rw [show j + K + (m + 1) = j + K + m + 1 by ring]
      exact hkill.2
  refine ⟨fun d hd hdn => ?_, fun d hd hdn => ?_⟩
  · have := hfwd (d - (j + K)) (by omega)
    rwa [show j + K + (d - (j + K)) = d by omega] at this
  · have hbit : carryBit p w d = 0 := by
      have := hfwd (d - (j + K)) (by omega)
      rwa [show j + K + (d - (j + K)) = d by omega] at this
    exact (apply_eq_zero_of_carryDigit_eq_zero p w hw
      (hgap d (by omega) hdn) hbit).1

/-! ### The bridge from decompositions

A decomposition `fracVal u + fracVal v = κ + fracVal z` of a canonical target `z`
(with integer carry `κ`) is recognized by the column reduction: the reduced string of
`w = u + v` is exactly `z`, and the integer carry is exactly `κ`.  Together with
`gap_confinement` this pins the digits of `u` and `v` on the gap of a gapped target. -/

omit hp in
/-- Canonical digit strings have columnwise sum bounded by `2(p-1)`. -/
theorem add_apply_le (u v : ℕ →₀ ℕ) (hu : ∀ i, u i < p) (hv : ∀ i, v i < p) :
    ∀ i, (u + v) i ≤ 2 * p - 2 := by
  intro i
  have h1 := hu i
  have h2 := hv i
  simp only [Finsupp.add_apply]
  omega

/-- **The column reduction recognizes decompositions**: if `u`, `v` are canonical
strings with `fracVal u + fracVal v = κ + fracVal z` for a canonical string `z` and
an integer carry `κ ≤ 1`, then the column reduction of `w = u + v` returns exactly
the carry `κ` and the digits of `z`. -/
theorem carryDigit_eq_of_decomp {u v z : ℕ →₀ ℕ} {κ : ℕ} (hκ : κ ≤ 1)
    (hu : ∀ i, u i < p) (hv : ∀ i, v i < p) (hz : ∀ i, z i < p)
    (hval : fracVal p u + fracVal p v = (κ : ℚ) + fracVal p z) :
    carryBit p (u + v) 0 = κ ∧ ∀ d, carryDigit p (u + v) d = z d := by
  have hp1 : 1 < p := hp.out.one_lt
  have hw : ∀ i, (u + v) i ≤ 2 * p - 2 := add_apply_le p u v hu hv
  obtain ⟨r, hrdef, hrlt, hrval⟩ := exists_carrySum p (u + v) hw
  have hwval : fracVal p (u + v) = fracVal p u + fracVal p v := fracVal_add p u v
  -- the two integer carries agree
  have hbit : carryBit p (u + v) 0 = κ := by
    have h01 : carryBit p (u + v) 0 ≤ 1 := carryBit_le_one p (u + v) 0
    have hr1 : fracVal p r < 1 := fracVal_lt_one p hp1 hrlt
    have hz1 : fracVal p z < 1 := fracVal_lt_one p hp1 hz
    have hr0 : 0 ≤ fracVal p r := fracVal_nonneg p r
    have hz0 : 0 ≤ fracVal p z := fracVal_nonneg p z
    have hdiff : ((carryBit p (u + v) 0 : ℚ) - κ) = fracVal p z - fracVal p r := by
      rw [hwval, hval] at hrval
      linarith
    interval_cases h : carryBit p (u + v) 0 <;> interval_cases κ <;>
      first
      | rfl
      | (exfalso; norm_num at hdiff; linarith)
  -- hence the fractional values agree, and canonical strings are unique
  have hreq : r = z := by
    refine eq_of_fracVal_eq p hp1 hrlt hz ?_
    rw [hwval, hval, hbit] at hrval
    linarith
  exact ⟨hbit, fun d => by rw [← hrdef d, hreq]⟩

/-- **Decomposition components vanish on the tail of a gap**: if canonical strings
`u, v` of digit sums `≤ c₁, ≤ c₂` decompose a canonical target `z` whose digits
vanish on the gap columns `[j, j+n)` (with integer carry `κ ≤ 1`), then with
`s = c₁ + c₂` and `K = ⌊s/(p-1)⌋ < n`, both `u` and `v` vanish on the columns
`[j+K, j+n)`, and no carry of the column reduction crosses `[j+K, j+n]`. -/
theorem decomp_eq_zero_on_gap {u v z : ℕ →₀ ℕ} {κ c₁ c₂ j n : ℕ} (hκ : κ ≤ 1)
    (hu : ∀ i, u i < p) (hv : ∀ i, v i < p) (hz : ∀ i, z i < p)
    (hval : fracVal p u + fracVal p v = (κ : ℚ) + fracVal p z)
    (hc₁ : (u.sum fun _ v => v) ≤ c₁) (hc₂ : (v.sum fun _ v => v) ≤ c₂)
    (hgap : ∀ d, j ≤ d → d < j + n → z d = 0)
    (hKn : (c₁ + c₂) / (p - 1) < n) :
    (∀ d, j + (c₁ + c₂) / (p - 1) ≤ d → d < j + n → u d = 0 ∧ v d = 0) ∧
      ∀ d, j + (c₁ + c₂) / (p - 1) ≤ d → d ≤ j + n → carryBit p (u + v) d = 0 := by
  have hp1 : 1 < p := hp.out.one_lt
  set s := c₁ + c₂ with hs
  set K := s / (p - 1) with hKdef
  have hw : ∀ i, (u + v) i ≤ 2 * p - 2 := add_apply_le p u v hu hv
  obtain ⟨hbit0, hdig⟩ := carryDigit_eq_of_decomp p hκ hu hv hz hval
  have hgap' : ∀ d, j ≤ d → d < j + n → carryDigit p (u + v) d = 0 := by
    intro d h1 h2
    rw [hdig d]
    exact hgap d h1 h2
  have hsum : ((u + v).sum fun _ v => v) ≤ s := by
    rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)]
    omega
  have hK : s < (K + 1) * (p - 1) := by
    have hpos : 0 < p - 1 := by omega
    have h1 := Nat.div_add_mod s (p - 1)
    have h2 := Nat.mod_lt s hpos
    rw [hKdef]
    nlinarith [h1, h2]
  obtain ⟨hbits, hcols⟩ := gap_confinement p (u + v) hw hsum hK hgap' hKn
  refine ⟨fun d h1 h2 => ?_, hbits⟩
  have := hcols d h1 h2
  simp only [Finsupp.add_apply] at this
  omega

end TrustworthyKedlaya.UP
