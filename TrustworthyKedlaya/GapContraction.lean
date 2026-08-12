/-
Copyright (c) 2026 Shanwen Wang, Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import TrustworthyKedlaya.ColumnAddition
public import TrustworthyKedlaya.SupportSets

/-!
# No carries across a widening gap: the contraction bijection

Decompositions `fracVal u + fracVal v = κ + fracVal (gapDig j n b)` of a gapped
canonical target (Kedlaya (2001a), proof of Theorem 8) stabilize once the gap size
`n` reaches `n₀ = c₁ + c₂ + 1`, where `c₁, c₂` bound the digit sums of the two
components: the components vanish on the tail of the gap past
`i₀ = (j-1) + K`, `K = ⌊(c₁+c₂)/(p-1)⌋` (`decomp_gapDig_confine`, via
`decomp_eq_zero_on_gap`), so deleting the `n - n₀` zero columns at `i₀`
(`dropGapDig`) and re-inserting them (`gapDig`) are mutually inverse maps between
the decompositions at gap size `n` and those at gap size `n₀`
(`decomp_gapDig_contract` / `decomp_gapDig_expand`).  Matched components moreover
trace the twist family of their common full contraction with gap at `i₀` and index
shifted by `K` (`decomp_gapDig_component`), which is what makes twist sequences of
a product of two UP series into fixed finite sums of shifted products of twist
sequences of the factors.

The value bookkeeping runs through the tail sums of `ColumnAddition`: the
fractional value splits at any column as head window plus tail
(`fracVal_eq_sum_range_add_carryTail`), tails are additive (`carryTail_add`), and
above a column that no carry crosses, the tails of the components sum exactly to
the tail of the target (`decomp_carryTail_eq`, by telescoping the column
identity, `carryTail_reduced`).

## Main statements

- `TrustworthyKedlaya.UP.decomp_gapDig_confine`: components of a decomposition of
  the gapped target vanish on the gap past `i₀`, and no carry crosses there.
- `TrustworthyKedlaya.UP.decomp_gapDig_contract` /
  `TrustworthyKedlaya.UP.decomp_gapDig_expand`: deleting/inserting the zero run at
  `i₀` is a digit-sum-preserving bijection between decompositions at gap sizes
  `n ≥ n₀` and `n₀`.
- `TrustworthyKedlaya.UP.decomp_gapDig_component`: matched components are the
  gap-`i₀` twist family of their full contraction at index `n - K`.

## References

- K. S. Kedlaya, *The algebraic closure of the power series field in positive
  characteristic*, Proc. Amer. Math. Soc. 129 (2001) [Ked01a], proof of Theorem 8.
-/

@[expose] public section

namespace TrustworthyKedlaya.UP

open Finset

variable (p : ℕ) [hp : Fact (Nat.Prime p)]

/-! ### Round trips of the column surgery -/

omit hp in
/-- Deleting a freshly inserted zero run restores the original string. -/
theorem dropGapDig_gapDig (i₀ L : ℕ) (w : ℕ →₀ ℕ) :
    dropGapDig i₀ L (gapDig (i₀ + 1) L w) = w := by
  ext i
  rw [dropGapDig_apply]
  by_cases h : i < i₀
  · rw [if_pos h, gapDig_apply, Nat.add_sub_cancel, if_pos h]
  · rw [if_neg h, gapDig_apply, Nat.add_sub_cancel, if_neg (by omega),
      if_pos (by omega), Nat.add_sub_cancel]

omit hp in
/-- Consecutive deletions at the same position merge. -/
theorem dropGapDig_dropGapDig (i₀ L L' : ℕ) (e : ℕ →₀ ℕ) :
    dropGapDig i₀ L' (dropGapDig i₀ L e) = dropGapDig i₀ (L + L') e := by
  ext i
  simp only [dropGapDig_apply]
  by_cases h : i < i₀
  · rw [if_pos h, if_pos h, if_pos h]
  · rw [if_neg h, if_neg (by omega : ¬i + L' < i₀), if_neg h,
      show i + L' + L = i + (L + L') by omega]

/-! ### The tail-sum calculus -/

omit hp in
/-- Splitting the fractional value at a column: head window plus tail. -/
theorem fracVal_eq_sum_range_add_carryTail (w : ℕ →₀ ℕ) (D : ℕ) :
    fracVal p w
      = (∑ i ∈ range D, (w i : ℚ) * (p : ℚ) ^ (-(i + 1 : ℤ))) + carryTail p w D := by
  induction D with
  | zero => rw [Finset.range_zero, Finset.sum_empty, zero_add, carryTail_zero_eq]
  | succ D ih =>
    rw [ih, Finset.sum_range_succ, carryTail_succ]
    ring

omit hp in
/-- Tails are additive in the digit string. -/
theorem carryTail_add (u v : ℕ →₀ ℕ) (D : ℕ) :
    carryTail p (u + v) D = carryTail p u D + carryTail p v D := by
  have hu := fracVal_eq_sum_range_add_carryTail p u D
  have hv := fracVal_eq_sum_range_add_carryTail p v D
  have huv := fracVal_eq_sum_range_add_carryTail p (u + v) D
  rw [fracVal_add] at huv
  have hsum : ∑ i ∈ range D, ((u + v) i : ℚ) * (p : ℚ) ^ (-(i + 1 : ℤ))
      = (∑ i ∈ range D, (u i : ℚ) * (p : ℚ) ^ (-(i + 1 : ℤ)))
        + ∑ i ∈ range D, (v i : ℚ) * (p : ℚ) ^ (-(i + 1 : ℤ)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finsupp.add_apply]
    push_cast
    ring
  linarith [hu, hv, huv, hsum]

/-- Tail form of the column reduction: above any column `D`, the tail of `w` is the
tail of the reduced string plus the carry leaving column `D`. -/
theorem carryTail_reduced {w r : ℕ →₀ ℕ} (hw : ∀ i, w i ≤ 2 * p - 2)
    (hr : ∀ i, r i = carryDigit p w i) (D : ℕ) :
    carryTail p w D = carryTail p r D + (carryBit p w D : ℚ) * (p : ℚ) ^ (-(D : ℤ)) := by
  obtain ⟨L₀, hL₀⟩ := (w.support ∪ r.support).exists_nat_subset_range
  have hwL : w.support ⊆ range (max L₀ D) := fun k hk => mem_range.mpr
    (lt_of_lt_of_le (mem_range.mp (hL₀ (Finset.mem_union_left _ hk))) (le_max_left _ _))
  have hrL : r.support ⊆ range (max L₀ D) := fun k hk => mem_range.mpr
    (lt_of_lt_of_le (mem_range.mp (hL₀ (Finset.mem_union_right _ hk))) (le_max_left _ _))
  set L := max L₀ D with hLdef
  have hDL : D ≤ L := le_max_right _ _
  set g : ℕ → ℚ :=
    fun k => carryTail p w k - (carryBit p w k : ℚ) * (p : ℚ) ^ (-(k : ℤ)) with hg
  have h1 : carryTail p r D = ∑ k ∈ Finset.Ico D L, (r k : ℚ) * (p : ℚ) ^ (-(k + 1 : ℤ)) := by
    rw [carryTail]
    refine Finset.sum_subset (fun k hk => ?_) (fun k hk hnk => ?_)
    · rw [Finset.mem_filter] at hk
      exact Finset.mem_Ico.mpr ⟨hk.2, mem_range.mp (hrL hk.1)⟩
    · have h0 : r k = 0 := by
        by_contra h0
        exact hnk (Finset.mem_filter.mpr
          ⟨Finsupp.mem_support_iff.mpr h0, (Finset.mem_Ico.mp hk).1⟩)
      rw [h0, Nat.cast_zero, zero_mul]
  have hterm : ∀ k ∈ Finset.Ico D L,
      (r k : ℚ) * (p : ℚ) ^ (-(k + 1 : ℤ)) = g k - g (k + 1) := by
    intro k _
    have hcast : (-(↑(k + 1) : ℤ)) = -(k + 1 : ℤ) := by push_cast; ring
    rw [hr k, hg]
    simp only [hcast]
    exact carryDigit_column p w hw k
  rw [h1, Finset.sum_congr rfl hterm, Finset.sum_Ico_eq_sum_range]
  have htel : ∑ k ∈ range (L - D), (g (D + k) - g (D + k + 1)) = g D - g (D + (L - D)) :=
    Finset.sum_range_sub' (fun i => g (D + i)) (L - D)
  have hgL : g L = 0 := by
    rw [hg]
    simp only []
    rw [carryTail_eq_zero p w hwL le_rfl, carryBit_eq_zero_of_notMem p w hw
      (fun hmem => absurd (mem_range.mp (hwL hmem)) (by omega))]
    norm_num
  rw [htel, show D + (L - D) = L by omega, hgL, sub_zero]
  simp only [hg]
  ring

omit hp in
/-- The tail of a gap-inserted string at any column inside or at the end of the gap:
only the shifted tail survives, scaled by `p^{-n}`. -/
theorem carryTail_gapDig (hp0 : 0 < p) {j n D : ℕ} (b : ℕ →₀ ℕ) (hD1 : j - 1 ≤ D)
    (hD2 : D ≤ j - 1 + n) :
    carryTail p (gapDig j n b) D = (p : ℚ) ^ (-(n : ℤ)) * carryTail p b (j - 1) := by
  have hsplit := fracVal_eq_sum_range_add_carryTail p (gapDig j n b) D
  rw [fracVal_gapDig p hp0] at hsplit
  have hhead : ∑ i ∈ range D, ((gapDig j n b) i : ℚ) * (p : ℚ) ^ (-(i + 1 : ℤ))
      = ∑ i ∈ range (j - 1), (b i : ℚ) * (p : ℚ) ^ (-(i + 1 : ℤ)) := by
    have h0 : ∀ i ∈ range D, i ∉ range (j - 1) →
        ((gapDig j n b) i : ℚ) * (p : ℚ) ^ (-(i + 1 : ℤ)) = 0 := by
      intro i hi hni
      have h1 : ¬i < j - 1 := fun h => hni (mem_range.mpr h)
      have h2 : i < j - 1 + n := lt_of_lt_of_le (mem_range.mp hi) hD2
      rw [gapDig_apply, if_neg h1, if_neg (by omega), Nat.cast_zero, zero_mul]
    rw [← Finset.sum_subset
      (fun x hx => mem_range.mpr (lt_of_lt_of_le (mem_range.mp hx) hD1)) h0]
    exact Finset.sum_congr rfl fun i hi => by rw [gapDig_apply, if_pos (mem_range.mp hi)]
  have htails : carryTail p b (j - 1)
      = ∑ i ∈ b.support.filter (fun i => j - 1 ≤ i), (b i : ℚ) * (p : ℚ) ^ (-(i + 1 : ℤ)) :=
    rfl
  rw [htails]
  linarith [hsplit, hhead]

omit hp in
/-- Value of a zero-run insertion in terms of the base string: inserting `L` zero
columns at position `i₀` discounts the tail at `i₀` by `p^{-L}`. -/
theorem fracVal_gapDig_insert (hp0 : 0 < p) (i₀ L : ℕ) (w : ℕ →₀ ℕ) :
    fracVal p (gapDig (i₀ + 1) L w)
      = fracVal p w - (1 - (p : ℚ) ^ (-(L : ℤ))) * carryTail p w i₀ := by
  have h1 := fracVal_gapDig p hp0 (i₀ + 1) L w
  simp only [Nat.add_sub_cancel] at h1
  have h3 : (∑ i ∈ w.support.filter (fun i => i₀ ≤ i), (w i : ℚ) * (p : ℚ) ^ (-(i + 1 : ℤ)))
      = carryTail p w i₀ := rfl
  rw [h3] at h1
  have h2 := fracVal_eq_sum_range_add_carryTail p w i₀
  rw [h1]
  linear_combination -h2

/-! ### The tail identity of a decomposition -/

/-- **The tail identity at a no-carry column**: if canonical strings `u, v` decompose
a canonical target `z` (with integer carry `κ ≤ 1`) and no carry of the column
reduction of `u + v` leaves column `D`, then above `D` the tails of `u` and `v` sum
exactly to the tail of `z`. -/
theorem decomp_carryTail_eq {u v z : ℕ →₀ ℕ} {κ : ℕ} (hκ : κ ≤ 1)
    (hu : ∀ i, u i < p) (hv : ∀ i, v i < p) (hz : ∀ i, z i < p)
    (hval : fracVal p u + fracVal p v = (κ : ℚ) + fracVal p z)
    {D : ℕ} (hbit : carryBit p (u + v) D = 0) :
    carryTail p u D + carryTail p v D = carryTail p z D := by
  obtain ⟨-, hdig⟩ := carryDigit_eq_of_decomp p hκ hu hv hz hval
  have h := carryTail_reduced p (add_apply_le p u v hu hv) (fun i => (hdig i).symm) D
  rw [hbit, Nat.cast_zero, zero_mul, add_zero, carryTail_add] at h
  exact h

/-! ### The gapped-target decompositions

For the remaining statements fix levels `c₁, c₂`, the derived data
`K = (c₁+c₂)/(p-1)`, `n₀ = c₁+c₂+1`, a gap position `j` (in the `twistSeq`
convention: the gap block of `gapDig j n b` is `[j-1, j-1+n)`), and the split
column `i₀ = (j-1) + K`.  The parameters are taken as variables constrained by
defining equations so that statements and proofs stay readable. -/

/-- **Confinement** (Kedlaya (2001a), proof of Theorem 8): both components of a
decomposition of the gapped target vanish on the gap columns past `i₀ = (j-1)+K`,
and no carry of their column addition crosses `[i₀, (j-1)+n]`. -/
theorem decomp_gapDig_confine {b u v : ℕ →₀ ℕ} {κ c₁ c₂ j n K i₀ : ℕ} (hκ : κ ≤ 1)
    (hK : K = (c₁ + c₂) / (p - 1)) (hi₀ : i₀ = j - 1 + K) (hKn : K < n)
    (hb : ∀ i, b i < p) (hu : ∀ i, u i < p) (hv : ∀ i, v i < p)
    (hc₁ : (u.sum fun _ v => v) ≤ c₁) (hc₂ : (v.sum fun _ v => v) ≤ c₂)
    (hval : fracVal p u + fracVal p v = (κ : ℚ) + fracVal p (gapDig j n b)) :
    (∀ d, i₀ ≤ d → d < j - 1 + n → u d = 0 ∧ v d = 0) ∧
      ∀ d, i₀ ≤ d → d ≤ j - 1 + n → carryBit p (u + v) d = 0 := by
  subst hK hi₀
  exact decomp_eq_zero_on_gap p hκ hu hv (fun i => gapDig_lt p hb hp.out.pos j n i)
    hval hc₁ hc₂
    (fun d h1 h2 => by rw [gapDig_apply, if_neg (by omega), if_neg (by omega)]) hKn

/-- **Contraction across a widening gap** (Kedlaya (2001a), proof of Theorem 8):
for `n ≥ n₀ = c₁+c₂+1`, deleting the `L = n - n₀` zero columns at `i₀ = (j-1)+K`
turns a decomposition of the gapped target at gap size `n` into one at gap size
`n₀`, preserving digit sums; the original components are recovered by re-inserting
the zero run, so the map is a bijection onto the decompositions at `n₀`
(`decomp_gapDig_expand` with `dropGapDig_gapDig` supplies the inverse). -/
theorem decomp_gapDig_contract {b u v : ℕ →₀ ℕ} {κ c₁ c₂ j n K n₀ i₀ L : ℕ}
    (hκ : κ ≤ 1) (hK : K = (c₁ + c₂) / (p - 1)) (hn₀ : n₀ = c₁ + c₂ + 1)
    (hi₀ : i₀ = j - 1 + K) (hL : L = n - n₀) (hn : n₀ ≤ n)
    (hb : ∀ i, b i < p) (hu : ∀ i, u i < p) (hv : ∀ i, v i < p)
    (hc₁ : (u.sum fun _ v => v) ≤ c₁) (hc₂ : (v.sum fun _ v => v) ≤ c₂)
    (hval : fracVal p u + fracVal p v = (κ : ℚ) + fracVal p (gapDig j n b)) :
    gapDig (i₀ + 1) L (dropGapDig i₀ L u) = u ∧
      gapDig (i₀ + 1) L (dropGapDig i₀ L v) = v ∧
      ((dropGapDig i₀ L u).sum fun _ v => v) = (u.sum fun _ v => v) ∧
      ((dropGapDig i₀ L v).sum fun _ v => v) = (v.sum fun _ v => v) ∧
      fracVal p (dropGapDig i₀ L u) + fracVal p (dropGapDig i₀ L v)
        = (κ : ℚ) + fracVal p (gapDig j n₀ b) := by
  have hp0 := hp.out.pos
  have hpne : ((p : ℚ)) ≠ 0 := by exact_mod_cast hp0.ne'
  have hKle : K ≤ c₁ + c₂ := hK ▸ Nat.div_le_self _ _
  obtain ⟨hzero, hbits⟩ := decomp_gapDig_confine p hκ hK hi₀ (by omega) hb hu hv hc₁ hc₂ hval
  have hu0 : ∀ i, i₀ ≤ i → i < i₀ + L → u i = 0 :=
    fun i h1 h2 => (hzero i h1 (by omega)).1
  have hv0 : ∀ i, i₀ ≤ i → i < i₀ + L → v i = 0 :=
    fun i h1 h2 => (hzero i h1 (by omega)).2
  have hru : gapDig (i₀ + 1) L (dropGapDig i₀ L u) = u := gapDig_dropGapDig hu0
  have hrv : gapDig (i₀ + 1) L (dropGapDig i₀ L v) = v := gapDig_dropGapDig hv0
  have hsu : ((dropGapDig i₀ L u).sum fun _ v => v) = u.sum fun _ v => v := by
    conv_rhs => rw [← hru]
    rw [gapDig_sum]
  have hsv : ((dropGapDig i₀ L v).sum fun _ v => v) = v.sum fun _ v => v := by
    conv_rhs => rw [← hrv]
    rw [gapDig_sum]
  refine ⟨hru, hrv, hsu, hsv, ?_⟩
  -- the tail identity at the no-carry column `i₀ + L`
  have hbitD : carryBit p (u + v) (i₀ + L) = 0 := hbits (i₀ + L) (by omega) (by omega)
  have htw := decomp_carryTail_eq p hκ hu hv
    (fun i => gapDig_lt p hb hp0 j n i) hval hbitD
  have hTz : carryTail p (gapDig j n b) (i₀ + L)
      = (p : ℚ) ^ (-(n : ℤ)) * carryTail p b (j - 1) :=
    carryTail_gapDig p hp0 b (by omega) (by omega)
  -- tails of the components in terms of their contractions
  have hτu : carryTail p u (i₀ + L)
      = (p : ℚ) ^ (-(L : ℤ)) * carryTail p (dropGapDig i₀ L u) i₀ := by
    conv_lhs => rw [← hru]
    have h := carryTail_gapDig p hp0 (dropGapDig i₀ L u)
      (j := i₀ + 1) (n := L) (D := i₀ + L) (by omega) (by omega)
    simpa [Nat.add_sub_cancel] using h
  have hτv : carryTail p v (i₀ + L)
      = (p : ℚ) ^ (-(L : ℤ)) * carryTail p (dropGapDig i₀ L v) i₀ := by
    conv_lhs => rw [← hrv]
    have h := carryTail_gapDig p hp0 (dropGapDig i₀ L v)
      (j := i₀ + 1) (n := L) (D := i₀ + L) (by omega) (by omega)
    simpa [Nat.add_sub_cancel] using h
  have hA : (p : ℚ) ^ (-(L : ℤ))
        * (carryTail p (dropGapDig i₀ L u) i₀ + carryTail p (dropGapDig i₀ L v) i₀)
      = (p : ℚ) ^ (-(n : ℤ)) * carryTail p b (j - 1) := by
    linear_combination htw + hTz - hτu - hτv
  have hpowL : (p : ℚ) ^ ((L : ℤ)) * (p : ℚ) ^ (-(L : ℤ)) = 1 := by
    rw [← zpow_add₀ hpne]
    simp
  have hpow2 : (p : ℚ) ^ ((L : ℤ)) * (p : ℚ) ^ (-(n : ℤ)) = (p : ℚ) ^ (-(n₀ : ℤ)) := by
    rw [← zpow_add₀ hpne]
    congr 1
    omega
  have htail : carryTail p (dropGapDig i₀ L u) i₀ + carryTail p (dropGapDig i₀ L v) i₀
      = (p : ℚ) ^ (-(n₀ : ℤ)) * carryTail p b (j - 1) := by
    linear_combination (p : ℚ) ^ ((L : ℤ)) * hA
      - (carryTail p (dropGapDig i₀ L u) i₀ + carryTail p (dropGapDig i₀ L v) i₀) * hpowL
      + carryTail p b (j - 1) * hpow2
  -- transfer the value identity through the insertion formula
  have hiu := fracVal_gapDig_insert p hp0 i₀ L (dropGapDig i₀ L u)
  have hiv := fracVal_gapDig_insert p hp0 i₀ L (dropGapDig i₀ L v)
  rw [hru] at hiu
  rw [hrv] at hiv
  have hzn : fracVal p (gapDig j n b)
      = (∑ i ∈ range (j - 1), (b i : ℚ) * (p : ℚ) ^ (-(i + 1 : ℤ)))
        + (p : ℚ) ^ (-(n : ℤ)) * carryTail p b (j - 1) := fracVal_gapDig p hp0 j n b
  have hzn₀ : fracVal p (gapDig j n₀ b)
      = (∑ i ∈ range (j - 1), (b i : ℚ) * (p : ℚ) ^ (-(i + 1 : ℤ)))
        + (p : ℚ) ^ (-(n₀ : ℤ)) * carryTail p b (j - 1) := fracVal_gapDig p hp0 j n₀ b
  have hpow : (p : ℚ) ^ (-(n₀ : ℤ)) * (p : ℚ) ^ (-(L : ℤ)) = (p : ℚ) ^ (-(n : ℤ)) := by
    rw [← zpow_add₀ hpne]
    congr 1
    omega
  linear_combination hval - hiu - hiv + hzn - hzn₀
    + (1 - (p : ℚ) ^ (-(L : ℤ))) * htail - carryTail p b (j - 1) * hpow

/-- **Expansion across a widening gap** (inverse to `decomp_gapDig_contract`):
inserting `L = n - n₀` zero columns at `i₀ = (j-1)+K` turns a decomposition of the
gapped target at gap size `n₀ = c₁+c₂+1` into one at gap size `n ≥ n₀`.  Digit
bounds and digit sums are preserved by `gapDig_lt` and `gapDig_sum`, and
`dropGapDig_gapDig` recovers the original pair. -/
theorem decomp_gapDig_expand {b u₀ v₀ : ℕ →₀ ℕ} {κ c₁ c₂ j n K n₀ i₀ L : ℕ}
    (hκ : κ ≤ 1) (hK : K = (c₁ + c₂) / (p - 1)) (hn₀ : n₀ = c₁ + c₂ + 1)
    (hi₀ : i₀ = j - 1 + K) (hL : L = n - n₀) (hn : n₀ ≤ n)
    (hb : ∀ i, b i < p) (hu : ∀ i, u₀ i < p) (hv : ∀ i, v₀ i < p)
    (hc₁ : (u₀.sum fun _ v => v) ≤ c₁) (hc₂ : (v₀.sum fun _ v => v) ≤ c₂)
    (hval : fracVal p u₀ + fracVal p v₀ = (κ : ℚ) + fracVal p (gapDig j n₀ b)) :
    fracVal p (gapDig (i₀ + 1) L u₀) + fracVal p (gapDig (i₀ + 1) L v₀)
      = (κ : ℚ) + fracVal p (gapDig j n b) := by
  have hp0 := hp.out.pos
  have hpne : ((p : ℚ)) ≠ 0 := by exact_mod_cast hp0.ne'
  have hKle : K ≤ c₁ + c₂ := hK ▸ Nat.div_le_self _ _
  obtain ⟨-, hbits⟩ := decomp_gapDig_confine p hκ hK hi₀ (by omega) hb hu hv hc₁ hc₂ hval
  have hbit0 : carryBit p (u₀ + v₀) i₀ = 0 := hbits i₀ le_rfl (by omega)
  have htw := decomp_carryTail_eq p hκ hu hv
    (fun i => gapDig_lt p hb hp0 j n₀ i) hval hbit0
  have hTz : carryTail p (gapDig j n₀ b) i₀
      = (p : ℚ) ^ (-(n₀ : ℤ)) * carryTail p b (j - 1) :=
    carryTail_gapDig p hp0 b (by omega) (by omega)
  have hiu := fracVal_gapDig_insert p hp0 i₀ L u₀
  have hiv := fracVal_gapDig_insert p hp0 i₀ L v₀
  have hzn : fracVal p (gapDig j n b)
      = (∑ i ∈ range (j - 1), (b i : ℚ) * (p : ℚ) ^ (-(i + 1 : ℤ)))
        + (p : ℚ) ^ (-(n : ℤ)) * carryTail p b (j - 1) := fracVal_gapDig p hp0 j n b
  have hzn₀ : fracVal p (gapDig j n₀ b)
      = (∑ i ∈ range (j - 1), (b i : ℚ) * (p : ℚ) ^ (-(i + 1 : ℤ)))
        + (p : ℚ) ^ (-(n₀ : ℤ)) * carryTail p b (j - 1) := fracVal_gapDig p hp0 j n₀ b
  have hpow : (p : ℚ) ^ (-(n₀ : ℤ)) * (p : ℚ) ^ (-(L : ℤ)) = (p : ℚ) ^ (-(n : ℤ)) := by
    rw [← zpow_add₀ hpne]
    congr 1
    omega
  linear_combination hval + hiu + hiv + hzn₀ - hzn
    - (1 - (p : ℚ) ^ (-(L : ℤ))) * (htw.trans hTz) + carryTail p b (j - 1) * hpow

/-- **Component families** (Kedlaya (2001a), proof of Theorem 8): the components of
a decomposition of the gapped target at gap size `n ≥ n₀` are the values, at index
`n - K` of the twist family with gap at `i₀ = (j-1)+K`, of their full contractions —
which are computed from the contracted pair at gap size `n₀` and hence do not
depend on `n`. -/
theorem decomp_gapDig_component {b u v : ℕ →₀ ℕ} {κ c₁ c₂ j n K n₀ i₀ L : ℕ}
    (hκ : κ ≤ 1) (hK : K = (c₁ + c₂) / (p - 1)) (hn₀ : n₀ = c₁ + c₂ + 1)
    (hi₀ : i₀ = j - 1 + K) (hL : L = n - n₀) (hn : n₀ ≤ n)
    (hb : ∀ i, b i < p) (hu : ∀ i, u i < p) (hv : ∀ i, v i < p)
    (hc₁ : (u.sum fun _ v => v) ≤ c₁) (hc₂ : (v.sum fun _ v => v) ≤ c₂)
    (hval : fracVal p u + fracVal p v = (κ : ℚ) + fracVal p (gapDig j n b)) :
    gapDig (i₀ + 1) (n - K) (dropGapDig i₀ (n₀ - K) (dropGapDig i₀ L u)) = u ∧
      gapDig (i₀ + 1) (n - K) (dropGapDig i₀ (n₀ - K) (dropGapDig i₀ L v)) = v := by
  have hKle : K ≤ c₁ + c₂ := hK ▸ Nat.div_le_self _ _
  obtain ⟨hzero, -⟩ := decomp_gapDig_confine p hκ hK hi₀ (by omega) hb hu hv hc₁ hc₂ hval
  constructor
  · rw [dropGapDig_dropGapDig, show L + (n₀ - K) = n - K by omega]
    exact gapDig_dropGapDig fun i h1 h2 => (hzero i h1 (by omega)).1
  · rw [dropGapDig_dropGapDig, show L + (n₀ - K) = n - K by omega]
    exact gapDig_dropGapDig fun i h1 h2 => (hzero i h1 (by omega)).2

end TrustworthyKedlaya.UP
