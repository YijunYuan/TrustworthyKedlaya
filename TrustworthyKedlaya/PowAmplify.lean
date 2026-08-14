/-
Copyright (c) 2026 Shanwen Wang, Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import TrustworthyKedlaya.NewtonSlope
public import TrustworthyKedlaya.ShadowCalculus
public import Mathlib.Data.Nat.Choose.Dvd

/-!
# `p`-power amplification of congruences and power shadows

Two amplification results (Kedlaya 2001b, p. 336: the Frobenius step "raising
both sides of the congruence to the `p^k`-th power"):

- `le_val_pow_pow_sub`: if `w ≤ val x`, `w ≤ val y` and
  `val (x - y) ≥ w + e` with `e ≥ 0`, then
  `val (x^{p^k} - y^{p^k}) ≥ p^k w + min 1 (p^k e)` — one `p`-th power gains
  the factor `p` on the congruence excess until the excess reaches `1`, by the
  binomial expansion (all middle binomial coefficients are divisible by `p`
  and `v(p) = 1`).
- `le_val_shadow_pow_sub`: the iterated multiplication carry
  `val (S(u)^j - S(u^j)) ≥ j a + 1` for `u` supported at exponents `≥ a`.

## References

- K. S. Kedlaya, *Power series and `p`-adic algebraic closures*, J. Number
  Theory 89 (2001) [Ked01b], p. 336.
-/

@[expose] public section

namespace TrustworthyKedlaya.pAdicHahnSeries

variable {p : ℕ} [hp : Fact (Nat.Prime p)]

/-- A common valuation lower bound passes to finite sums. -/
theorem le_val_finset_sum {ι : Type*} (s : Finset ι) (f : ι → 𝕃_[p]) {g : WithTop ℚ}
    (h : ∀ i ∈ s, g ≤ val p (f i)) : g ≤ val p (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, val_zero_eq_top]
    exact le_top
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (val p).map_le_add (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- Natural-number scalars have nonnegative valuation. -/
theorem le_val_natCast (n : ℕ) : (0 : WithTop ℚ) ≤ val p (n : 𝕃_[p]) := by
  have h := le_val_natCast_mul (p := p) n 1
  rwa [mul_one, (val p).map_one] at h

/-- **One `p`-th power step of congruence amplification**: from
`val (x - y) ≥ w + e` (with `w` a common lower bound for `val x`, `val y` and
`e ≥ 0`) deduce `val (x^p - y^p) ≥ p w + min 1 (p e)`.  In the binomial
expansion of `((x - y) + y)^p - y^p`, the middle terms carry a factor `p`
(valuation `1`), and the extreme term carries `(x - y)^p`. -/
theorem le_val_pow_char_sub {x y : 𝕃_[p]} {w e : ℚ} (he : 0 ≤ e)
    (hx : (w : WithTop ℚ) ≤ val p x) (hy : (w : WithTop ℚ) ≤ val p y)
    (hxy : ((w + e : ℚ) : WithTop ℚ) ≤ val p (x - y)) :
    (((p : ℚ) * w + min 1 ((p : ℚ) * e) : ℚ) : WithTop ℚ) ≤ val p (x ^ p - y ^ p) := by
  classical
  have hp1 : 1 ≤ (p : ℚ) := by exact_mod_cast hp.out.one_lt.le
  -- binomial expansion of `x = (x - y) + y`
  have hexp : x ^ p - y ^ p
      = ∑ j ∈ Finset.Ico 1 (p + 1), (x - y) ^ j * y ^ (p - j) * (p.choose j : 𝕃_[p]) := by
    have h0 : (x - y) ^ 0 * y ^ (p - 0) * (p.choose 0 : 𝕃_[p]) = y ^ p := by
      rw [pow_zero, one_mul, Nat.sub_zero, Nat.choose_zero_right, Nat.cast_one, mul_one]
    calc x ^ p - y ^ p = ((x - y) + y) ^ p - y ^ p := by rw [sub_add_cancel]
      _ = (∑ j ∈ Finset.range (p + 1),
            (x - y) ^ j * y ^ (p - j) * (p.choose j : 𝕃_[p])) - y ^ p := by
          rw [add_pow]
      _ = _ := by
          rw [Finset.range_eq_Ico,
            Finset.sum_eq_sum_Ico_succ_bot (Nat.succ_pos p), h0, add_sub_cancel_left]
  rw [hexp]
  refine le_val_finset_sum _ _ fun j hj => ?_
  obtain ⟨hj1, hjp⟩ := Finset.mem_Ico.mp hj
  have hjle : j ≤ p := Nat.lt_succ_iff.mp hjp
  rcases eq_or_lt_of_le hjle with hjp' | hjlt
  · -- the extreme term `(x - y)^p`
    subst hjp'
    rw [Nat.sub_self, pow_zero, mul_one, Nat.choose_self, Nat.cast_one, mul_one]
    refine le_trans ?_ (le_val_pow hxy j)
    rw [WithTop.coe_le_coe]
    have hmin : min 1 ((j : ℚ) * e) ≤ (j : ℚ) * e := min_le_right _ _
    have : (j : ℚ) * (w + e) = (j : ℚ) * w + (j : ℚ) * e := by ring
    linarith
  · -- a middle term: the binomial coefficient is divisible by `p`
    obtain ⟨m, hm⟩ :=
      Nat.Prime.dvd_choose_self hp.out (Nat.one_le_iff_ne_zero.mp hj1) hjlt
    have hval : val p ((x - y) ^ j * y ^ (p - j) * (p.choose j : 𝕃_[p]))
        = val p ((x - y) ^ j) + val p (y ^ (p - j)) + val p ((p.choose j : 𝕃_[p])) := by
      rw [(val p).map_mul, (val p).map_mul]
    have hC : ((1 : ℚ) : WithTop ℚ) ≤ val p ((p.choose j : 𝕃_[p])) := by
      rw [hm, Nat.cast_mul, (val p).map_mul, val_p_eq_one]
      have h0m := le_val_natCast (p := p) m
      calc ((1 : ℚ) : WithTop ℚ) = (1 : ℚ) + (0 : WithTop ℚ) := by
            rw [add_zero]
        _ ≤ ((1 : ℚ) : WithTop ℚ) + val p (m : 𝕃_[p]) := add_le_add le_rfl h0m
    have hA : (((j : ℚ) * (w + e) : ℚ) : WithTop ℚ) ≤ val p ((x - y) ^ j) :=
      le_val_pow hxy j
    have hB : ((((p : ℚ) - (j : ℚ)) * w : ℚ) : WithTop ℚ) ≤ val p (y ^ (p - j)) := by
      have := le_val_pow hy (p - j)
      rwa [Nat.cast_sub hjle] at this
    rw [hval]
    calc (((p : ℚ) * w + min 1 ((p : ℚ) * e) : ℚ) : WithTop ℚ)
        ≤ (((j : ℚ) * (w + e) + ((p : ℚ) - (j : ℚ)) * w + 1 : ℚ) : WithTop ℚ) := by
          rw [WithTop.coe_le_coe]
          have hje : 0 ≤ (j : ℚ) * e := by positivity
          have hmin : min 1 ((p : ℚ) * e) ≤ 1 := min_le_left _ _
          linarith
      _ = (((j : ℚ) * (w + e) : ℚ) : WithTop ℚ) + ((((p : ℚ) - (j : ℚ)) * w : ℚ) : WithTop ℚ)
          + ((1 : ℚ) : WithTop ℚ) := by
          rw [← WithTop.coe_add, ← WithTop.coe_add]
      _ ≤ val p ((x - y) ^ j) + val p (y ^ (p - j)) + val p ((p.choose j : 𝕃_[p])) :=
          add_le_add (add_le_add hA hB) hC

/-- **`p^k`-power amplification of congruences** (Kedlaya 2001b, p. 336): from
`val (x - y) ≥ w + e` with `w` a common lower
bound for `val x`, `val y` and `e ≥ 0`,
`val (x^{p^k} - y^{p^k}) ≥ p^k w + min 1 (p^k e)`: each `p`-th power multiplies
the congruence excess by `p` until it reaches the absolute carry depth `1`. -/
theorem le_val_pow_pow_sub {x y : 𝕃_[p]} {w e : ℚ} (he : 0 ≤ e)
    (hx : (w : WithTop ℚ) ≤ val p x) (hy : (w : WithTop ℚ) ≤ val p y)
    (hxy : ((w + e : ℚ) : WithTop ℚ) ≤ val p (x - y)) (k : ℕ) :
    (((p : ℚ) ^ k * w + min 1 ((p : ℚ) ^ k * e) : ℚ) : WithTop ℚ)
      ≤ val p (x ^ p ^ k - y ^ p ^ k) := by
  have hp1 : 1 ≤ (p : ℚ) := by exact_mod_cast hp.out.one_lt.le
  induction k with
  | zero =>
    simp only [pow_zero, pow_one, one_mul]
    refine le_trans ?_ hxy
    rw [WithTop.coe_le_coe]
    have := min_le_right (1 : ℚ) e
    linarith
  | succ k ih =>
    have hxk : (((p : ℚ) ^ k * w : ℚ) : WithTop ℚ) ≤ val p (x ^ p ^ k) := by
      have h := le_val_pow hx (p ^ k)
      rwa [Nat.cast_pow] at h
    have hyk : (((p : ℚ) ^ k * w : ℚ) : WithTop ℚ) ≤ val p (y ^ p ^ k) := by
      have h := le_val_pow hy (p ^ k)
      rwa [Nat.cast_pow] at h
    have he' : 0 ≤ min 1 ((p : ℚ) ^ k * e) := le_min zero_le_one (by positivity)
    have hstep := le_val_pow_char_sub (w := (p : ℚ) ^ k * w)
      (e := min 1 ((p : ℚ) ^ k * e)) he' hxk hyk ih
    have hpow : ∀ z : 𝕃_[p], (z ^ p ^ k) ^ p = z ^ p ^ (k + 1) := fun z => by
      rw [← pow_mul, ← pow_succ]
    rw [hpow, hpow] at hstep
    refine le_trans ?_ hstep
    rw [WithTop.coe_le_coe]
    have hassoc : (p : ℚ) * ((p : ℚ) ^ k * w) = (p : ℚ) ^ (k + 1) * w := by ring
    have hmin : min 1 ((p : ℚ) ^ (k + 1) * e) ≤ min 1 ((p : ℚ) * min 1 ((p : ℚ) ^ k * e)) := by
      rcases le_total ((p : ℚ) ^ k * e) 1 with h | h
      · rw [min_eq_right h]
        have : (p : ℚ) * ((p : ℚ) ^ k * e) = (p : ℚ) ^ (k + 1) * e := by ring
        rw [this]
      · have h1 : min 1 ((p : ℚ) ^ k * e) = 1 := min_eq_left h
        rw [h1, mul_one]
        have hpk1 : (1 : ℚ) ≤ (p : ℚ) ^ (k + 1) * e := by
          calc (1 : ℚ) ≤ (p : ℚ) ^ k * e := h
            _ ≤ (p : ℚ) * ((p : ℚ) ^ k * e) := le_mul_of_one_le_left (by positivity) hp1
            _ = (p : ℚ) ^ (k + 1) * e := by ring
        rw [min_eq_left hpk1, min_eq_left hp1]
    linarith
  -- (the `p ≥ 1` fact is used in both branches above)

/-- Coefficients of a power of a Hahn series obey the summed support bound. -/
theorem forall_le_coeff_pow {u : HahnSeries ℚ (𝔽ᵃ_[p])} {a : ℚ}
    (hu : ∀ q, u.coeff q ≠ 0 → a ≤ q) (j : ℕ) :
    ∀ q, (u ^ j).coeff q ≠ 0 → (j : ℚ) * a ≤ q := by
  induction j with
  | zero =>
    intro q hq
    rw [pow_zero] at hq
    have hq0 : q = 0 := by
      by_contra h0
      exact hq (by rw [HahnSeries.coeff_one, if_neg h0])
    rw [hq0, Nat.cast_zero, zero_mul]
  | succ j ih =>
    intro q hq
    rw [pow_succ, HahnSeries.coeff_mul] at hq
    obtain ⟨⟨q1, q2⟩, hmem, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero hq
    simp only [Finset.mem_antidiagonal] at hmem
    obtain ⟨hq1, hq2, hsum⟩ := hmem
    have h1 : (j : ℚ) * a ≤ q1 := ih q1 hq1
    have h2 : a ≤ q2 := hu q2 hq2
    rw [← hsum]
    push_cast
    linarith

/-- **Iterated multiplication carry for power shadows**: for `u` supported at
exponents `≥ a` and `j ≥ 1`,
`val (S(u)^j - S(u^j)) ≥ j a + 1`.  Induction on `j`: each step is one
multiplication carry (`le_val_shadow_mul_sub`) plus the inductive difference
scaled by `S(u)`. -/
theorem le_val_shadow_pow_sub (u : HahnSeries ℚ (𝔽ᵃ_[p])) (a : ℚ)
    (hu : ∀ q, u.coeff q ≠ 0 → a ≤ q) {j : ℕ} (hj : 1 ≤ j) :
    (((j : ℚ) * a + 1 : ℚ) : WithTop ℚ) ≤ val p (shadow u ^ j - shadow (u ^ j)) := by
  induction j, hj using Nat.le_induction with
  | base =>
    rw [pow_one, pow_one, sub_self, val_zero_eq_top]
    exact le_top
  | succ j hj ih =>
    rw [pow_succ, pow_succ]
    have hcast : ((j + 1 : ℕ) : ℚ) = (j : ℚ) + 1 := by push_cast; ring
    rw [hcast]
    have hident : shadow u ^ j * shadow u - shadow (u ^ j * u)
        = (shadow u ^ j - shadow (u ^ j)) * shadow u
          + (shadow (u ^ j) * shadow u - shadow (u ^ j * u)) := by
      ring
    rw [hident]
    have hSu : ((a : ℚ) : WithTop ℚ) ≤ val p (shadow u) := by
      rw [val_shadow]
      refine HahnSeries.le_orderTop_iff_forall.mpr fun q hq => ?_
      by_contra hne
      exact absurd (hu q hne) (not_le.mpr (by exact_mod_cast hq))
    refine (val p).map_le_add ?_ ?_
    · rw [(val p).map_mul]
      calc ((((j : ℚ) + 1) * a + 1 : ℚ) : WithTop ℚ)
          = (((j : ℚ) * a + 1 : ℚ) : WithTop ℚ) + ((a : ℚ) : WithTop ℚ) := by
            rw [← WithTop.coe_add]
            congr 1
            ring
        _ ≤ val p (shadow u ^ j - shadow (u ^ j)) + val p (shadow u) := add_le_add ih hSu
    · rw [(val p).map_sub_swap]
      have hcarry := le_val_shadow_mul_sub (u ^ j) u ((j : ℚ) * a) a
        (forall_le_coeff_pow hu j) hu
      refine le_trans ?_ hcarry
      rw [WithTop.coe_le_coe]
      linarith

end TrustworthyKedlaya.pAdicHahnSeries
