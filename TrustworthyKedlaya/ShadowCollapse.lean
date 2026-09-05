/-
Copyright (c) 2026 Shanwen Wang, Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import TrustworthyKedlaya.ShadowCalculus
public import TrustworthyKedlaya.TeichCarry
public import TrustworthyKedlaya.Coeffwise
public import TrustworthyKedlaya.IntTruncation

/-!
# Carry expansion for a sum of two shadows

A sum of two shadows of Hahn series expands, below any cutoff, into a finite sum
of shadows: `S(y) + S(y') = S(y + y') + ∑_{1 ≤ i ≤ K} S(tⁱ·zᵢ) + E` with
`v_p(E) ≥ v + K + 1`, where `zᵢ` is the coefficientwise carry-digit series
`(zᵢ)_q = carryDigit i (y_q) (y'_q)`.  Each carry
term shifts supports strictly upward, which drives the truncation induction of
`TrustworthyKedlaya.EngineTruncUP`.

The proof works at the lifted level: at each exponent the Teichmüller carry
congruence (`TrustworthyKedlaya.TeichCarry`) makes the defect coefficientwise
divisible by `p^{K+1}`, and dividing coefficientwise, then trading the scalar
`p^{K+1}` for the exponent shift `t^{K+1}` modulo null series, converts the
divisibility into the valuation bound.

## Main statements

- `TrustworthyKedlaya.pAdicHahnSeries.shadow_single_one_mul` /
  `p_pow_mul_shadow`: shadows intertwine monomial shifts with `p`-power
  multiplication.
- `TrustworthyKedlaya.pAdicHahnSeries.le_val_mkLp_of_forall_pow_dvd_coeff`:
  coefficientwise `p^k`-divisibility plus a support bound `v` gives valuation
  `≥ v + k`.
- `TrustworthyKedlaya.pAdicHahnSeries.le_val_shadow_add_collapse`: the carry
  expansion bound.

## References

- K. S. Kedlaya, *Power series and p-adic algebraic closures*, J. Number Theory 89
  (2001) [Ked01b], proof of Theorem 7.
-/

@[expose] public section

namespace TrustworthyKedlaya.pAdicHahnSeries

open WittVector

variable {p : ℕ} [hp : Fact (Nat.Prime p)]

/-- In `𝕃_[p]` the element `p` is the one-term series `[1]·p¹`. -/
theorem p_eq_single_one : ((p : ℕ) : 𝕃_[p]) = single 1 1 := by
  rw [single, fromCoeff, lifted_fromCoeff_single, map_one, mkLp_single_one]

/-- In `𝕃_[p]` the element `pⁱ` is the one-term series `[1]·pⁱ`. -/
theorem p_pow_eq_single (i : ℕ) :
    ((p : ℕ) : 𝕃_[p]) ^ i = single (i : ℚ) 1 := by
  rw [p_eq_single_one, single_pow, one_pow, mul_one]

/-- The shadow map intertwines monomial shifts: `S(t^q·z) = p^q·S(z)`. -/
theorem shadow_single_one_mul (q : ℚ) (z : HahnSeries ℚ (𝔽ᵃ_[p])) :
    shadow (HahnSeries.single q (1 : 𝔽ᵃ_[p]) * z) = single q 1 * shadow z := by
  apply ext_coeff
  funext r
  rw [coeff_shadow, coeff_ppow_mul, coeff_shadow, HahnSeries.coeff_single_mul, one_mul]

/-- The shadow map intertwines integer shifts with `p`-power multiplication:
`S(tⁱ·z) = pⁱ·S(z)`. -/
theorem p_pow_mul_shadow (i : ℕ) (z : HahnSeries ℚ (𝔽ᵃ_[p])) :
    ((p : ℕ) : 𝕃_[p]) ^ i * shadow z
      = shadow (HahnSeries.single (i : ℚ) (1 : 𝔽ᵃ_[p]) * z) := by
  rw [p_pow_eq_single, shadow_single_one_mul]

/-- Powers of the lifted one-term series `[1]·t¹`. -/
private theorem lifted_single_one_pow (k : ℕ) :
    (HahnSeries.single (1 : ℚ) (1 : ℤᶜᵘⁿ_[p])) ^ k
      = HahnSeries.single (k : ℚ) (1 : ℤᶜᵘⁿ_[p]) := by
  induction k with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, HahnSeries.single_mul_single, mul_one]
    norm_num

/-- **Divisibility gives valuation**: a lifted series all of whose coefficients are
divisible by `pᵏ`, and which vanishes below `v`, represents a class of valuation at
least `v + k`: divide coefficientwise, then trade the scalar `pᵏ` for the exponent
shift `tᵏ` modulo null series. -/
theorem le_val_mkLp_of_forall_pow_dvd_coeff {Δ : LiftedPAdicHahnSeries p} {k : ℕ}
    (hdvd : ∀ q, ((p : ℤᶜᵘⁿ_[p]) ^ k) ∣ Δ.coeff q) {v : ℚ}
    (hbelow : ∀ q < v, Δ.coeff q = 0) :
    ((v + k : ℚ) : WithTop ℚ) ≤ val p (Ideal.Quotient.mk (NullSeriesIdeal p) Δ) := by
  classical
  have hpk0 : ((p : ℤᶜᵘⁿ_[p]) ^ k) ≠ 0 :=
    pow_ne_zero _ (WittVector.p_nonzero p (𝔽ᵃ_[p]))
  -- coefficientwise quotient by `p^k`
  set c : ℚ → ℤᶜᵘⁿ_[p] := fun q => (hdvd q).choose with hc
  have hcspec : ∀ q, Δ.coeff q = ((p : ℤᶜᵘⁿ_[p]) ^ k) * c q := fun q => (hdvd q).choose_spec
  have hczero : ∀ q, Δ.coeff q = 0 → c q = 0 := by
    intro q h0
    have h1 := hcspec q
    rw [h0] at h1
    exact (mul_eq_zero.mp h1.symm).resolve_left hpk0
  have hcsupp : Function.support c ⊆ Function.support Δ.coeff := by
    intro q hq
    rw [Function.mem_support] at hq ⊢
    exact fun h0 => hq (hczero q h0)
  set Δ' : LiftedPAdicHahnSeries p := ⟨c, Δ.isPWO_support'.mono hcsupp⟩ with hΔ'
  have hΔ'coeff : ∀ q, Δ'.coeff q = c q := fun q => rfl
  -- `Δ = [p^k]·Δ'` at the lifted level
  have hfact : Δ = HahnSeries.single (0 : ℚ) ((p : ℤᶜᵘⁿ_[p]) ^ k) * Δ' := by
    apply HahnSeries.ext
    funext q
    rw [HahnSeries.coeff_single_mul, sub_zero, hΔ'coeff]
    exact hcspec q
  -- in the quotient, trade the scalar `p^k` for the shift `t^k`
  have hmk : Ideal.Quotient.mk (NullSeriesIdeal p) Δ
      = Ideal.Quotient.mk (NullSeriesIdeal p)
          (HahnSeries.single (k : ℚ) (1 : ℤᶜᵘⁿ_[p]) * Δ') := by
    rw [hfact, ← lifted_single_one_pow, map_mul, map_mul]
    congr 1
    rw [← HahnSeries.C_apply, map_pow, map_natCast, map_pow, map_natCast,
      map_pow, mkLp_single_one]
  rw [hmk]
  refine le_val_mkLp_of_coeff_eq_zero fun q hq => ?_
  rw [HahnSeries.coeff_single_mul, one_mul, hΔ'coeff]
  exact hczero _ (hbelow _ (by linarith))

/-- The shifted carry-digit series `tⁱ·zᵢ` of two UP series are UP
(the UP clause of the carry expansion). -/
theorem isUP_single_mul_coeffwise_carry {y y' : HahnSeries ℚ (𝔽ᵃ_[p])}
    (hy : UP.IsUP p y) (hy' : UP.IsUP p y') (i : ℕ) :
    UP.IsUP p (HahnSeries.single (i : ℚ) (1 : 𝔽ᵃ_[p])
      * UP.coeffwise p (carryDigit p i) (carryDigit_zero_zero p i) y y') := by
  have h := UP.isUP_single_intCast p (i : ℤ) (1 : 𝔽ᵃ_[p])
  rw [Int.cast_natCast] at h
  exact h.mul (hy.coeffwise hy' (carryDigit p i) (carryDigit_zero_zero p i))

/-- **Carry expansion for a sum of two shadows**: with
`zᵢ` the coefficientwise carry-digit series of `y` and `y'`, the defect
`S(y) + S(y') - S(y+y') - ∑_{1 ≤ i ≤ K} S(tⁱ·zᵢ)` has valuation at least
`v + K + 1`, where `v` bounds both supports from below. -/
theorem le_val_shadow_add_collapse (y y' : HahnSeries ℚ (𝔽ᵃ_[p])) {v : ℚ}
    (hy : ∀ q < v, y.coeff q = 0) (hy' : ∀ q < v, y'.coeff q = 0) (K : ℕ) :
    ((v + (K + 1) : ℚ) : WithTop ℚ) ≤ val p
      (shadow y + shadow y' - shadow (y + y')
        - ∑ i ∈ Finset.Icc 1 K, shadow (HahnSeries.single (i : ℚ) (1 : 𝔽ᵃ_[p])
            * UP.coeffwise p (carryDigit p i) (carryDigit_zero_zero p i) y y')) := by
  classical
  -- the lifted defect, with the carries as scalar `p^i` multiples (no shift)
  set Z : ℕ → LiftedPAdicHahnSeries p := fun i =>
    LiftedPAdicHahnSeries.fromCoeff
      (UP.coeffwise p (carryDigit p i) (carryDigit_zero_zero p i) y y').coeff
      (UP.coeffwise p (carryDigit p i) (carryDigit_zero_zero p i) y y').isPWO_support'
    with hZ
  set D : LiftedPAdicHahnSeries p :=
    LiftedPAdicHahnSeries.fromCoeff y.coeff y.isPWO_support'
      + LiftedPAdicHahnSeries.fromCoeff y'.coeff y'.isPWO_support'
      - LiftedPAdicHahnSeries.fromCoeff (y + y').coeff (y + y').isPWO_support'
      - ∑ i ∈ Finset.Icc 1 K,
          HahnSeries.single (0 : ℚ) ((p : ℤᶜᵘⁿ_[p]) ^ i) * Z i with hD
  -- the coefficients of the lifted defect, columnwise
  have hDcoeff : ∀ q : ℚ, D.coeff q
      = (teichmuller p (y.coeff q) + teichmuller p (y'.coeff q))
        - (teichmuller p (y.coeff q + y'.coeff q)
          + ∑ i ∈ Finset.Icc 1 K,
              teichmuller p (carryDigit p i (y.coeff q) (y'.coeff q))
                * (p : ℤᶜᵘⁿ_[p]) ^ i) := by
    intro q
    rw [hD]
    rw [HahnSeries.coeff_sub', HahnSeries.coeff_sub', HahnSeries.coeff_add']
    simp only [Pi.sub_apply, Pi.add_apply]
    have hsum : (∑ i ∈ Finset.Icc 1 K,
        HahnSeries.single (0 : ℚ) ((p : ℤᶜᵘⁿ_[p]) ^ i) * Z i).coeff q
        = ∑ i ∈ Finset.Icc 1 K,
            teichmuller p (carryDigit p i (y.coeff q) (y'.coeff q))
              * (p : ℤᶜᵘⁿ_[p]) ^ i := by
      rw [HahnSeries.coeff_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [HahnSeries.coeff_single_mul, sub_zero, mul_comm]
      rfl
    rw [hsum]
    have hadd : (y + y').coeff q = y.coeff q + y'.coeff q := by
      rw [HahnSeries.coeff_add', Pi.add_apply]
    change teichmuller p (y.coeff q) + teichmuller p (y'.coeff q)
        - teichmuller p ((y + y').coeff q) - _ = _
    rw [hadd]
    ring
  -- columnwise divisibility from the Teichmüller carry congruence
  have hdvd : ∀ q, ((p : ℤᶜᵘⁿ_[p]) ^ (K + 1)) ∣ D.coeff q := by
    intro q
    rw [hDcoeff q]
    exact teichmuller_add_sub_sum_carryDigit_dvd p (y.coeff q) (y'.coeff q) K
  -- the defect vanishes below `v`
  have hbelow : ∀ q < v, D.coeff q = 0 := by
    intro q hq
    rw [hDcoeff q, hy q hq, hy' q hq]
    simp
  -- identify the goal element with the class of `D`
  have hgoal : shadow y + shadow y' - shadow (y + y')
      - ∑ i ∈ Finset.Icc 1 K, shadow (HahnSeries.single (i : ℚ) (1 : 𝔽ᵃ_[p])
          * UP.coeffwise p (carryDigit p i) (carryDigit_zero_zero p i) y y')
      = Ideal.Quotient.mk (NullSeriesIdeal p) D := by
    rw [hD, map_sub, map_sub, map_add, map_sum]
    rw [← shadow_eq_mkLp, ← shadow_eq_mkLp, ← shadow_eq_mkLp]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← p_pow_mul_shadow, map_mul]
    congr 1
    rw [← HahnSeries.C_apply, map_pow, map_natCast, map_pow, map_natCast]
  rw [hgoal]
  exact_mod_cast le_val_mkLp_of_forall_pow_dvd_coeff hdvd hbelow

end TrustworthyKedlaya.pAdicHahnSeries
