/-
Copyright (c) 2026 Shanwen Wang, Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import TrustworthyKedlaya.Kedlaya.WittCarryUP
public import TrustworthyKedlaya.Kedlaya.MulCombine

/-!
# Witt carries preserve uniform periodicity: products

The set `B'` of truncationwise-UP elements of `𝕃_[p]` is closed under
multiplication, hence is a subring containing every integer polynomial in shadows
of UP series.

The engine is the **digit expansion of a product of shadows**:
at the lifted level, the column of
`lift(y)·lift(y')` at an exponent `q` is the finite sum of Teichmüller lifts
`∑ [u·u']` over the coefficient-pair multiset `mulPairs y y' q`, so its
Teichmüller digits define **product-digit series** `Dᵢ` — convolution
combinations in the sense of `TrustworthyKedlaya.Kedlaya.MulCombine`, hence UP — with
`S(y)·S(y') = ∑_{i ≤ K} pⁱ·S(Dᵢ)` up to valuation `v₁ + v₂ + K + 1` and
`D₀ = y·y'`.  Truncations of a product of shadows below any cutoff are therefore
truncations of a finite sum of shadows of UP series, and the sum engine
(`TrustworthyKedlaya.Kedlaya.EngineTruncUP`) applies.

## Main statements

- `TrustworthyKedlaya.pAdicHahnSeries.mulDigit` / `mulDigitSeries`: the product
  digits of a coefficient-pair column, and the digit series `Dᵢ`.
- `TrustworthyKedlaya.pAdicHahnSeries.le_val_shadow_mul_collapse`: the digit
  expansion.
- `TrustworthyKedlaya.pAdicHahnSeries.IsTruncUP.mul` / `truncUPSubring`: `B'` is
  closed under multiplication and forms a subring.

## References

- K. S. Kedlaya, *Power series and p-adic algebraic closures*, J. Number Theory 89
  (2001) [Ked01b], proof of Theorem 7.
-/

@[expose] public section

namespace TrustworthyKedlaya.pAdicHahnSeries

open WittVector

variable {p : ℕ} [hp : Fact (Nat.Prime p)]

/-! ### Product digits of a coefficient-pair column -/

/-- The `i`-th **product digit** of a coefficient-pair column: the `i`-th
Teichmüller digit of the sum of the lifted pairwise products. -/
noncomputable def mulDigit (i : ℕ) (P : Multiset (𝔽ᵃ_[p] × 𝔽ᵃ_[p])) : 𝔽ᵃ_[p] :=
  teichDigit p i ((P.map fun uv => teichmuller p (uv.1 * uv.2)).sum)

@[simp] theorem mulDigit_empty (i : ℕ) : mulDigit i (0 : Multiset (𝔽ᵃ_[p] × 𝔽ᵃ_[p])) = 0 := by
  simp [mulDigit, teichDigit]

/-- The zeroth product digit is the sum of the products (the zeroth Witt coordinate
is additive and `[u]` has zeroth coordinate `u`). -/
theorem mulDigit_zero (P : Multiset (𝔽ᵃ_[p] × 𝔽ᵃ_[p])) :
    mulDigit 0 P = (P.map fun uv => uv.1 * uv.2).sum := by
  rw [mulDigit, teichDigit_zero]
  induction P using Multiset.induction_on with
  | empty => simp
  | cons a t ih =>
    rw [Multiset.map_cons, Multiset.sum_cons, WittVector.add_coeff_zero,
      Multiset.map_cons, Multiset.sum_cons, ih, WittVector.teichmuller_coeff_zero]

/-- The `i`-th **product-digit series** of two Hahn series: the convolution
combination of `y, y'` under the `i`-th product digit. -/
noncomputable def mulDigitSeries (i : ℕ) (y y' : HahnSeries ℚ (𝔽ᵃ_[p])) :
    HahnSeries ℚ (𝔽ᵃ_[p]) :=
  UP.mulCombine p (mulDigit i) (mulDigit_empty i) y y'

/-- The zeroth product-digit series is the Hahn product. -/
theorem mulDigitSeries_zero (y y' : HahnSeries ℚ (𝔽ᵃ_[p])) :
    mulDigitSeries 0 y y' = y * y' := by
  apply HahnSeries.ext
  funext q
  rw [mulDigitSeries, UP.coeff_mulCombine, mulDigit_zero,
    ← UP.coeff_mul_eq_sum_mulPairs]

/-- Product-digit series of UP series are UP. -/
theorem isUP_mulDigitSeries {y y' : HahnSeries ℚ (𝔽ᵃ_[p])}
    (hy : UP.IsUP p y) (hy' : UP.IsUP p y') (i : ℕ) :
    UP.IsUP p (mulDigitSeries i y y') := by
  unfold mulDigitSeries
  exact hy.mulCombine hy' (mulDigit i) (mulDigit_empty i)

/-- Product-digit series vanish below the sum of the support floors
(the support clause of the digit expansion). -/
theorem coeff_mulDigitSeries_eq_zero {y y' : HahnSeries ℚ (𝔽ᵃ_[p])} {v v' : ℚ}
    (hy : ∀ q < v, y.coeff q = 0) (hy' : ∀ q < v', y'.coeff q = 0) (i : ℕ)
    {q : ℚ} (hq : q < v + v') : (mulDigitSeries i y y').coeff q = 0 := by
  rw [mulDigitSeries, UP.coeff_mulCombine, UP.mulPairs_eq_zero_of_lt hy hy' hq,
    mulDigit_empty]

/-! ### The digit expansion of a product of shadows -/

/-- **Digit expansion of a product of shadows**: with
`Dᵢ` the product-digit series of `y` and `y'`, the defect
`S(y)·S(y') - ∑_{i ≤ K} pⁱ·S(Dᵢ)` has valuation at least `v + v' + K + 1`, where
`v, v'` bound the supports from below. -/
theorem le_val_shadow_mul_collapse (y y' : HahnSeries ℚ (𝔽ᵃ_[p])) {v v' : ℚ}
    (hy : ∀ q < v, y.coeff q = 0) (hy' : ∀ q < v', y'.coeff q = 0) (K : ℕ) :
    ((v + v' + (K + 1) : ℚ) : WithTop ℚ) ≤ val p
      (shadow y * shadow y'
        - ∑ i ∈ Finset.Iic K, ((p : ℕ) : 𝕃_[p]) ^ i * shadow (mulDigitSeries i y y')) := by
  classical
  -- the summed lifted column at each exponent
  set colsum : ℚ → ℤᶜᵘⁿ_[p] := fun q =>
    ((UP.mulPairs p y y' q).map fun uv => teichmuller p (uv.1 * uv.2)).sum with hcolsum
  -- the lifted defect
  set Δ : LiftedPAdicHahnSeries p :=
    LiftedPAdicHahnSeries.fromCoeff y.coeff y.isPWO_support'
        * LiftedPAdicHahnSeries.fromCoeff y'.coeff y'.isPWO_support'
      - ∑ i ∈ Finset.Iic K,
          HahnSeries.single (0 : ℚ) ((p : ℤᶜᵘⁿ_[p]) ^ i)
            * LiftedPAdicHahnSeries.fromCoeff (mulDigitSeries i y y').coeff
                (mulDigitSeries i y y').isPWO_support' with hΔ
  -- supports of the lifts agree with the originals
  have hFsupp : (LiftedPAdicHahnSeries.fromCoeff y.coeff y.isPWO_support').support
      = y.support := by
    ext q
    rw [HahnSeries.mem_support, HahnSeries.mem_support]
    exact Function.Injective.ne_iff' (injective_teichmuller p) (by simp)
  have hF'supp : (LiftedPAdicHahnSeries.fromCoeff y'.coeff y'.isPWO_support').support
      = y'.support := by
    ext q
    rw [HahnSeries.mem_support, HahnSeries.mem_support]
    exact Function.Injective.ne_iff' (injective_teichmuller p) (by simp)
  -- the lifted product, columnwise
  have hFcol : ∀ q : ℚ,
      (LiftedPAdicHahnSeries.fromCoeff y.coeff y.isPWO_support'
        * LiftedPAdicHahnSeries.fromCoeff y'.coeff y'.isPWO_support').coeff q
      = colsum q := by
    intro q
    rw [HahnSeries.coeff_mul]
    have hanti : Finset.antidiagonal
          (LiftedPAdicHahnSeries.fromCoeff y.coeff y.isPWO_support').isPWO_support
          (LiftedPAdicHahnSeries.fromCoeff y'.coeff y'.isPWO_support').isPWO_support q
        = Finset.antidiagonal y.isPWO_support y'.isPWO_support q := by
      apply Finset.ext
      intro ij
      constructor
      · intro h
        obtain ⟨h1, h2, h3⟩ := Finset.mem_antidiagonal.mp h
        exact Finset.mem_antidiagonal.mpr ⟨hFsupp ▸ h1, hF'supp ▸ h2, h3⟩
      · intro h
        obtain ⟨h1, h2, h3⟩ := Finset.mem_antidiagonal.mp h
        exact Finset.mem_antidiagonal.mpr ⟨hFsupp.symm ▸ h1, hF'supp.symm ▸ h2, h3⟩
    rw [hanti]
    have hterm : ∀ ij ∈ Finset.antidiagonal y.isPWO_support y'.isPWO_support q,
        (LiftedPAdicHahnSeries.fromCoeff y.coeff y.isPWO_support').coeff ij.1
            * (LiftedPAdicHahnSeries.fromCoeff y'.coeff y'.isPWO_support').coeff ij.2
          = teichmuller p (y.coeff ij.1 * y'.coeff ij.2) := by
      intro ij _
      exact (map_mul (teichmuller p) _ _).symm
    rw [Finset.sum_congr rfl hterm]
    change _ = ((UP.mulPairs p y y' q).map fun uv => teichmuller p (uv.1 * uv.2)).sum
    rw [UP.mulPairs, Multiset.map_map]
    rfl
  -- the coefficients of the lifted defect, columnwise
  have hΔcoeff : ∀ q : ℚ, Δ.coeff q
      = colsum q - ∑ i ∈ Finset.Iic K,
          teichmuller p (teichDigit p i (colsum q)) * (p : ℤᶜᵘⁿ_[p]) ^ i := by
    intro q
    rw [hΔ]
    rw [HahnSeries.coeff_sub']
    simp only [Pi.sub_apply]
    rw [hFcol q]
    congr 1
    rw [HahnSeries.coeff_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [HahnSeries.coeff_single_mul, sub_zero, mul_comm]
    rfl
  -- columnwise divisibility from the Teichmüller digit expansion
  have hdvd : ∀ q, ((p : ℤᶜᵘⁿ_[p]) ^ (K + 1)) ∣ Δ.coeff q := by
    intro q
    rw [hΔcoeff q]
    exact sub_sum_teichDigit_dvd p (colsum q) K
  -- the defect vanishes below `v + v'`
  have hbelow : ∀ q < v + v', Δ.coeff q = 0 := by
    intro q hq
    have hcol0 : colsum q = 0 := by
      rw [hcolsum]
      simp [UP.mulPairs_eq_zero_of_lt hy hy' hq]
    rw [hΔcoeff q, hcol0]
    simp [teichDigit]
  -- the scalar `p`-power singles represent the `p`-powers of `𝕃_[p]`
  have hpow : ∀ i : ℕ, Ideal.Quotient.mk (NullSeriesIdeal p)
      (HahnSeries.single (0 : ℚ) ((p : ℤᶜᵘⁿ_[p]) ^ i) : LiftedPAdicHahnSeries p)
      = ((p : ℕ) : 𝕃_[p]) ^ i := by
    intro i
    rw [← HahnSeries.C_apply, map_pow, map_natCast, map_pow, map_natCast]
  -- each lifted summand represents `pⁱ·S(Dᵢ)`
  have hsummand : ∀ i : ℕ, Ideal.Quotient.mk (NullSeriesIdeal p)
      (HahnSeries.single (0 : ℚ) ((p : ℤᶜᵘⁿ_[p]) ^ i)
        * LiftedPAdicHahnSeries.fromCoeff (mulDigitSeries i y y').coeff
            (mulDigitSeries i y y').isPWO_support')
      = ((p : ℕ) : 𝕃_[p]) ^ i * shadow (mulDigitSeries i y y') := by
    intro i
    rw [map_mul, hpow i, ← shadow_eq_mkLp]
  -- identify the goal element with the class of `Δ`
  have hgoal : shadow y * shadow y'
      - ∑ i ∈ Finset.Iic K, ((p : ℕ) : 𝕃_[p]) ^ i * shadow (mulDigitSeries i y y')
      = Ideal.Quotient.mk (NullSeriesIdeal p) Δ := by
    rw [hΔ, map_sub, map_mul, map_sum]
    rw [← shadow_eq_mkLp, ← shadow_eq_mkLp]
    rw [Finset.sum_congr rfl fun i _ => hsummand i]
  rw [hgoal]
  exact_mod_cast le_val_mkLp_of_forall_pow_dvd_coeff hdvd hbelow

/-! ### Truncations of a product of shadows are UP -/

/-- **Truncations of a product of two shadows of UP series are UP**: choose the
digit-expansion depth to clear the cutoff; the truncation then agrees with the
truncation of a finite sum of shadows of UP series, and the sum engine applies. -/
theorem isUP_trunc_shadow_mul {y y' : HahnSeries ℚ (𝔽ᵃ_[p])}
    (hy : UP.IsUP p y) (hy' : UP.IsUP p y') (θ : ℤ) :
    UP.IsUP p (trunc (θ : ℚ) (shadow y * shadow y')) := by
  classical
  obtain ⟨v, hv⟩ := exists_int_support_bound [y, y']
  have hvy : ∀ q < (v : ℚ), y.coeff q = 0 := hv y (by simp)
  have hvy' : ∀ q < (v : ℚ), y'.coeff q = 0 := hv y' (by simp)
  set K : ℕ := (θ - 2 * v).toNat with hK
  have hθle : (θ : ℚ) ≤ (v : ℚ) + (v : ℚ) + ((K : ℚ) + 1) := by
    have hZ : θ ≤ 2 * v + ((θ - 2 * v).toNat : ℤ) + 1 := by omega
    have hQ : ((θ : ℤ) : ℚ) ≤ ((2 * v + ((θ - 2 * v).toNat : ℤ) + 1 : ℤ) : ℚ) := by
      exact_mod_cast hZ
    push_cast at hQ
    rw [hK]
    linarith
  have hval := le_val_shadow_mul_collapse y y' hvy hvy' K
  have hval' : (((θ : ℚ)) : WithTop ℚ) ≤ val p
      (shadow y * shadow y'
        - ∑ i ∈ Finset.Iic K, ((p : ℕ) : 𝕃_[p]) ^ i * shadow (mulDigitSeries i y y')) := by
    refine le_trans ?_ hval
    rw [WithTop.coe_le_coe]
    exact hθle
  rw [trunc_eq_of_le_val_sub hval']
  -- rewrite the digit sum as a sum of shadows over a list
  have hsum : (∑ i ∈ Finset.Iic K, ((p : ℕ) : 𝕃_[p]) ^ i * shadow (mulDigitSeries i y y'))
      = ((((Finset.Iic K).toList.map
          (fun i : ℕ => HahnSeries.single (i : ℚ) (1 : 𝔽ᵃ_[p]) * mulDigitSeries i y y')).map
            shadow)).sum := by
    rw [List.map_map]
    have h := Finset.sum_map_toList (Finset.Iic K)
      (fun i : ℕ => shadow (HahnSeries.single (i : ℚ) (1 : 𝔽ᵃ_[p]) * mulDigitSeries i y y'))
    rw [Function.comp_def, h]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [p_pow_mul_shadow]
  rw [hsum]
  refine isUP_trunc_list_sum_shadow _ ?_ θ
  intro u hu
  rw [List.mem_map] at hu
  obtain ⟨i, hi, rfl⟩ := hu
  have hone := UP.isUP_single_intCast p (i : ℤ) (1 : 𝔽ᵃ_[p])
  rw [Int.cast_natCast] at hone
  exact hone.mul (isUP_mulDigitSeries hy hy' i)

/-! ### `B'` is closed under multiplication -/

/-- **`B'` is closed under multiplication**: below a
cutoff `n`, replace both factors by the shadows of their truncations at cutoffs
shifted by the valuations; the product of shadows has UP truncations by the digit
expansion, and the approximation is at `p`-adic distance `≥ n`. -/
theorem IsTruncUP.mul {g g' : 𝕃_[p]} (hg : IsTruncUP g) (hg' : IsTruncUP g') :
    IsTruncUP (g * g') := by
  by_cases hg0 : g = 0
  · rw [hg0, zero_mul]
    exact isTruncUP_zero
  by_cases hg'0 : g' = 0
  · rw [hg'0, mul_zero]
    exact isTruncUP_zero
  obtain ⟨q₀, hq₀⟩ : ∃ q₀ : ℚ, val p g = (q₀ : WithTop ℚ) :=
    ⟨_, by rw [val_apply, dif_neg hg0]⟩
  obtain ⟨q₀', hq₀'⟩ : ∃ q₀' : ℚ, val p g' = (q₀' : WithTop ℚ) :=
    ⟨_, by rw [val_apply, dif_neg hg'0]⟩
  intro n
  set θ₁ : ℤ := ⌈(n : ℚ) - q₀'⌉ with hθ₁
  set θ₂ : ℤ := ⌈(n : ℚ) - q₀⌉ with hθ₂
  set y : HahnSeries ℚ (𝔽ᵃ_[p]) := trunc (θ₁ : ℚ) g with hy
  set y' : HahnSeries ℚ (𝔽ᵃ_[p]) := trunc (θ₂ : ℚ) g' with hy'
  have hyUP : UP.IsUP p y := hg.trunc_intCast θ₁
  have hy'UP : UP.IsUP p y' := hg'.trunc_intCast θ₂
  -- the product of shadows approximates `g g'` at depth `n`
  have hval : ((n : ℚ) : WithTop ℚ) ≤ val p (g * g' - shadow y * shadow y') := by
    have hid : g * g' - shadow y * shadow y'
        = (g - shadow y) * g' + shadow y * (g' - shadow y') := by
      ring
    rw [hid]
    refine (val p).map_le_add ?_ ?_
    · rw [(val p).map_mul, hq₀']
      have h1 := le_val_sub_shadow_trunc (θ₁ : ℚ) g
      calc ((n : ℚ) : WithTop ℚ)
          ≤ ((θ₁ : ℚ) : WithTop ℚ) + ((q₀' : ℚ) : WithTop ℚ) := by
            rw [← WithTop.coe_add, WithTop.coe_le_coe]
            have hceil := Int.le_ceil ((n : ℚ) - q₀')
            rw [← hθ₁] at hceil
            linarith
        _ ≤ val p (g - shadow y) + ((q₀' : ℚ) : WithTop ℚ) := by
            exact add_le_add h1 le_rfl
    · rw [(val p).map_mul]
      have h2 := le_val_sub_shadow_trunc (θ₂ : ℚ) g'
      have hSy : ((q₀ : ℚ) : WithTop ℚ) ≤ val p (shadow y) := by
        refine le_val_shadow_of_forall_coeff_eq_zero ?_
        intro q hq
        rw [hy]
        by_cases hqθ : q < (θ₁ : ℚ)
        · rw [coeff_trunc_of_lt hqθ]
          refine coeff_eq_zero_of_lt_val ?_
          rw [hq₀, WithTop.coe_lt_coe]
          exact hq
        · rw [coeff_trunc_of_le (not_lt.mp hqθ)]
      calc ((n : ℚ) : WithTop ℚ)
          ≤ ((q₀ : ℚ) : WithTop ℚ) + ((θ₂ : ℚ) : WithTop ℚ) := by
            rw [← WithTop.coe_add, WithTop.coe_le_coe]
            have hceil := Int.le_ceil ((n : ℚ) - q₀)
            rw [← hθ₂] at hceil
            linarith
        _ ≤ val p (shadow y) + val p (g' - shadow y') := add_le_add hSy h2
  rw [trunc_eq_of_le_val_sub hval]
  have h := isUP_trunc_shadow_mul hyUP hy'UP (n : ℤ)
  rwa [show (((n : ℤ) : ℚ)) = (n : ℚ) by push_cast; rfl] at h

/-! ### `B'` is a subring -/

theorem isTruncUP_one : IsTruncUP (1 : 𝕃_[p]) := by
  have hp0 := p_pow_eq_single (p := p) 0
  rw [pow_zero, Nat.cast_zero] at hp0
  have h1 : (1 : 𝕃_[p]) = shadow (HahnSeries.single (0 : ℚ) (1 : 𝔽ᵃ_[p])) := by
    rw [hp0]
    apply ext_coeff
    rw [coeff_single, coeff_shadow]
    funext r
    by_cases hr : r = 0
    · subst hr
      rw [if_pos rfl, HahnSeries.coeff_single_same]
    · rw [if_neg hr, HahnSeries.coeff_single_of_ne hr]
  rw [h1]
  have hUP : UP.IsUP p (HahnSeries.single (0 : ℚ) (1 : 𝔽ᵃ_[p])) := by
    have h := UP.isUP_single_intCast p (0 : ℤ) (1 : 𝔽ᵃ_[p])
    rwa [Int.cast_zero] at h
  exact isTruncUP_shadow hUP

/-- `B'` is closed under powers. -/
protected theorem IsTruncUP.pow {g : 𝕃_[p]} (hg : IsTruncUP g) :
    ∀ n : ℕ, IsTruncUP (g ^ n)
  | 0 => by
    rw [pow_zero]
    exact isTruncUP_one
  | n + 1 => by
    rw [pow_succ]
    exact (hg.pow n).mul hg

variable (p) in
/-- **`B'` as a subring of `𝕃_[p]`**: it contains every integer polynomial in
shadows of UP series. -/
noncomputable def truncUPSubring : Subring (𝕃_[p]) where
  carrier := {g | IsTruncUP g}
  zero_mem' := isTruncUP_zero
  one_mem' := isTruncUP_one
  add_mem' := fun h h' => h.add h'
  neg_mem' := fun h => h.neg
  mul_mem' := fun h h' => h.mul h'

@[simp] theorem mem_truncUPSubring {g : 𝕃_[p]} :
    g ∈ truncUPSubring p ↔ IsTruncUP g := Iff.rfl

end TrustworthyKedlaya.pAdicHahnSeries
