/-
Copyright (c) 2026 Shanwen Wang, Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import TrustworthyKedlaya.LpCoeff

/-!
# The shadow map `𝔽̄_p((t^ℚ)) → 𝕃_p` and its calculus

The comparison between equal and mixed characteristic runs through the **shadow map**
`S : 𝔽̄_p((t^ℚ)) → 𝕃_[p]` transporting a Hahn series to the `p`-adic Hahn series with the
same canonical coefficient function (`t ↦ p` on Teichmüller expansions).  This file
establishes its metric calculus:

- `TrustworthyKedlaya.pAdicHahnSeries.shadow`: the map itself (`fromCoeff` of the
  coefficient function);
- `val_mkLp_eq_of_isUnit_leading`: the **master valuation lemma** — a lifted series with
  unit leading coefficient at `q₀` has valuation exactly `q₀` in the quotient (both
  inequalities via `null_series_no_unit_leading`);
- `val_shadow_sub`: the shadow map is an **isometry**:
  `val (S y - S y') = orderTop (y - y')`;
- `val_p_eq_one`: the element `p ∈ 𝕃_[p]` has valuation `1` (the `t = p`
  identification: `single 1 1 - single 0 p` is a null series);
- `le_val_shadow_add_sub`: the **carry bound** — `S` is additive to first `p`-adic
  order: `val (S(y+y') - S y - S y') ≥ q₀ + 1` whenever the supports of `y` and `y'`
  only overlap at exponents `≥ q₀`.

Every route to `kedlaya_2017_theorem13_4` and `kedlaya_2001b_ordinal_bound`
(Kedlaya 2001b, Section 3; Kedlaya 2017, Section "mixed") factors through these
estimates: they drive the cross-characteristic Newton comparison
(`lem:roots-continuity`) and the congruence bookkeeping of both approximation
propositions.

## References

- K. S. Kedlaya, *Power series and p-adic algebraic closures*, J. Number Theory 89
  (2001) [Ked01b], Section 3.
-/

@[expose] public section

namespace TrustworthyKedlaya.pAdicHahnSeries

open WittVector

variable {p : ℕ} [hp : Fact (Nat.Prime p)]

/-! ### The shadow map -/

/-- The **shadow** of a Hahn series `y ∈ 𝔽̄_p((t^ℚ))`: the `p`-adic Hahn series with the
same canonical coefficient function (replace `t` by `p` in the Teichmüller expansion). -/
noncomputable def shadow (y : HahnSeries ℚ (𝔽ᵃ_[p])) : 𝕃_[p] :=
  fromCoeff y.coeff y.isPWO_support'

@[simp]
theorem coeff_shadow (y : HahnSeries ℚ (𝔽ᵃ_[p])) : (shadow y).coeff = y.coeff :=
  coeff_of_fromCoeff_eq_self _ _

theorem shadow_injective :
    Function.Injective (shadow : HahnSeries ℚ (𝔽ᵃ_[p]) → 𝕃_[p]) := by
  intro y y' h
  ext q
  have h1 := congrArg (fun z => coeff z q) h
  simpa only [coeff_shadow] using h1

/-- The shadow of a Hahn series as an element of the lifted ring: the Teichmüller lift
of the coefficient function. -/
theorem shadow_eq_mkLp (y : HahnSeries ℚ (𝔽ᵃ_[p])) :
    shadow y = Ideal.Quotient.mk (NullSeriesIdeal p)
      (LiftedPAdicHahnSeries.fromCoeff y.coeff y.isPWO_support') := rfl

/-! ### The master valuation lemma -/

/-- If all coefficients of a lifted series `Δ` below `q₀` vanish, the class of `Δ` in
`𝕃_[p]` has valuation at least `q₀`: the canonical expansion cannot begin below `q₀`,
else the difference from `Δ` would be a null series with a unit (Teichmüller) leading
coefficient. -/
theorem le_val_mkLp_of_coeff_eq_zero {Δ : LiftedPAdicHahnSeries p} {q₀ : ℚ}
    (hlead : ∀ q < q₀, Δ.coeff q = 0) :
    (q₀ : WithTop ℚ) ≤ val p (Ideal.Quotient.mk (NullSeriesIdeal p) Δ) := by
  set x : 𝕃_[p] := Ideal.Quotient.mk (NullSeriesIdeal p) Δ with hx
  by_cases hx0 : x = 0
  · rw [hx0, val_zero_eq_top]
    exact le_top
  · -- the difference between `Δ` and the canonical representative is a null series
    have hν : Δ - LiftedPAdicHahnSeries.fromCoeff x.coeff (support_IsPWO x)
        ∈ NullSeriesIdeal p := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub]
      have h2 : Ideal.Quotient.mk (NullSeriesIdeal p)
          (LiftedPAdicHahnSeries.fromCoeff x.coeff (support_IsPWO x)) = x :=
        fromCoeff_of_coeff_eq_self x
      rw [h2, ← hx, sub_self]
    rw [val_apply, dif_neg hx0]
    set m : ℚ := (support_IsPWO x).isWF.min (support_nonempty_of_nonzero p x hx0) with hm
    rw [WithTop.coe_le_coe]
    by_contra hlt
    push Not at hlt
    -- the null series has leading position `m < q₀` with coefficient `-[x.coeff m]`
    have hmmem : m ∈ Function.support x.coeff :=
      (support_IsPWO x).isWF.min_mem (support_nonempty_of_nonzero p x hx0)
    have hmne : x.coeff m ≠ 0 := hmmem
    refine null_series_no_unit_leading hν (q := m) ?_ ?_
    · have hcoeff : (Δ - LiftedPAdicHahnSeries.fromCoeff x.coeff (support_IsPWO x)).coeff m
          = -(teichmuller p (x.coeff m)) := by
        rw [HahnSeries.coeff_sub', Pi.sub_apply, hlead m hlt]
        change 0 - teichmuller p (x.coeff m) = _
        ring
      rw [hcoeff]
      have hunit : IsUnit (teichmuller p (x.coeff m)) := by
        simpa using teich_sub_isUnit (a := x.coeff m) (b := 0) hmne
      exact hunit.neg
    · intro q' hq'
      rw [HahnSeries.coeff_sub', Pi.sub_apply, hlead q' (hq'.trans hlt)]
      have hzero : x.coeff q' = 0 := by
        by_contra hne
        exact absurd ((support_IsPWO x).isWF.min_le
          (support_nonempty_of_nonzero p x hx0) hne) (not_le.mpr hq')
      change (0 : ℤᵘⁿ_[p]) - teichmuller p (x.coeff q') = 0
      rw [hzero]
      simp

/-- **Master valuation lemma**: a lifted series whose coefficients vanish below `q₀`
and whose coefficient at `q₀` is a unit represents a class of valuation exactly `q₀`. -/
theorem val_mkLp_eq_of_isUnit_leading {Δ : LiftedPAdicHahnSeries p} {q₀ : ℚ}
    (hunit : IsUnit (Δ.coeff q₀)) (hlead : ∀ q < q₀, Δ.coeff q = 0) :
    val p (Ideal.Quotient.mk (NullSeriesIdeal p) Δ) = (q₀ : WithTop ℚ) := by
  set x : 𝕃_[p] := Ideal.Quotient.mk (NullSeriesIdeal p) Δ with hx
  -- `x ≠ 0`: a null series cannot have a unit leading coefficient
  have hx0 : x ≠ 0 := by
    intro h0
    have hΔ : Δ ∈ NullSeriesIdeal p := by
      rwa [← Ideal.Quotient.eq_zero_iff_mem, ← hx]
    exact null_series_no_unit_leading hΔ hunit hlead
  have hν : Δ - LiftedPAdicHahnSeries.fromCoeff x.coeff (support_IsPWO x)
      ∈ NullSeriesIdeal p := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub]
    rw [show Ideal.Quotient.mk (NullSeriesIdeal p)
        (LiftedPAdicHahnSeries.fromCoeff x.coeff (support_IsPWO x)) = x from
      fromCoeff_of_coeff_eq_self x, ← hx, sub_self]
  have hge : (q₀ : WithTop ℚ) ≤ val p x := le_val_mkLp_of_coeff_eq_zero hlead
  rw [val_apply, dif_neg hx0] at hge ⊢
  set m : ℚ := (support_IsPWO x).isWF.min (support_nonempty_of_nonzero p x hx0) with hm
  rw [WithTop.coe_le_coe] at hge
  rw [WithTop.coe_inj]
  -- remains to rule out `q₀ < m`: the null series would lead at `q₀` with a unit
  rcases eq_or_lt_of_le hge with h | hlt
  · exact h.symm
  · exfalso
    refine null_series_no_unit_leading hν (q := q₀) ?_ ?_
    · have hzero : x.coeff q₀ = 0 := by
        by_contra hne
        exact absurd ((support_IsPWO x).isWF.min_le
          (support_nonempty_of_nonzero p x hx0) hne) (not_le.mpr hlt)
      have hcoeff : (Δ - LiftedPAdicHahnSeries.fromCoeff x.coeff (support_IsPWO x)).coeff q₀
          = Δ.coeff q₀ := by
        rw [HahnSeries.coeff_sub', Pi.sub_apply]
        change _ - teichmuller p (x.coeff q₀) = _
        rw [hzero]
        simp
      rwa [hcoeff]
    · intro q' hq'
      rw [HahnSeries.coeff_sub', Pi.sub_apply, hlead q' hq']
      have hzero : x.coeff q' = 0 := by
        by_contra hne
        exact absurd ((support_IsPWO x).isWF.min_le
          (support_nonempty_of_nonzero p x hx0) hne) (not_le.mpr (hq'.trans hlt))
      change (0 : ℤᵘⁿ_[p]) - teichmuller p (x.coeff q') = 0
      rw [hzero]
      simp

/-! ### The shadow map is an isometry -/

/-- **Isometry**: the valuation of a difference of shadows is the `t`-adic order of the
difference of the originals.  In particular the shadow map transports Cauchy-ness and
limits between `𝔽̄_p((t^ℚ))` and `𝕃_[p]`. -/
theorem val_shadow_sub (y y' : HahnSeries ℚ (𝔽ᵃ_[p])) :
    val p (shadow y - shadow y') = (y - y').orderTop := by
  by_cases h : y = y'
  · rw [h, sub_self, sub_self, val_zero_eq_top, HahnSeries.orderTop_zero]
  · have hne : y - y' ≠ 0 := sub_ne_zero.mpr h
    set q₀ : ℚ := (y - y').order with hq₀
    have horder : (y - y').orderTop = (q₀ : WithTop ℚ) :=
      (HahnSeries.order_eq_orderTop_of_ne_zero hne).symm
    -- the lifted difference has unit leading coefficient at `q₀`
    have hsub : shadow y - shadow y' = Ideal.Quotient.mk (NullSeriesIdeal p)
        (LiftedPAdicHahnSeries.fromCoeff y.coeff y.isPWO_support'
          - LiftedPAdicHahnSeries.fromCoeff y'.coeff y'.isPWO_support') := by
      rw [map_sub]
      rfl
    rw [hsub, horder]
    have hcoeffΔ : ∀ q, (LiftedPAdicHahnSeries.fromCoeff y.coeff y.isPWO_support'
        - LiftedPAdicHahnSeries.fromCoeff y'.coeff y'.isPWO_support').coeff q
        = teichmuller p (y.coeff q) - teichmuller p (y'.coeff q) := by
      intro q
      rw [HahnSeries.coeff_sub', Pi.sub_apply]
      rfl
    refine val_mkLp_eq_of_isUnit_leading ?_ ?_
    · rw [hcoeffΔ]
      have hq₀mem : (y - y').coeff q₀ ≠ 0 := HahnSeries.coeff_order_eq_zero.not.mpr hne
      rw [HahnSeries.coeff_sub', Pi.sub_apply, sub_ne_zero] at hq₀mem
      exact teich_sub_isUnit hq₀mem
    · intro q hq
      rw [hcoeffΔ]
      have hqz : (y - y').coeff q = 0 := by
        by_contra hne'
        have hmem : q ∈ (y - y').support := hne'
        exact absurd (HahnSeries.order_le_of_coeff_ne_zero hne') (not_le.mpr hq)
      rw [HahnSeries.coeff_sub', Pi.sub_apply, sub_eq_zero] at hqz
      rw [hqz, sub_self]

@[simp]
theorem shadow_zero : shadow (0 : HahnSeries ℚ (𝔽ᵃ_[p])) = 0 := by
  rw [shadow_eq_mkLp]
  have h : LiftedPAdicHahnSeries.fromCoeff (p := p)
      (0 : HahnSeries ℚ (𝔽ᵃ_[p])).coeff (0 : HahnSeries ℚ (𝔽ᵃ_[p])).isPWO_support' = 0 := by
    apply HahnSeries.ext
    funext q
    change teichmuller p ((0 : HahnSeries ℚ (𝔽ᵃ_[p])).coeff q) = 0
    rw [show (0 : HahnSeries ℚ (𝔽ᵃ_[p])).coeff q = 0 from rfl]
    exact WittVector.teichmuller_zero p
  rw [h, map_zero]

/-- The valuation of a single shadow is the `t`-adic order of the original. -/
theorem val_shadow (y : HahnSeries ℚ (𝔽ᵃ_[p])) :
    val p (shadow y) = y.orderTop := by
  have h := val_shadow_sub y 0
  rwa [shadow_zero, sub_zero, sub_zero] at h

/-! ### The element `p` has valuation one -/

open Filter Topology in
/-- The `t = p` identification: `single 1 1 - p` is a null series (its only integer
column carries `1·p¹ - p·p⁰ = 0`). -/
theorem single_one_sub_p_isNullSeries :
    IsNullSeries ((HahnSeries.single (1 : ℚ) (1 : ℤᵘⁿ_[p]))
      - (p : LiftedPAdicHahnSeries p)) := by
  set δ : LiftedPAdicHahnSeries p :=
    HahnSeries.single (1 : ℚ) (1 : ℤᵘⁿ_[p]) - (p : LiftedPAdicHahnSeries p) with hδ
  have hpcoeff : ∀ q : ℚ, (p : LiftedPAdicHahnSeries p).coeff q
      = if q = 0 then (p : ℤᵘⁿ_[p]) else 0 := by
    intro q
    rw [show (p : LiftedPAdicHahnSeries p)
        = HahnSeries.single (0 : ℚ) (p : ℤᵘⁿ_[p]) from by
      rw [← map_natCast (HahnSeries.C : ℤᵘⁿ_[p] →+* LiftedPAdicHahnSeries p) p]; rfl]
    rw [HahnSeries.coeff_single]
    simp
  have hδcoeff : ∀ q : ℚ, δ.coeff q
      = (if q = 1 then (1 : ℤᵘⁿ_[p]) else 0) - (if q = 0 then (p : ℤᵘⁿ_[p]) else 0) := by
    intro q
    rw [hδ, HahnSeries.coeff_sub', Pi.sub_apply, HahnSeries.coeff_single, hpcoeff]
    simp
  have hp0 : (p : ℤᵘⁿ_[p]) ≠ 0 := WittVector.p_nonzero p _
  intro g
  refine Tendsto.congr' ?_ tendsto_const_nhds
  rw [EventuallyEq, eventually_atTop]
  refine ⟨1, fun M hM => ?_⟩
  symm
  by_cases hg : ∃ n₀ : ℤ, g + (n₀ : ℚ) = 0
  · -- the integer column: the partial sum is `p^{n₀+1}·1 - p^{n₀}·p = 0` once `M ≥ 1`
    obtain ⟨n₀, hn₀⟩ := hg
    have hq0 : g + ((n₀ : ℤ) : ℚ) = 0 := hn₀
    have hq1 : g + (((n₀ + 1 : ℤ)) : ℚ) = 1 := by push_cast; linarith
    have hset : (finiteBelow δ g M).toFinset = ({n₀, n₀ + 1} : Finset ℤ) := by
      ext n
      simp only [Set.Finite.mem_toFinset, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨-, hne⟩
        rw [hδcoeff] at hne
        by_contra hcon
        push Not at hcon
        have h1 : g + (n : ℚ) ≠ 1 := by
          intro h
          have : (n : ℚ) = ((n₀ + 1 : ℤ) : ℚ) := by push_cast at hq1 ⊢; linarith
          exact hcon.2 (by exact_mod_cast this)
        have h0 : g + (n : ℚ) ≠ 0 := by
          intro h
          have : (n : ℚ) = ((n₀ : ℤ) : ℚ) := by linarith
          exact hcon.1 (by exact_mod_cast this)
        rw [if_neg h1, if_neg h0, sub_zero] at hne
        exact hne rfl
      · rintro (rfl | rfl)
        · constructor
          · rw [hq0]; exact_mod_cast Nat.zero_le M
          · rw [hδcoeff, if_neg (by rw [hq0]; norm_num), if_pos hq0]
            simpa using hp0
        · constructor
          · rw [hq1]; exact_mod_cast hM
          · rw [hδcoeff, if_pos hq1, if_neg (by rw [hq1]; norm_num)]
            simp
    rw [Finset.sum_coe_sort ((finiteBelow δ g M).toFinset)
      (fun m => (p : QpUn p) ^ (m : ℤ) * algebraMap (OQpUn p) (QpUn p) (δ.coeff (g + (m : ℚ))))]
    rw [hset, Finset.sum_pair (by omega : n₀ ≠ n₀ + 1)]
    rw [hδcoeff, hδcoeff, if_neg (by rw [hq0]; norm_num), if_pos hq0,
      if_pos hq1, if_neg (by rw [hq1]; norm_num)]
    rw [zero_sub, sub_zero, map_neg, map_one, mul_one]
    have hpQ : ((p : QpUn p)) ≠ 0 := by
      intro h
      exact (WittVector.p_nonzero p (𝔽ᵃ_[p]))
        (IsFractionRing.to_map_eq_zero_iff.mp (by push_cast at h ⊢; exact h))
    have halg : algebraMap (OQpUn p) (QpUn p) (p : ℤᵘⁿ_[p]) = (p : QpUn p) := by
      push_cast
      rfl
    rw [halg, zpow_add₀ hpQ n₀ 1, zpow_one]
    ring
  · -- no integer column: every coefficient in the column vanishes
    have hempty : ∀ n : ℤ, δ.coeff (g + n) = 0 := by
      intro n
      rw [hδcoeff]
      have h1 : g + (n : ℚ) ≠ 1 := by
        intro h
        exact hg ⟨n - 1, by push_cast; linarith⟩
      have h0 : g + (n : ℚ) ≠ 0 := fun h => hg ⟨n, h⟩
      rw [if_neg h1, if_neg h0, sub_zero]
    refine Finset.sum_eq_zero fun n _ => ?_
    rw [hempty n, map_zero, mul_zero]

/-- In `𝕃_[p]` the element `p` equals the class of `single 1 1`: `t` becomes `p`. -/
theorem mkLp_single_one :
    Ideal.Quotient.mk (NullSeriesIdeal p) (HahnSeries.single (1 : ℚ) (1 : ℤᵘⁿ_[p]))
      = (p : 𝕃_[p]) := by
  rw [← sub_eq_zero, ← map_natCast (Ideal.Quotient.mk (NullSeriesIdeal p)) p, ← map_sub,
    Ideal.Quotient.eq_zero_iff_mem]
  exact single_one_sub_p_isNullSeries

/-- The element `p ∈ 𝕃_[p]` has valuation `1`. -/
@[simp]
theorem val_p_eq_one : val p ((p : ℕ) : 𝕃_[p]) = (1 : ℚ) := by
  rw [← mkLp_single_one]
  refine val_mkLp_eq_of_isUnit_leading ?_ ?_
  · rw [HahnSeries.coeff_single, if_pos rfl]
    exact isUnit_one
  · intro q hq
    rw [HahnSeries.coeff_single, if_neg (by exact fun h => absurd h (ne_of_lt hq))]

/-! ### The carry bound: the shadow map is additive to first `p`-adic order -/

/-- The Teichmüller carry `[a+b] - [a] - [b]` is divisible by `p` in `W(𝔽̄_p)`. -/
theorem teichmuller_add_sub_mem_span (a b : 𝔽ᵃ_[p]) :
    teichmuller p (a + b) - teichmuller p a - teichmuller p b
      ∈ Ideal.span {(p : ℤᵘⁿ_[p])} := by
  have hEq : ∀ i < 1, (teichmuller p (a + b)).coeff i
      = (teichmuller p a + teichmuller p b).coeff i := by
    intro i hi
    interval_cases i
    rw [WittVector.teichmuller_coeff_zero, WittVector.add_coeff_zero,
      WittVector.teichmuller_coeff_zero, WittVector.teichmuller_coeff_zero]
  have hcoeff := (WittVector.le_coeff_eq_iff_le_sub_coeff_eq_zero (n := 1)).mp hEq
  have hmem := (WittVector.mem_span_p_pow_iff_le_coeff_eq_zero
    (teichmuller p (a + b) - (teichmuller p a + teichmuller p b)) 1).mpr hcoeff
  rw [pow_one] at hmem
  rwa [sub_sub]

/-- **Carry bound**: the shadow map is additive to first `p`-adic order.  If the
supports of `y` and `y'` only meet at exponents `≥ q₀`, then
`S(y + y') ≡ S(y) + S(y')` modulo valuation `q₀ + 1`: Teichmüller carries are
divisible by `p` and only occur where both coefficients are nonzero. -/
theorem le_val_shadow_add_sub (y y' : HahnSeries ℚ (𝔽ᵃ_[p])) (q₀ : ℚ)
    (hov : ∀ q, y.coeff q ≠ 0 → y'.coeff q ≠ 0 → q₀ ≤ q) :
    ((q₀ + 1 : ℚ) : WithTop ℚ) ≤ val p (shadow (y + y') - shadow y - shadow y') := by
  classical
  set Δ : LiftedPAdicHahnSeries p :=
    LiftedPAdicHahnSeries.fromCoeff (y + y').coeff (y + y').isPWO_support'
      - LiftedPAdicHahnSeries.fromCoeff y.coeff y.isPWO_support'
      - LiftedPAdicHahnSeries.fromCoeff y'.coeff y'.isPWO_support' with hΔ
  have hΔcoeff : ∀ q, Δ.coeff q
      = teichmuller p (y.coeff q + y'.coeff q) - teichmuller p (y.coeff q)
        - teichmuller p (y'.coeff q) := by
    intro q
    rw [hΔ, HahnSeries.coeff_sub', Pi.sub_apply, HahnSeries.coeff_sub', Pi.sub_apply]
    rfl
  -- coefficients vanish off the overlap and are divisible by `p` on it
  have hvanish : ∀ q, q < q₀ → Δ.coeff q = 0 := by
    intro q hq
    rw [hΔcoeff]
    by_cases hy : y.coeff q = 0
    · rw [hy, zero_add, WittVector.teichmuller_zero, sub_zero, sub_self]
    · have hy' : y'.coeff q = 0 := by
        by_contra hy'
        exact absurd (hov q hy hy') (not_le.mpr hq)
      rw [hy', add_zero, WittVector.teichmuller_zero, sub_zero, sub_self]
  have hdvd : ∀ q, ∃ wq : ℤᵘⁿ_[p],
      Δ.coeff q = (p : ℤᵘⁿ_[p]) * wq ∧ (Δ.coeff q = 0 → wq = 0) := by
    intro q
    by_cases h0 : Δ.coeff q = 0
    · exact ⟨0, by rw [h0, mul_zero], fun _ => rfl⟩
    · have h := teichmuller_add_sub_mem_span (p := p) (y.coeff q) (y'.coeff q)
      rw [Ideal.mem_span_singleton] at h
      obtain ⟨wq, hwq⟩ := h
      exact ⟨wq, by rw [hΔcoeff]; exact hwq, fun h' => absurd h' h0⟩
  -- extract the quotient series `Δ'` with `Δ = p • Δ'`
  choose w hw hw0 using hdvd
  have hwsupp : Function.support w ⊆ Δ.support := by
    intro q hq
    rw [Function.mem_support] at hq
    rw [HahnSeries.mem_support]
    intro h0
    exact hq (hw0 q h0)
  set Δ' : LiftedPAdicHahnSeries p := ⟨w, Δ.isPWO_support'.mono hwsupp⟩ with hΔ'
  have hΔeq : Δ = (p : ℕ) • Δ' := by
    apply HahnSeries.ext
    funext q
    rw [HahnSeries.coeff_smul']
    change Δ.coeff q = (p : ℕ) • w q
    rw [nsmul_eq_mul]
    exact hw q
  -- pass to the quotient and use `val(p) = 1` plus the master lower bound
  have hclass : shadow (y + y') - shadow y - shadow y'
      = Ideal.Quotient.mk (NullSeriesIdeal p) Δ := by
    rw [hΔ, map_sub, map_sub]
    rfl
  have hclass' : Ideal.Quotient.mk (NullSeriesIdeal p) Δ
      = ((p : ℕ) : 𝕃_[p]) * Ideal.Quotient.mk (NullSeriesIdeal p) Δ' := by
    rw [hΔeq, nsmul_eq_mul]
    rw [map_mul, map_natCast]
  rw [hclass, hclass', AddValuation.map_mul, val_p_eq_one]
  have hΔ'lead : ∀ q < q₀, Δ'.coeff q = 0 := by
    intro q hq
    change w q = 0
    exact hw0 q (hvanish q hq)
  have hge := le_val_mkLp_of_coeff_eq_zero (Δ := Δ') hΔ'lead
  calc ((q₀ + 1 : ℚ) : WithTop ℚ) = ((1 : ℚ) : WithTop ℚ) + ((q₀ : ℚ) : WithTop ℚ) := by
        rw [← WithTop.coe_add]
        congr 1
        ring
    _ ≤ ((1 : ℚ) : WithTop ℚ) + val p (Ideal.Quotient.mk (NullSeriesIdeal p) Δ') :=
        add_le_add le_rfl hge

/-! ### Second carry bounds: negation and multiplication

The shadow map is also multiplicative to first `p`-adic order (`lem:shadow-mul-carry`):
the Teichmüller map is multiplicative on the nose, so the carries of a product come only
from re-Teichmüllerizing the finite antidiagonal sums, each divisible by `p`.  The same
column bookkeeping bounds `S(-y) + S(y)`. -/

/-- The support of a lifted series built from a coefficient function is the support of
that function (the Teichmüller map is injective and sends `0` to `0`). -/
theorem support_fromCoeff (s : ℚ → 𝔽ᵃ_[p]) (hs : (Function.support s).IsPWO) :
    (LiftedPAdicHahnSeries.fromCoeff s hs).support = Function.support s := by
  ext q
  simp only [HahnSeries.mem_support, Function.mem_support]
  change teichmuller p (s q) ≠ 0 ↔ s q ≠ 0
  refine ⟨fun h h' => h (by rw [h', WittVector.teichmuller_zero p]), fun h h' => h ?_⟩
  exact (injective_teichmuller p) (by rw [h', WittVector.teichmuller_zero p])

/-- The Teichmüller carry of a negation: `[-a] + [a]` is divisible by `p` in `W(𝔽̄_p)`. -/
theorem teichmuller_neg_add_mem_span (a : 𝔽ᵃ_[p]) :
    teichmuller p (-a) + teichmuller p a ∈ Ideal.span {(p : ℤᵘⁿ_[p])} := by
  have h := teichmuller_add_sub_mem_span (p := p) (-a) a
  rw [neg_add_cancel, WittVector.teichmuller_zero] at h
  have h' := neg_mem h
  rw [zero_sub, neg_sub, sub_neg_eq_add] at h'
  rwa [add_comm] at h'

/-- The Teichmüller lift of a finite sum differs from the sum of the lifts by a
multiple of `p`: iterate the binary carry `teichmuller_add_sub_mem_span`. -/
theorem teichmuller_sum_sub_mem_span {ι : Type*} (s : Finset ι) (f : ι → 𝔽ᵃ_[p]) :
    teichmuller p (∑ i ∈ s, f i) - ∑ i ∈ s, teichmuller p (f i)
      ∈ Ideal.span {(p : ℤᵘⁿ_[p])} := by
  classical
  induction s using Finset.cons_induction with
  | empty =>
    simp only [Finset.sum_empty, WittVector.teichmuller_zero, sub_zero]
    exact Ideal.zero_mem _
  | cons a t ha ih =>
    rw [Finset.sum_cons, Finset.sum_cons]
    have h1 := teichmuller_add_sub_mem_span (p := p) (f a) (∑ i ∈ t, f i)
    have h2 := Ideal.add_mem _ h1 ih
    have heq : teichmuller p (f a + ∑ i ∈ t, f i) - teichmuller p (f a)
          - teichmuller p (∑ i ∈ t, f i)
        + (teichmuller p (∑ i ∈ t, f i) - ∑ i ∈ t, teichmuller p (f i))
        = teichmuller p (f a + ∑ i ∈ t, f i)
          - (teichmuller p (f a) + ∑ i ∈ t, teichmuller p (f i)) := by
      ring
    rwa [heq] at h2

/-- **Extraction principle**: a lifted series with all coefficients divisible by `p`,
vanishing below `q₀`, has class of valuation at least `q₀ + 1` in `𝕃_[p]`. -/
theorem le_val_mkLp_add_one_of_forall_mem_span {Δ : LiftedPAdicHahnSeries p} {q₀ : ℚ}
    (hvanish : ∀ q, q < q₀ → Δ.coeff q = 0)
    (hdvd : ∀ q, Δ.coeff q ∈ Ideal.span {(p : ℤᵘⁿ_[p])}) :
    ((q₀ + 1 : ℚ) : WithTop ℚ) ≤ val p (Ideal.Quotient.mk (NullSeriesIdeal p) Δ) := by
  classical
  have hdvd' : ∀ q, ∃ wq : ℤᵘⁿ_[p],
      Δ.coeff q = (p : ℤᵘⁿ_[p]) * wq ∧ (Δ.coeff q = 0 → wq = 0) := by
    intro q
    by_cases h0 : Δ.coeff q = 0
    · exact ⟨0, by rw [h0, mul_zero], fun _ => rfl⟩
    · have h := hdvd q
      rw [Ideal.mem_span_singleton] at h
      obtain ⟨wq, hwq⟩ := h
      exact ⟨wq, hwq, fun h' => absurd h' h0⟩
  choose w hw hw0 using hdvd'
  have hwsupp : Function.support w ⊆ Δ.support := by
    intro q hq
    rw [Function.mem_support] at hq
    rw [HahnSeries.mem_support]
    intro h0
    exact hq (hw0 q h0)
  set Δ' : LiftedPAdicHahnSeries p := ⟨w, Δ.isPWO_support'.mono hwsupp⟩ with hΔ'
  have hΔeq : Δ = (p : ℕ) • Δ' := by
    apply HahnSeries.ext
    funext q
    rw [HahnSeries.coeff_smul']
    change Δ.coeff q = (p : ℕ) • w q
    rw [nsmul_eq_mul]
    exact hw q
  have hclass : Ideal.Quotient.mk (NullSeriesIdeal p) Δ
      = ((p : ℕ) : 𝕃_[p]) * Ideal.Quotient.mk (NullSeriesIdeal p) Δ' := by
    rw [hΔeq, nsmul_eq_mul]
    rw [map_mul, map_natCast]
  rw [hclass, AddValuation.map_mul, val_p_eq_one]
  have hΔ'lead : ∀ q < q₀, Δ'.coeff q = 0 := by
    intro q hq
    change w q = 0
    exact hw0 q (hvanish q hq)
  have hge := le_val_mkLp_of_coeff_eq_zero (Δ := Δ') hΔ'lead
  calc ((q₀ + 1 : ℚ) : WithTop ℚ) = ((1 : ℚ) : WithTop ℚ) + ((q₀ : ℚ) : WithTop ℚ) := by
        rw [← WithTop.coe_add]
        congr 1
        ring
    _ ≤ ((1 : ℚ) : WithTop ℚ) + val p (Ideal.Quotient.mk (NullSeriesIdeal p) Δ') :=
        add_le_add le_rfl hge

/-- **Negation carry**: `val (S(-y) + S(y)) ≥ q₀ + 1` when `y` is supported at exponents
`≥ q₀`.  The column carries `[-y_q] + [y_q]` have vanishing zeroth Witt coordinate. -/
theorem le_val_shadow_neg_add (y : HahnSeries ℚ (𝔽ᵃ_[p])) (q₀ : ℚ)
    (hy : ∀ q, y.coeff q ≠ 0 → q₀ ≤ q) :
    ((q₀ + 1 : ℚ) : WithTop ℚ) ≤ val p (shadow (-y) + shadow y) := by
  classical
  set Δ : LiftedPAdicHahnSeries p :=
    LiftedPAdicHahnSeries.fromCoeff (-y).coeff (-y).isPWO_support'
      + LiftedPAdicHahnSeries.fromCoeff y.coeff y.isPWO_support' with hΔ
  have hΔcoeff : ∀ q, Δ.coeff q
      = teichmuller p (-(y.coeff q)) + teichmuller p (y.coeff q) := by
    intro q
    rw [hΔ, HahnSeries.coeff_add', Pi.add_apply]
    change teichmuller p ((-y).coeff q) + teichmuller p (y.coeff q) = _
    rw [HahnSeries.coeff_neg']
    rfl
  have hclass : shadow (-y) + shadow y = Ideal.Quotient.mk (NullSeriesIdeal p) Δ := by
    rw [hΔ, map_add]
    rfl
  rw [hclass]
  refine le_val_mkLp_add_one_of_forall_mem_span ?_ ?_
  · intro q hq
    rw [hΔcoeff]
    have h0 : y.coeff q = 0 := by
      by_contra hne
      exact absurd (hy q hne) (not_le.mpr hq)
    rw [h0, neg_zero, WittVector.teichmuller_zero, add_zero]
  · intro q
    rw [hΔcoeff]
    exact teichmuller_neg_add_mem_span (y.coeff q)

/-- **Multiplication carry**: the shadow map is multiplicative to first `p`-adic order.
If `y` and `y'` are supported at exponents `≥ a` and `≥ b` respectively, then
`val (S(y·y') - S(y)·S(y')) ≥ a + b + 1`: the Teichmüller map is multiplicative, so the
only carries come from re-Teichmüllerizing the antidiagonal sums, each divisible by `p`
and supported at exponents `≥ a + b`. -/
theorem le_val_shadow_mul_sub (y y' : HahnSeries ℚ (𝔽ᵃ_[p])) (a b : ℚ)
    (hy : ∀ q, y.coeff q ≠ 0 → a ≤ q) (hy' : ∀ q, y'.coeff q ≠ 0 → b ≤ q) :
    ((a + b + 1 : ℚ) : WithTop ℚ) ≤ val p (shadow (y * y') - shadow y * shadow y') := by
  classical
  set fx := LiftedPAdicHahnSeries.fromCoeff y.coeff y.isPWO_support' with hfx
  set fy := LiftedPAdicHahnSeries.fromCoeff y'.coeff y'.isPWO_support' with hfy
  set Δ : LiftedPAdicHahnSeries p :=
    LiftedPAdicHahnSeries.fromCoeff (y * y').coeff (y * y').isPWO_support' - fx * fy
    with hΔ
  have h_supp_fx : fx.support = y.support := support_fromCoeff _ _
  have h_supp_fy : fy.support = y'.support := support_fromCoeff _ _
  -- the two antidiagonals coincide
  have h_anti : ∀ q, Finset.antidiagonal fx.isPWO_support fy.isPWO_support q
      = Finset.antidiagonal y.isPWO_support y'.isPWO_support q := by
    intro q
    ext ⟨i, j⟩
    simp only [Finset.mem_antidiagonal]
    rw [h_supp_fx, h_supp_fy]
  have hΔcoeff : ∀ q, Δ.coeff q
      = teichmuller p ((y * y').coeff q)
        - ∑ ij ∈ Finset.antidiagonal y.isPWO_support y'.isPWO_support q,
            teichmuller p (y.coeff ij.1 * y'.coeff ij.2) := by
    intro q
    rw [hΔ, HahnSeries.coeff_sub', Pi.sub_apply]
    congr 1
    rw [HahnSeries.coeff_mul, h_anti q]
    refine Finset.sum_congr rfl fun ij _ => ?_
    change teichmuller p (y.coeff ij.1) * teichmuller p (y'.coeff ij.2) = _
    rw [← map_mul]
  have hclass : shadow (y * y') - shadow y * shadow y'
      = Ideal.Quotient.mk (NullSeriesIdeal p) Δ := by
    rw [hΔ, map_sub, map_mul]
    rfl
  rw [hclass]
  refine le_val_mkLp_add_one_of_forall_mem_span ?_ ?_
  · -- coefficients vanish below `a + b`: the antidiagonal is empty there
    intro q hq
    have hempty : Finset.antidiagonal y.isPWO_support y'.isPWO_support q = ∅ := by
      ext ⟨i, j⟩
      simp only [Finset.mem_antidiagonal, Finset.notMem_empty, iff_false, not_and]
      intro hi hj hij
      have hia : a ≤ i := hy i hi
      have hjb : b ≤ j := hy' j hj
      have : a + b ≤ q := by rw [← hij]; exact add_le_add hia hjb
      exact absurd this (not_le.mpr hq)
    have hmul0 : (y * y').coeff q = 0 := by
      rw [HahnSeries.coeff_mul, hempty, Finset.sum_empty]
    rw [hΔcoeff, hmul0, WittVector.teichmuller_zero, hempty, Finset.sum_empty, sub_zero]
  · -- every coefficient is a Teichmüller carry of a finite sum, divisible by `p`
    intro q
    rw [hΔcoeff, HahnSeries.coeff_mul]
    exact teichmuller_sum_sub_mem_span _ _

end TrustworthyKedlaya.pAdicHahnSeries
