/-
Copyright (c) 2026 Shanwen Wang, Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import TrustworthyKedlaya.Lp.Basic

/-!
# Coefficient calculus for `𝕃_p`

The transfinite Newton algorithm (Wang-Yuan, Section 2; Kedlaya 2001b, Proposition 2)
manipulates elements of `𝕃_[p]` through their canonical Teichmüller expansions
`α = ∑ₓ [αₓ] pˣ`: the coefficient maps `Cₓ(α) = α.coeff x`, the valuation
`v_p = val p` (the support minimum), and one-term series `[a] p^q`.  This file
provides that calculus (Wang-Yuan, Lemma 2.2):

- `TrustworthyKedlaya.pAdicHahnSeries.coeff_eq_zero_of_lt_val` /
  `coeff_val_ne_zero` / `val_le_of_coeff_ne_zero`: coefficients below the
  valuation vanish, and the coefficient at the valuation does not (2.2(1));
- `TrustworthyKedlaya.pAdicHahnSeries.single`: the one-term series `[a] p^q`,
  with `coeff_single_mul`: multiplying by `[a] p^q` scales coefficients by `a`
  and shifts positions by `q` (2.2(2) and 2.2(3) in one statement);
- `TrustworthyKedlaya.pAdicHahnSeries.coeff_add_of_le_val` / `coeff_sub_of_le_val` /
  `coeff_sum_of_le_val`: at a position at or below the valuations of all operands,
  the coefficient map is additive (2.2(4)).

It also records two facts about the valuation of a class represented by a lifted series:

- `TrustworthyKedlaya.pAdicHahnSeries.val_mkLp_eq_of_isUnit_leading`: the **master
  valuation lemma** — a lifted series with unit leading coefficient at `q₀` has valuation
  exactly `q₀` in the quotient (both inequalities via `null_series_no_unit_leading`);
- `TrustworthyKedlaya.pAdicHahnSeries.val_p_eq_one`: the element `p ∈ 𝕃_[p]` has
  valuation `1` (the `t = p` identification: `single 1 1 - p` is a null series).
-/

@[expose] public section

namespace TrustworthyKedlaya.pAdicHahnSeries

open WittVector

variable {p : ℕ} [hp : Fact (Nat.Prime p)]

/-! ### The valuation and the coefficient function -/

theorem mem_support_iff (x : 𝕃_[p]) (q : ℚ) : q ∈ x.support ↔ x.coeff q ≠ 0 :=
  Function.mem_support

/-- The coefficient function of the zero series vanishes. -/
theorem coeff_zero_eq : (0 : 𝕃_[p]).coeff = 0 := by
  ext q
  by_cases hq : q ∈ (0 : 𝕃_[p]).support
  · exact (eq_zero_iff_coeff_zero (0 : 𝕃_[p])).mp rfl q hq
  · rw [mem_support_iff] at hq
    push Not at hq
    simpa using hq

open Classical in
/-- The defining formula of the valuation `val p`: the support minimum for nonzero
series, `⊤` for zero. -/
theorem val_apply (x : 𝕃_[p]) :
    val p x = if h : x = 0 then (⊤ : WithTop ℚ)
      else ((support_IsPWO x).isWF.min (support_nonempty_of_nonzero p x h) : WithTop ℚ) :=
  rfl

@[simp]
theorem val_zero_eq_top : val p (0 : 𝕃_[p]) = ⊤ := by
  rw [val_apply, dif_pos rfl]

theorem val_eq_top_iff {x : 𝕃_[p]} : val p x = ⊤ ↔ x = 0 := by
  constructor
  · intro h
    by_contra hx
    rw [val_apply, dif_neg hx] at h
    exact WithTop.coe_ne_top h
  · rintro rfl
    exact val_zero_eq_top

/-- **Coefficients below the valuation vanish** (Wang-Yuan, Lemma 2.2(1)). -/
theorem coeff_eq_zero_of_lt_val {x : 𝕃_[p]} {q : ℚ} (h : (q : WithTop ℚ) < val p x) :
    x.coeff q = 0 := by
  by_cases hx : x = 0
  · rw [hx, coeff_zero_eq]
    rfl
  · rw [val_apply, dif_neg hx] at h
    by_contra hne
    have hmem : q ∈ x.support := (mem_support_iff x q).mpr hne
    have hle := (support_IsPWO x).isWF.min_le (support_nonempty_of_nonzero p x hx) hmem
    exact absurd (WithTop.coe_lt_coe.mp h) (not_lt.mpr hle)

/-- **The coefficient at the valuation is nonzero** (Wang-Yuan, Lemma 2.2(1)). -/
theorem coeff_val_ne_zero {x : 𝕃_[p]} {q : ℚ} (h : val p x = (q : WithTop ℚ)) :
    x.coeff q ≠ 0 := by
  have hx : x ≠ 0 := by
    rintro rfl
    rw [val_zero_eq_top] at h
    exact WithTop.top_ne_coe h
  rw [val_apply, dif_neg hx] at h
  have hq : (support_IsPWO x).isWF.min (support_nonempty_of_nonzero p x hx) = q :=
    WithTop.coe_injective h
  have hmem := (support_IsPWO x).isWF.min_mem (support_nonempty_of_nonzero p x hx)
  rw [hq] at hmem
  exact (mem_support_iff x q).mp hmem

/-- A nonzero coefficient bounds the valuation from above. -/
theorem val_le_of_coeff_ne_zero {x : 𝕃_[p]} {q : ℚ} (h : x.coeff q ≠ 0) :
    val p x ≤ (q : WithTop ℚ) := by
  by_contra hlt
  push Not at hlt
  exact h (coeff_eq_zero_of_lt_val hlt)

/-! ### One-term series and the shift-and-scale rule -/

/-- The one-term `p`-adic Hahn series `[a] p^q` (Teichmüller digit `a` at position
`q`). -/
noncomputable def single (q : ℚ) (a : Fpbar p) : 𝕃_[p] :=
  fromCoeff (fun r => if r = q then a else 0) (by
    refine Set.Finite.isPWO (Set.Finite.subset (Set.finite_singleton q) ?_)
    intro r hr
    rw [Function.mem_support] at hr
    by_contra hrq
    rw [if_neg (by simpa using hrq)] at hr
    exact hr rfl)

@[simp]
theorem coeff_single (q : ℚ) (a : Fpbar p) :
    (single (p := p) q a).coeff = fun r => if r = q then a else 0 :=
  coeff_of_fromCoeff_eq_self _ _

/-- The lifted representative of `single q a` is the Hahn-series single term with
Teichmüller coefficient. -/
theorem lifted_fromCoeff_single (q : ℚ) (a : Fpbar p)
    (h : (Function.support fun r => if r = q then a else 0).IsPWO) :
    LiftedPAdicHahnSeries.fromCoeff (p := p) (fun r => if r = q then a else 0) h
      = HahnSeries.single q (teichmuller p a) := by
  apply HahnSeries.ext
  funext r
  change teichmuller p (if r = q then a else 0) = (HahnSeries.single q (teichmuller p a)).coeff r
  rw [HahnSeries.coeff_single]
  split
  · rfl
  · exact WittVector.teichmuller_zero p

/-- **Shift-and-scale** (Wang-Yuan, Lemma 2.2(2)-(3)): multiplying by the one-term
series `[a] p^q` multiplies every coefficient by `a` and shifts its position by `q`. -/
theorem coeff_single_mul (q : ℚ) (a : Fpbar p) (x : 𝕃_[p]) (r : ℚ) :
    (single q a * x).coeff r = a * x.coeff (r - q) := by
  -- the shifted-and-scaled coefficient function, with its well-ordered support
  have hs : (Function.support fun r => a * x.coeff (r - q)).IsPWO := by
    have himg : (Function.support fun r => a * x.coeff (r - q))
        ⊆ (fun u => u + q) '' Function.support x.coeff := by
      intro r hr
      rw [Function.mem_support] at hr
      exact ⟨r - q, fun h0 => hr (by rw [h0, mul_zero]), by ring⟩
    exact ((support_IsPWO x).image_of_monotone
      (fun u v huv => by simpa using add_le_add_right huv q)).mono himg
  -- compare the two series through their canonical lifted representatives
  have hkey : single q a * x = fromCoeff (fun r => a * x.coeff (r - q)) hs := by
    conv_lhs => rw [← fromCoeff_of_coeff_eq_self x]
    change fromCoeff (fun r => if r = q then a else 0) _ * fromCoeff x.coeff _ = _
    simp only [fromCoeff]
    rw [← map_mul, lifted_fromCoeff_single]
    congr 1
    apply HahnSeries.ext
    funext r
    change (HahnSeries.single q (teichmuller p a)
        * LiftedPAdicHahnSeries.fromCoeff x.coeff (support_IsPWO x)).coeff r
      = teichmuller p (a * x.coeff (r - q))
    have hmul := HahnSeries.coeff_single_mul_add (r := teichmuller p a)
      (x := LiftedPAdicHahnSeries.fromCoeff x.coeff (support_IsPWO x))
      (a := r - q) (b := q)
    rw [show r - q + q = r by ring] at hmul
    rw [hmul, map_mul]
    rfl
  rw [hkey, coeff_of_fromCoeff_eq_self]

/-- Multiplying by a Teichmüller constant scales all coefficients
(Wang-Yuan, Lemma 2.2(3)). -/
theorem coeff_teichmuller_mul (a : Fpbar p) (x : 𝕃_[p]) (r : ℚ) :
    (single 0 a * x).coeff r = a * x.coeff r := by
  rw [coeff_single_mul, sub_zero]

/-- Multiplying by `p^q` shifts all coefficients (Wang-Yuan, Lemma 2.2(2)). -/
theorem coeff_ppow_mul (q : ℚ) (x : 𝕃_[p]) (r : ℚ) :
    (single q 1 * x).coeff r = x.coeff (r - q) := by
  rw [coeff_single_mul, one_mul]

/-- Two `p`-adic Hahn series with the same canonical coefficient function are equal. -/
theorem ext_coeff {x y : 𝕃_[p]} (h : x.coeff = y.coeff) : x = y := by
  have key : ∀ (s t : ℚ → Fpbar p) (hs : (Function.support s).IsPWO)
      (ht : (Function.support t).IsPWO), s = t → fromCoeff s hs = fromCoeff t ht := by
    rintro s t hs ht rfl
    rfl
  rw [← fromCoeff_of_coeff_eq_self x, ← fromCoeff_of_coeff_eq_self y]
  exact key _ _ _ _ h

/-- One-term series multiply by adding positions and multiplying digits:
`[a]p^q · [b]p^r = [ab]p^(q+r)`. -/
theorem single_mul_single (q r : ℚ) (a b : Fpbar p) :
    single q a * single (p := p) r b = single (q + r) (a * b) := by
  apply ext_coeff
  funext u
  rw [coeff_single_mul, coeff_single, coeff_single]
  dsimp only
  by_cases hu : u = q + r
  · rw [if_pos (by rw [hu]; ring), if_pos hu]
  · rw [if_neg (fun hc : u - q = r => hu (by linarith)), if_neg hu, mul_zero]

/-- The one-term series `[1]p^0` is the multiplicative unit. -/
theorem single_zero_one : single (p := p) 0 1 = 1 := by
  rw [single, fromCoeff, lifted_fromCoeff_single, map_one (WittVector.teichmuller p),
    HahnSeries.single_zero_one, map_one]

/-- Powers of one-term series: `([a]p^q)^n = [aⁿ]p^(nq)`. -/
theorem single_pow (q : ℚ) (a : Fpbar p) (n : ℕ) :
    single (p := p) q a ^ n = single (n * q) (a ^ n) := by
  induction n with
  | zero => rw [pow_zero, pow_zero, Nat.cast_zero, zero_mul, single_zero_one]
  | succ n ih =>
    rw [pow_succ, pow_succ, ih, single_mul_single]
    congr 1
    push_cast
    ring

/-- The one-term series with zero digit is zero. -/
theorem single_zero (q : ℚ) : single (p := p) q 0 = 0 := by
  apply ext_coeff
  funext r
  rw [coeff_single, coeff_zero_eq]
  simp

/-- The valuation of a one-term series is its position (Wang-Yuan, Lemma 2.2). -/
theorem val_single (q : ℚ) {a : Fpbar p} (ha : a ≠ 0) :
    val p (single (p := p) q a) = (q : WithTop ℚ) := by
  have hcoeff : (single (p := p) q a).coeff = fun r => if r = q then a else 0 :=
    coeff_single q a
  have hne : single (p := p) q a ≠ 0 := by
    intro h
    rw [h, coeff_zero_eq] at hcoeff
    have := congrFun hcoeff q
    simp at this
    exact ha this.symm
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp (fun h => hne (val_eq_top_iff.mp h))
  have hmc := coeff_val_ne_zero hm.symm
  rw [hcoeff] at hmc
  dsimp only at hmc
  by_cases hmq : m = q
  · rw [← hm, hmq]
  · rw [if_neg hmq] at hmc
    exact absurd rfl hmc

/-- The valuation of a one-term series is at least its position (no nonzero-digit
hypothesis: the zero digit gives the zero series, of valuation `⊤`). -/
theorem le_val_single (q : ℚ) (a : Fpbar p) :
    (q : WithTop ℚ) ≤ val p (single (p := p) q a) := by
  rcases eq_or_ne a 0 with rfl | ha
  · rw [single_zero, val_zero_eq_top]
    exact le_top
  · rw [val_single q ha]

/-! ### Additivity at dominated positions -/

/-- **Additivity of the coefficient maps** (Wang-Yuan, Lemma 2.2(4)): at a position at or
below both valuations, the coefficient of a sum is the sum of the coefficients.

The sum `f_x + f_y` of the canonical lifted representatives represents `x + y` but need
not be canonical; the defect `Δ = f_x + f_y - f_{x+y}` is a null series vanishing strictly
below `q`.  If additivity failed at `q`, the coefficient `[x_q] + [y_q] - [(x+y)_q]` of
`Δ` at `q` would have nonzero Witt coefficient `0`, hence be a unit — contradicting
`null_series_no_unit_leading`. -/
theorem coeff_add_of_le_val {x y : 𝕃_[p]} {q : ℚ}
    (hx : (q : WithTop ℚ) ≤ val p x) (hy : (q : WithTop ℚ) ≤ val p y) :
    (x + y).coeff q = x.coeff q + y.coeff q := by
  by_contra hne
  set fx : LiftedPAdicHahnSeries p :=
    LiftedPAdicHahnSeries.fromCoeff x.coeff (support_IsPWO x) with hfx_def
  set fy : LiftedPAdicHahnSeries p :=
    LiftedPAdicHahnSeries.fromCoeff y.coeff (support_IsPWO y) with hfy_def
  set fz : LiftedPAdicHahnSeries p :=
    LiftedPAdicHahnSeries.fromCoeff (x + y).coeff (support_IsPWO (x + y)) with hfz_def
  -- `Δ = fx + fy - fz` is a null series: its class in `𝕃_[p]` is `x + y - (x + y) = 0`
  have hΔ : fx + fy - fz ∈ NullSeriesIdeal p := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_add]
    have h1 : Ideal.Quotient.mk (NullSeriesIdeal p) fx = x := fromCoeff_of_coeff_eq_self x
    have h2 : Ideal.Quotient.mk (NullSeriesIdeal p) fy = y := fromCoeff_of_coeff_eq_self y
    have h3 : Ideal.Quotient.mk (NullSeriesIdeal p) fz = x + y :=
      fromCoeff_of_coeff_eq_self (x + y)
    rw [h1, h2, h3, sub_self]
  -- `Δ` vanishes strictly below `q`: all three coefficient functions do
  have hbelow : ∀ q' < q, (fx + fy - fz).coeff q' = 0 := by
    intro q' hq'
    have hq'x : x.coeff q' = 0 :=
      coeff_eq_zero_of_lt_val (lt_of_lt_of_le (WithTop.coe_lt_coe.mpr hq') hx)
    have hq'y : y.coeff q' = 0 :=
      coeff_eq_zero_of_lt_val (lt_of_lt_of_le (WithTop.coe_lt_coe.mpr hq') hy)
    have hq'z : (x + y).coeff q' = 0 :=
      coeff_eq_zero_of_lt_val
        (lt_of_lt_of_le (WithTop.coe_lt_coe.mpr hq') ((val p).map_le_add hx hy))
    rw [HahnSeries.coeff_sub, HahnSeries.coeff_add]
    change teichmuller p (x.coeff q') + teichmuller p (y.coeff q')
        - teichmuller p ((x + y).coeff q') = 0
    rw [hq'x, hq'y, hq'z, WittVector.teichmuller_zero]
    simp
  -- if additivity failed at `q`, the coefficient of `Δ` there would be a unit
  have hq_unit : IsUnit ((fx + fy - fz).coeff q) := by
    apply WittVector.isUnit_of_coeff_zero_ne_zero
    intro h0
    apply hne
    have hcoeff : (fx + fy - fz).coeff q
        = teichmuller p (x.coeff q) + teichmuller p (y.coeff q)
          - teichmuller p ((x + y).coeff q) := by
      rw [HahnSeries.coeff_sub, HahnSeries.coeff_add]; rfl
    rw [hcoeff, ← WittVector.constantCoeff_apply, map_sub, map_add,
      WittVector.constantCoeff_apply, WittVector.constantCoeff_apply,
      WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero,
      WittVector.teichmuller_coeff_zero, WittVector.teichmuller_coeff_zero] at h0
    exact (sub_eq_zero.mp h0).symm
  exact null_series_no_unit_leading hΔ hq_unit hbelow

/-- Subtraction rule (Wang-Yuan, Lemma 2.2(4), the `−` case). -/
theorem coeff_sub_of_le_val {x y : 𝕃_[p]} {q : ℚ}
    (hx : (q : WithTop ℚ) ≤ val p x) (hy : (q : WithTop ℚ) ≤ val p y) :
    (x - y).coeff q = x.coeff q - y.coeff q := by
  have hxy : (q : WithTop ℚ) ≤ val p (x - y) :=
    le_trans (le_min hx hy) ((val p).map_sub x y)
  have h := coeff_add_of_le_val hxy hy
  rw [sub_add_cancel] at h
  exact eq_sub_of_add_eq h.symm

/-- Iterated additivity (Wang-Yuan, Lemma 2.2(4)): at a position at or below the
valuations of all summands, the coefficient of a finite sum is the sum of the
coefficients. -/
theorem coeff_sum_of_le_val {ι : Type*} {s : Finset ι} {f : ι → 𝕃_[p]} {q : ℚ}
    (h : ∀ i ∈ s, (q : WithTop ℚ) ≤ val p (f i)) :
    (∑ i ∈ s, f i).coeff q = ∑ i ∈ s, (f i).coeff q := by
  induction s using Finset.cons_induction with
  | empty => simp [coeff_zero_eq]
  | cons a s ha ih =>
    rw [Finset.sum_cons, Finset.sum_cons,
      coeff_add_of_le_val (h a (Finset.mem_cons_self a s))
        ((val p).map_le_sum fun i hi => h i (Finset.mem_cons_of_mem hi)),
      ih fun i hi => h i (Finset.mem_cons_of_mem hi)]

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
      change (0 : ℤᶜᵘⁿ_[p]) - teichmuller p (x.coeff q') = 0
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
      change (0 : ℤᶜᵘⁿ_[p]) - teichmuller p (x.coeff q') = 0
      rw [hzero]
      simp

/-! ### The element `p` has valuation one -/

open Filter Topology in
/-- The `t = p` identification: `single 1 1 - p` is a null series (its only integer
column carries `1·p¹ - p·p⁰ = 0`). -/
theorem single_one_sub_p_isNullSeries :
    IsNullSeries ((HahnSeries.single (1 : ℚ) (1 : ℤᶜᵘⁿ_[p]))
      - (p : LiftedPAdicHahnSeries p)) := by
  set δ : LiftedPAdicHahnSeries p :=
    HahnSeries.single (1 : ℚ) (1 : ℤᶜᵘⁿ_[p]) - (p : LiftedPAdicHahnSeries p) with hδ
  have hpcoeff : ∀ q : ℚ, (p : LiftedPAdicHahnSeries p).coeff q
      = if q = 0 then (p : ℤᶜᵘⁿ_[p]) else 0 := by
    intro q
    rw [show (p : LiftedPAdicHahnSeries p)
        = HahnSeries.single (0 : ℚ) (p : ℤᶜᵘⁿ_[p]) from by
      rw [← map_natCast (HahnSeries.C : ℤᶜᵘⁿ_[p] →+* LiftedPAdicHahnSeries p) p]; rfl]
    rw [HahnSeries.coeff_single]
    simp
  have hδcoeff : ∀ q : ℚ, δ.coeff q
      = (if q = 1 then (1 : ℤᶜᵘⁿ_[p]) else 0) - (if q = 0 then (p : ℤᶜᵘⁿ_[p]) else 0) := by
    intro q
    rw [hδ, HahnSeries.coeff_sub', Pi.sub_apply, HahnSeries.coeff_single, hpcoeff]
    simp
  have hp0 : (p : ℤᶜᵘⁿ_[p]) ≠ 0 := WittVector.p_nonzero p _
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
      (fun m => (p : QpCUn p) ^ (m : ℤ) * algebraMap (OQpCUn p) (QpCUn p) (δ.coeff (g + (m : ℚ))))]
    rw [hset, Finset.sum_pair (by omega : n₀ ≠ n₀ + 1)]
    rw [hδcoeff, hδcoeff, if_neg (by rw [hq0]; norm_num), if_pos hq0,
      if_pos hq1, if_neg (by rw [hq1]; norm_num)]
    rw [zero_sub, sub_zero, map_neg, map_one, mul_one]
    have hpQ : ((p : QpCUn p)) ≠ 0 := by
      intro h
      exact (WittVector.p_nonzero p (𝔽ᵃ_[p]))
        (IsFractionRing.to_map_eq_zero_iff.mp (by push_cast at h ⊢; exact h))
    have halg : algebraMap (OQpCUn p) (QpCUn p) (p : ℤᶜᵘⁿ_[p]) = (p : QpCUn p) := by
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
    Ideal.Quotient.mk (NullSeriesIdeal p) (HahnSeries.single (1 : ℚ) (1 : ℤᶜᵘⁿ_[p]))
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

end TrustworthyKedlaya.pAdicHahnSeries
