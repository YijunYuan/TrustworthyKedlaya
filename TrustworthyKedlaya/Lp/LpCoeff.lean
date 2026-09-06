/-
Copyright (c) 2026 Shanwen Wang, Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import TrustworthyKedlaya.Lp.PAdicHahnSeries

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

end TrustworthyKedlaya.pAdicHahnSeries
