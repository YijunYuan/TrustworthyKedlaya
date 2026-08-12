/-
Copyright (c) 2026 Shanwen Wang, Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import TrustworthyKedlaya.PAdicHahnSeries

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
  and shifts positions by `q` (2.2(2) and 2.2(3) in one statement).

The remaining item of Lemma 2.2 — additivity of `Cₓ` at positions at or below both
valuations, 2.2(4) — is the next step of `lem:lp-coeff-calculus`.
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

end TrustworthyKedlaya.pAdicHahnSeries
