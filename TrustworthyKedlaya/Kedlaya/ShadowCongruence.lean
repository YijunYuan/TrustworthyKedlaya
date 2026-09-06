/-
Copyright (c) 2026 Shanwen Wang, Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import TrustworthyKedlaya.Kedlaya.ShadowCalculus
public import TrustworthyKedlaya.Kedlaya.RootMatching
public import Mathlib.RingTheory.HahnSeries.Valuation

/-!
# Roots vary continuously across characteristics

The shadow map `S : 𝔽̄_p((t^ℚ)) → 𝕃_[p]` is neither additive nor multiplicative, but its
carries are `p`-divisible.  This file transports that calculus from elements to the
coefficients of split polynomials and derives Kedlaya's continuity of roots:

- `exists_sum_le_val_coeff_shadow`: the
  coefficients of `∏_{y ∈ Y}(X - S(y))` agree with the shadows of the coefficients of
  `∏_{y ∈ Y}(X - y)` to depth `σ_{n-i}(W) + 1`, where `W` is the valuation multiset of
  `Y` and `σ_j` the sum of the `j` smallest elements (encoded by minimal witnesses as
  in `TrustworthyKedlaya.Kedlaya.RootMatching`);
- `roots_continuity_forward` / `roots_continuity_reverse` (Kedlaya 2001b): if the
  shadows of the coefficients of the split monic
  `P = ∏_{y ∈ Y}(X - y)` are within `σ_{n-i}(W) + k` of the coefficients of the split
  monic `Q = ∏_{z ∈ Z}(X - z)` (`k ≤ 1`, equal valuation multisets), then each root of
  either polynomial of valuation `s` matches a root of the other, with
  `val (S(y) - z) ≥ s + k/m` for `m` the multiplicity of `s`.  Both directions follow
  from `exists_root_sub_valuation_le` applied to the pair `(∏(X - S(y)), Q)` over
  `𝕃_[p]`.

The `WithTop`-valued wrappers `le_val_shadow_mul_sub'`, `le_val_shadow_neg_add'`,
`le_val_shadow_add_sub'` restate the carry bounds of `ShadowCalculus` with `orderTop`
floors, absorbing the zero-series cases.

## References

- K. S. Kedlaya, *Power series and p-adic algebraic closures*, J. Number Theory 89
  (2001) [Ked01b], Section 3.
-/

@[expose] public section

namespace TrustworthyKedlaya.pAdicHahnSeries

open WittVector Polynomial HahnSeries

variable {p : ℕ} [hp : Fact (Nat.Prime p)]

/-- The shadow of the constant series `1` is `1`. -/
@[simp]
theorem shadow_one : shadow (1 : HahnSeries ℚ (𝔽ᵃ_[p])) = 1 := by
  rw [shadow_eq_mkLp]
  have h : LiftedPAdicHahnSeries.fromCoeff (p := p)
      (1 : HahnSeries ℚ (𝔽ᵃ_[p])).coeff (1 : HahnSeries ℚ (𝔽ᵃ_[p])).isPWO_support' = 1 := by
    apply HahnSeries.ext
    funext q
    change teichmuller p ((1 : HahnSeries ℚ (𝔽ᵃ_[p])).coeff q)
      = (1 : LiftedPAdicHahnSeries p).coeff q
    rw [HahnSeries.coeff_one, HahnSeries.coeff_one]
    split
    · exact map_one _
    · exact WittVector.teichmuller_zero p
  rw [h, map_one]

/-! ### `WithTop`-valued carry bounds -/

/-- Multiplication carry with `orderTop` floors:
`val (S(y·y') - S(y)·S(y')) ≥ orderTop y + orderTop y' + 1`. -/
theorem le_val_shadow_mul_sub' (y y' : HahnSeries ℚ (𝔽ᵃ_[p])) :
    y.orderTop + y'.orderTop + 1 ≤ val p (shadow (y * y') - shadow y * shadow y') := by
  by_cases hy : y = 0
  · simp [hy]
  by_cases hy' : y' = 0
  · simp [hy']
  obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.mp (orderTop_ne_top.mpr hy)
  obtain ⟨b, hb⟩ := WithTop.ne_top_iff_exists.mp (orderTop_ne_top.mpr hy')
  have h := le_val_shadow_mul_sub y y' a b
    (fun q hq => by
      rw [← WithTop.coe_le_coe (α := ℚ), ha]; exact orderTop_le_of_coeff_ne_zero hq)
    (fun q hq => by
      rw [← WithTop.coe_le_coe (α := ℚ), hb]; exact orderTop_le_of_coeff_ne_zero hq)
  rw [← ha, ← hb]
  calc ((a : WithTop ℚ)) + (b : WithTop ℚ) + 1
      = ((a + b + 1 : ℚ) : WithTop ℚ) := by norm_cast
    _ ≤ _ := h

/-- Negation carry with an `orderTop` floor:
`val (S(-y) + S(y)) ≥ orderTop y + 1`. -/
theorem le_val_shadow_neg_add' (y : HahnSeries ℚ (𝔽ᵃ_[p])) :
    y.orderTop + 1 ≤ val p (shadow (-y) + shadow y) := by
  by_cases hy : y = 0
  · simp [hy]
  obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.mp (orderTop_ne_top.mpr hy)
  have h := le_val_shadow_neg_add y a
    (fun q hq => by
      rw [← WithTop.coe_le_coe (α := ℚ), ha]; exact orderTop_le_of_coeff_ne_zero hq)
  rw [← ha]
  calc ((a : WithTop ℚ)) + 1 = ((a + 1 : ℚ) : WithTop ℚ) := by norm_cast
    _ ≤ _ := h

/-- Addition carry with `orderTop` floors:
`val (S(y+y') - S(y) - S(y')) ≥ min (orderTop y) (orderTop y') + 1`. -/
theorem le_val_shadow_add_sub' (y y' : HahnSeries ℚ (𝔽ᵃ_[p])) :
    min y.orderTop y'.orderTop + 1 ≤ val p (shadow (y + y') - shadow y - shadow y') := by
  rcases le_total y.orderTop y'.orderTop with hmin | hmin
  · rw [min_eq_left hmin]
    by_cases hy : y = 0
    · simp [hy]
    obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.mp (orderTop_ne_top.mpr hy)
    have h := le_val_shadow_add_sub y y' a
      (fun q hq _ => by
        rw [← WithTop.coe_le_coe (α := ℚ), ha]; exact orderTop_le_of_coeff_ne_zero hq)
    rw [← ha]
    calc ((a : WithTop ℚ)) + 1 = ((a + 1 : ℚ) : WithTop ℚ) := by norm_cast
      _ ≤ _ := h
  · rw [min_eq_right hmin]
    by_cases hy' : y' = 0
    · simp [hy']
    obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.mp (orderTop_ne_top.mpr hy')
    have h := le_val_shadow_add_sub y y' a
      (fun q _ hq => by
        rw [← WithTop.coe_le_coe (α := ℚ), ha]; exact orderTop_le_of_coeff_ne_zero hq)
    rw [← ha]
    calc ((a : WithTop ℚ)) + 1 = ((a + 1 : ℚ) : WithTop ℚ) := by norm_cast
      _ ≤ _ := h

/-! ### Shadowing the coefficients of a split polynomial -/

/-- **Shadowing the coefficients of a split polynomial**: the coefficients of
`∏_{y ∈ Y}(X - S(y))` agree with the shadows of the coefficients of `∏_{y ∈ Y}(X - y)`
to depth `σ_{n-i}(W) + 1`, where `W = Y.map orderTop` and `σ` is delivered by a minimal
witness `T`.

Induction on `Y`, comparing `(X - S(y₀))·R` with the shadow of `(X - y₀)·P`
coefficientwise: the difference decomposes into the inductive difference, a
`S(y₀)`-multiple of it, and negation/multiplication/addition Teichmüller carries, each
of valuation at least `σ_{n+1-i}(W') + 1` by the carry bounds and the coefficient
floors. -/
theorem exists_sum_le_val_coeff_shadow (Y : Multiset (HahnSeries ℚ (𝔽ᵃ_[p]))) (i : ℕ) :
    ∃ T ≤ Y.map HahnSeries.orderTop, T.card = Y.card - i ∧
      T.sum + 1 ≤ val p (((Y.map fun y => X - Polynomial.C (shadow y)).prod).coeff i
        - shadow (((Y.map fun y => X - Polynomial.C y).prod).coeff i)) := by
  classical
  induction Y using Multiset.induction_on generalizing i with
  | empty =>
    simp only [Multiset.map_zero, Multiset.prod_zero, Multiset.card_zero]
    refine ⟨0, le_rfl, by rw [Multiset.card_zero, Nat.zero_sub], ?_⟩
    by_cases h0 : i = 0
    · subst h0
      rw [Polynomial.coeff_one_zero, Polynomial.coeff_one_zero, shadow_one, sub_self,
        (val p).map_zero]
      exact le_top
    · rw [Polynomial.coeff_one, Polynomial.coeff_one, if_neg h0, if_neg h0, shadow_zero,
        sub_zero, (val p).map_zero]
      exact le_top
  | cons y₀ Y ih =>
    by_cases hbig : (y₀ ::ₘ Y).card ≤ i
    · -- at or above the common degree the coefficients are `1` or `0` on both sides
      refine ⟨0, Multiset.zero_le _, by rw [Multiset.card_zero, Nat.sub_eq_zero_of_le hbig], ?_⟩
      have hPmonic : (((y₀ ::ₘ Y).map fun y => X - Polynomial.C y).prod).Monic :=
        monic_multiset_prod_of_monic _ _ fun y _ => monic_X_sub_C y
      have hRmap : ((y₀ ::ₘ Y).map fun y => X - Polynomial.C (shadow y))
          = (((y₀ ::ₘ Y).map shadow).map fun z => X - Polynomial.C z) := by
        rw [Multiset.map_map]
        rfl
      have hRmonic : (((y₀ ::ₘ Y).map fun y => X - Polynomial.C (shadow y)).prod).Monic := by
        rw [hRmap]
        exact monic_multiset_prod_of_monic _ _ fun z _ => monic_X_sub_C z
      have hPdeg : (((y₀ ::ₘ Y).map fun y => X - Polynomial.C y).prod).natDegree
          = (y₀ ::ₘ Y).card :=
        natDegree_multiset_prod_X_sub_C_eq_card _
      have hRdeg : (((y₀ ::ₘ Y).map fun y => X - Polynomial.C (shadow y)).prod).natDegree
          = (y₀ ::ₘ Y).card := by
        rw [hRmap, natDegree_multiset_prod_X_sub_C_eq_card, Multiset.card_map]
      rcases eq_or_lt_of_le hbig with heq | hlt
      · have hPc : (((y₀ ::ₘ Y).map fun y => X - Polynomial.C y).prod).coeff i = 1 := by
          rw [← heq, ← hPdeg]
          exact hPmonic.coeff_natDegree
        have hRc : (((y₀ ::ₘ Y).map fun y => X - Polynomial.C (shadow y)).prod).coeff i = 1 := by
          rw [← heq, ← hRdeg]
          exact hRmonic.coeff_natDegree
        rw [hPc, hRc, shadow_one, sub_self, (val p).map_zero]
        exact le_top
      · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hRdeg]; exact hlt),
          Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hPdeg]; exact hlt),
          shadow_zero, sub_zero, (val p).map_zero]
        exact le_top
    · -- below the degree: the four-bracket carry decomposition
      have hilt : i < Y.card + 1 := by
        have := Nat.lt_of_not_le hbig
        rwa [Multiset.card_cons] at this
      simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons]
      set Pp : Polynomial (HahnSeries ℚ (𝔽ᵃ_[p])) := (Y.map fun y => X - Polynomial.C y).prod
        with hPp
      set Rp : Polynomial (𝕃_[p]) := (Y.map fun y => X - Polynomial.C (shadow y)).prod with hRp
      obtain ⟨Tm, hTmle, hTmcard, hTmmin⟩ :=
        exists_min_sum_powersetCard (y₀.orderTop ::ₘ Y.map HahnSeries.orderTop)
          (j := Y.card + 1 - i)
          (by rw [Multiset.card_cons, Multiset.card_map]; exact Nat.sub_le _ _)
      refine ⟨Tm, hTmle, hTmcard, ?_⟩
      have hmap : Y.map ⇑(HahnSeries.addVal ℚ (𝔽ᵃ_[p])) = Y.map HahnSeries.orderTop :=
        Multiset.map_congr rfl fun y _ => HahnSeries.addVal_apply
      have horder_mul : ∀ a b : HahnSeries ℚ (𝔽ᵃ_[p]),
          (a * b).orderTop = a.orderTop + b.orderTop := by
        intro a b
        rw [← HahnSeries.addVal_apply (x := a * b), ← HahnSeries.addVal_apply (x := a),
          ← HahnSeries.addVal_apply (x := b)]
        exact (HahnSeries.addVal ℚ (𝔽ᵃ_[p])).map_mul a b
      cases i with
      | zero =>
        obtain ⟨T₄, hT₄le, hT₄card, _, hT₄sum⟩ :=
          exists_sum_le_v_coeff_prod_X_sub_C (HahnSeries.addVal ℚ (𝔽ᵃ_[p])) Y
            (i := 0) (Nat.zero_le _)
        rw [hmap] at hT₄le
        rw [HahnSeries.addVal_apply] at hT₄sum
        obtain ⟨T₁, hT₁le, hT₁card, hT₁sum⟩ := ih 0
        have hP' : ((X - Polynomial.C y₀) * Pp).coeff 0 = -(y₀ * Pp.coeff 0) := by
          rw [Polynomial.mul_coeff_zero, Polynomial.coeff_sub, Polynomial.coeff_X_zero,
            Polynomial.coeff_C_zero, zero_sub, neg_mul]
        have hR' : ((X - Polynomial.C (shadow y₀)) * Rp).coeff 0 = -(shadow y₀ * Rp.coeff 0) := by
          rw [Polynomial.mul_coeff_zero, Polynomial.coeff_sub, Polynomial.coeff_X_zero,
            Polynomial.coeff_C_zero, zero_sub, neg_mul]
        have h1 : Tm.sum + 1 ≤ val p (shadow y₀ * (Rp.coeff 0 - shadow (Pp.coeff 0))) := by
          rw [(val p).map_mul, val_shadow]
          have h := hTmmin (y₀.orderTop ::ₘ T₁) (Multiset.cons_le_cons _ hT₁le)
            (by rw [Multiset.card_cons, hT₁card]; omega)
          rw [Multiset.sum_cons] at h
          calc Tm.sum + 1 ≤ (y₀.orderTop + T₁.sum) + 1 := add_le_add h le_rfl
            _ = y₀.orderTop + (T₁.sum + 1) := by rw [add_assoc]
            _ ≤ _ := add_le_add le_rfl hT₁sum
        have h2 : Tm.sum + 1
            ≤ val p (shadow y₀ * shadow (Pp.coeff 0) - shadow (y₀ * Pp.coeff 0)) := by
          rw [(val p).map_sub_swap]
          refine le_trans ?_ (le_val_shadow_mul_sub' y₀ (Pp.coeff 0))
          have h := hTmmin (y₀.orderTop ::ₘ T₄) (Multiset.cons_le_cons _ hT₄le)
            (by rw [Multiset.card_cons, hT₄card]; omega)
          rw [Multiset.sum_cons] at h
          exact add_le_add (le_trans h (add_le_add le_rfl hT₄sum)) le_rfl
        have h3 : Tm.sum + 1
            ≤ val p (shadow (-(y₀ * Pp.coeff 0)) + shadow (y₀ * Pp.coeff 0)) := by
          refine le_trans ?_ (le_val_shadow_neg_add' (y₀ * Pp.coeff 0))
          rw [horder_mul]
          have h := hTmmin (y₀.orderTop ::ₘ T₄) (Multiset.cons_le_cons _ hT₄le)
            (by rw [Multiset.card_cons, hT₄card]; omega)
          rw [Multiset.sum_cons] at h
          exact add_le_add (le_trans h (add_le_add le_rfl hT₄sum)) le_rfl
        have hdiff : ((X - Polynomial.C (shadow y₀)) * Rp).coeff 0
              - shadow (((X - Polynomial.C y₀) * Pp).coeff 0)
            = -(shadow y₀ * (Rp.coeff 0 - shadow (Pp.coeff 0)))
              - (shadow y₀ * shadow (Pp.coeff 0) - shadow (y₀ * Pp.coeff 0))
              - (shadow (-(y₀ * Pp.coeff 0)) + shadow (y₀ * Pp.coeff 0)) := by
          rw [hR', hP']
          ring
        rw [hdiff]
        refine (val p).map_le_sub ((val p).map_le_sub ?_ h2) h3
        rw [(val p).map_neg]
        exact h1
      | succ j =>
        have hjn : j + 1 ≤ Y.card := by omega
        obtain ⟨T₄, hT₄le, hT₄card, _, hT₄sum⟩ :=
          exists_sum_le_v_coeff_prod_X_sub_C (HahnSeries.addVal ℚ (𝔽ᵃ_[p])) Y
            (i := j) (le_trans (Nat.le_succ j) hjn)
        obtain ⟨T₃, hT₃le, hT₃card, _, hT₃sum⟩ :=
          exists_sum_le_v_coeff_prod_X_sub_C (HahnSeries.addVal ℚ (𝔽ᵃ_[p])) Y
            (i := j + 1) hjn
        rw [hmap] at hT₄le hT₃le
        rw [HahnSeries.addVal_apply] at hT₄sum hT₃sum
        obtain ⟨T₁, hT₁le, hT₁card, hT₁sum⟩ := ih j
        obtain ⟨T₂, hT₂le, hT₂card, hT₂sum⟩ := ih (j + 1)
        have hP' : ((X - Polynomial.C y₀) * Pp).coeff (j + 1)
            = Pp.coeff j + -(y₀ * Pp.coeff (j + 1)) := by
          rw [sub_mul, Polynomial.coeff_sub, Polynomial.coeff_X_mul, Polynomial.coeff_C_mul,
            sub_eq_add_neg]
        have hR' : ((X - Polynomial.C (shadow y₀)) * Rp).coeff (j + 1)
            = Rp.coeff j - shadow y₀ * Rp.coeff (j + 1) := by
          rw [sub_mul, Polynomial.coeff_sub, Polynomial.coeff_X_mul, Polynomial.coeff_C_mul]
        have h1 : Tm.sum + 1 ≤ val p (Rp.coeff j - shadow (Pp.coeff j)) :=
          le_trans (add_le_add (hTmmin T₁ (le_trans hT₁le (Multiset.le_cons_self _ _))
            (by rw [hT₁card]; omega)) le_rfl) hT₁sum
        have h2 : Tm.sum + 1
            ≤ val p (shadow y₀ * (Rp.coeff (j + 1) - shadow (Pp.coeff (j + 1)))) := by
          rw [(val p).map_mul, val_shadow]
          have h := hTmmin (y₀.orderTop ::ₘ T₂) (Multiset.cons_le_cons _ hT₂le)
            (by rw [Multiset.card_cons, hT₂card]; omega)
          rw [Multiset.sum_cons] at h
          calc Tm.sum + 1 ≤ (y₀.orderTop + T₂.sum) + 1 := add_le_add h le_rfl
            _ = y₀.orderTop + (T₂.sum + 1) := by rw [add_assoc]
            _ ≤ _ := add_le_add le_rfl hT₂sum
        have h3 : Tm.sum + 1
            ≤ val p (shadow y₀ * shadow (Pp.coeff (j + 1)) - shadow (y₀ * Pp.coeff (j + 1))) := by
          rw [(val p).map_sub_swap]
          refine le_trans ?_ (le_val_shadow_mul_sub' y₀ (Pp.coeff (j + 1)))
          have h := hTmmin (y₀.orderTop ::ₘ T₃) (Multiset.cons_le_cons _ hT₃le)
            (by rw [Multiset.card_cons, hT₃card]; omega)
          rw [Multiset.sum_cons] at h
          exact add_le_add (le_trans h (add_le_add le_rfl hT₃sum)) le_rfl
        have h4 : Tm.sum + 1 ≤ val p
            ((shadow (Pp.coeff j + -(y₀ * Pp.coeff (j + 1))) - shadow (Pp.coeff j)
                - shadow (-(y₀ * Pp.coeff (j + 1))))
              + (shadow (-(y₀ * Pp.coeff (j + 1))) + shadow (y₀ * Pp.coeff (j + 1)))) := by
          refine (val p).map_le_add ?_ ?_
          · refine le_trans ?_
              (le_val_shadow_add_sub' (Pp.coeff j) (-(y₀ * Pp.coeff (j + 1))))
            have hw : Tm.sum
                ≤ min (Pp.coeff j).orderTop (-(y₀ * Pp.coeff (j + 1))).orderTop := by
              refine le_min ?_ ?_
              · exact le_trans (hTmmin T₄ (le_trans hT₄le (Multiset.le_cons_self _ _))
                  (by rw [hT₄card]; omega)) hT₄sum
              · rw [HahnSeries.orderTop_neg, horder_mul]
                have h := hTmmin (y₀.orderTop ::ₘ T₃) (Multiset.cons_le_cons _ hT₃le)
                  (by rw [Multiset.card_cons, hT₃card]; omega)
                rw [Multiset.sum_cons] at h
                exact le_trans h (add_le_add le_rfl hT₃sum)
            exact add_le_add hw le_rfl
          · refine le_trans ?_ (le_val_shadow_neg_add' (y₀ * Pp.coeff (j + 1)))
            rw [horder_mul]
            have h := hTmmin (y₀.orderTop ::ₘ T₃) (Multiset.cons_le_cons _ hT₃le)
              (by rw [Multiset.card_cons, hT₃card]; omega)
            rw [Multiset.sum_cons] at h
            exact add_le_add (le_trans h (add_le_add le_rfl hT₃sum)) le_rfl
        have hdiff : ((X - Polynomial.C (shadow y₀)) * Rp).coeff (j + 1)
              - shadow (((X - Polynomial.C y₀) * Pp).coeff (j + 1))
            = (Rp.coeff j - shadow (Pp.coeff j))
              - shadow y₀ * (Rp.coeff (j + 1) - shadow (Pp.coeff (j + 1)))
              - (shadow y₀ * shadow (Pp.coeff (j + 1)) - shadow (y₀ * Pp.coeff (j + 1)))
              - ((shadow (Pp.coeff j + -(y₀ * Pp.coeff (j + 1))) - shadow (Pp.coeff j)
                  - shadow (-(y₀ * Pp.coeff (j + 1))))
                + (shadow (-(y₀ * Pp.coeff (j + 1))) + shadow (y₀ * Pp.coeff (j + 1)))) := by
          rw [hR', hP']
          ring
        rw [hdiff]
        exact (val p).map_le_sub ((val p).map_le_sub ((val p).map_le_sub h1 h2) h3) h4

/-! ### Roots vary continuously across characteristics -/

section RootsContinuity

variable (Y : Multiset (HahnSeries ℚ (𝔽ᵃ_[p]))) (Z : Multiset (𝕃_[p]))

/-- The combined coefficientwise congruence: if the shadows of the coefficients of
`P = ∏_{y ∈ Y}(X - y)` are within `σ_{n-i}(W) + k` of the coefficients of
`Q = ∏_{z ∈ Z}(X - z)`, with `k ≤ 1`, then so are the coefficients of
`R = ∏_{y ∈ Y}(X - S(y))` — the shadow-symmetric congruence absorbs the difference. -/
theorem exists_sum_le_val_coeff_sub_of_shadow_congruence
    {k : ℚ} (hk1 : k ≤ 1)
    (hcong : ∀ i < Y.card, ∃ T ≤ Y.map HahnSeries.orderTop, T.card = Y.card - i ∧
      T.sum + (k : WithTop ℚ) ≤ val p
        (shadow (((Y.map fun y => X - Polynomial.C y).prod).coeff i)
          - ((Z.map fun z => X - Polynomial.C z).prod).coeff i))
    {i : ℕ} (hi : i < Y.card) :
    ∃ T ≤ Y.map HahnSeries.orderTop, T.card = Y.card - i ∧
      T.sum + (k : WithTop ℚ) ≤ val p
        ((((Y.map fun y => X - Polynomial.C (shadow y)).prod)
          - ((Z.map fun z => X - Polynomial.C z).prod)).coeff i) := by
  classical
  obtain ⟨T₀, hT₀le, hT₀card, hT₀min⟩ :=
    exists_min_sum_powersetCard (Y.map HahnSeries.orderTop) (j := Y.card - i)
      (by rw [Multiset.card_map]; exact Nat.sub_le _ _)
  refine ⟨T₀, hT₀le, hT₀card, ?_⟩
  obtain ⟨T₁, hT₁le, hT₁card, hT₁sum⟩ := exists_sum_le_val_coeff_shadow Y i
  obtain ⟨T₂, hT₂le, hT₂card, hT₂sum⟩ := hcong i hi
  rw [Polynomial.coeff_sub]
  have hsplit : ((Y.map fun y => X - Polynomial.C (shadow y)).prod).coeff i
        - ((Z.map fun z => X - Polynomial.C z).prod).coeff i
      = (((Y.map fun y => X - Polynomial.C (shadow y)).prod).coeff i
          - shadow (((Y.map fun y => X - Polynomial.C y).prod).coeff i))
        + (shadow (((Y.map fun y => X - Polynomial.C y).prod).coeff i)
          - ((Z.map fun z => X - Polynomial.C z).prod).coeff i) := by
    ring
  rw [hsplit]
  refine (val p).map_le_add ?_ ?_
  · refine le_trans ?_ hT₁sum
    refine le_trans (add_le_add (hT₀min T₁ hT₁le (by rw [hT₁card])) le_rfl) ?_
    exact add_le_add le_rfl (by exact_mod_cast hk1)
  · exact le_trans (add_le_add (hT₀min T₂ hT₂le (by rw [hT₂card])) le_rfl) hT₂sum

/-- **Roots vary continuously across characteristics, forward direction**
(Kedlaya 2001b, the continuity-of-roots lemma): under the
normalized coefficient congruence to depth `σ_{n-i}(W) + k`, every root `y` of
`P = ∏_{y ∈ Y}(X - y)` of valuation `s` has a companion root `z` of
`Q = ∏_{z ∈ Z}(X - z)` with `val z = s` and `val (S(y) - z) ≥ s + k/m`, where `m` is
the multiplicity of `s` in the common valuation multiset. -/
theorem roots_continuity_forward
    (hW : Y.map HahnSeries.orderTop = Z.map (val p))
    {k : ℚ} (hk1 : k ≤ 1)
    (hcong : ∀ i < Y.card, ∃ T ≤ Y.map HahnSeries.orderTop, T.card = Y.card - i ∧
      T.sum + (k : WithTop ℚ) ≤ val p
        (shadow (((Y.map fun y => X - Polynomial.C y).prod).coeff i)
          - ((Z.map fun z => X - Polynomial.C z).prod).coeff i))
    {y : HahnSeries ℚ (𝔽ᵃ_[p])} (hy : y ∈ Y) {s : ℚ} (hs : y.orderTop = (s : WithTop ℚ)) :
    ∃ z ∈ Z, val p z = (s : WithTop ℚ) ∧
      ((s + k / ((Y.map HahnSeries.orderTop).count ((s : WithTop ℚ)) : ℚ) : ℚ) : WithTop ℚ)
        ≤ val p (shadow y - z) := by
  classical
  have hmapshadow : (Y.map shadow).map (val p) = Y.map HahnSeries.orderTop := by
    rw [Multiset.map_map]
    exact Multiset.map_congr rfl fun y _ => val_shadow y
  have hRmap : ((Y.map shadow).map fun u => X - Polynomial.C u)
      = Y.map fun y => X - Polynomial.C (shadow y) := by
    rw [Multiset.map_map]
    rfl
  have h := exists_root_sub_valuation_le (val p) (Y.map shadow) Z
    (by rw [hmapshadow, hW])
    (k := k)
    (fun i hi => by
      rw [Multiset.card_map] at hi ⊢
      rw [hmapshadow, hRmap]
      exact exists_sum_le_val_coeff_sub_of_shadow_congruence Y Z hk1 hcong hi)
    (u := shadow y) (Multiset.mem_map_of_mem shadow hy)
    (s := s) (by rw [val_shadow, hs])
  obtain ⟨z, hzZ, hzval, hzbound⟩ := h
  refine ⟨z, hzZ, hzval, ?_⟩
  rwa [hmapshadow] at hzbound

/-- **Roots vary continuously across characteristics, reverse direction**: every root
`z` of `Q` of valuation `s` has a companion root `y` of `P` with `orderTop y = s` and
`val (S(y) - z) ≥ s + k/m`. -/
theorem roots_continuity_reverse
    (hW : Y.map HahnSeries.orderTop = Z.map (val p))
    {k : ℚ} (hk1 : k ≤ 1)
    (hcong : ∀ i < Y.card, ∃ T ≤ Y.map HahnSeries.orderTop, T.card = Y.card - i ∧
      T.sum + (k : WithTop ℚ) ≤ val p
        (shadow (((Y.map fun y => X - Polynomial.C y).prod).coeff i)
          - ((Z.map fun z => X - Polynomial.C z).prod).coeff i))
    {z : 𝕃_[p]} (hz : z ∈ Z) {s : ℚ} (hs : val p z = (s : WithTop ℚ)) :
    ∃ y ∈ Y, y.orderTop = (s : WithTop ℚ) ∧
      ((s + k / ((Y.map HahnSeries.orderTop).count ((s : WithTop ℚ)) : ℚ) : ℚ) : WithTop ℚ)
        ≤ val p (shadow y - z) := by
  classical
  have hmapshadow : (Y.map shadow).map (val p) = Y.map HahnSeries.orderTop := by
    rw [Multiset.map_map]
    exact Multiset.map_congr rfl fun y _ => val_shadow y
  have hRmap : ((Y.map shadow).map fun u => X - Polynomial.C u)
      = Y.map fun y => X - Polynomial.C (shadow y) := by
    rw [Multiset.map_map]
    rfl
  have hcard : Z.card = Y.card := by
    have h := congrArg Multiset.card hW
    rw [Multiset.card_map, Multiset.card_map] at h
    exact h.symm
  have h := exists_root_sub_valuation_le (val p) Z (Y.map shadow)
    (by rw [hmapshadow, hW])
    (k := k)
    (fun i hi => by
      rw [hcard] at hi
      obtain ⟨T, hTle, hTcard, hTsum⟩ :=
        exists_sum_le_val_coeff_sub_of_shadow_congruence Y Z hk1 hcong hi
      refine ⟨T, by rwa [← hW], by rw [hTcard, hcard], ?_⟩
      rw [hRmap]
      have hneg : ((Z.map fun y => X - Polynomial.C y).prod
            - (Y.map fun y => X - Polynomial.C (shadow y)).prod).coeff i
          = -(((Y.map fun y => X - Polynomial.C (shadow y)).prod
              - (Z.map fun y => X - Polynomial.C y).prod).coeff i) := by
        rw [← Polynomial.coeff_neg, neg_sub]
      rw [hneg, (val p).map_neg]
      exact hTsum)
    (u := z) hz (s := s) hs
  obtain ⟨u, huU, huval, hubound⟩ := h
  obtain ⟨y, hyY, rfl⟩ := Multiset.mem_map.mp huU
  refine ⟨y, hyY, by rwa [val_shadow] at huval, ?_⟩
  rw [(val p).map_sub_swap]
  rwa [← hW] at hubound

end RootsContinuity

end TrustworthyKedlaya.pAdicHahnSeries
