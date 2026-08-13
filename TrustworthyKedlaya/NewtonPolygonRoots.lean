/-
Copyright (c) 2026 Shanwen Wang, Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import TrustworthyKedlaya.RootMatching

/-!
# The Newton polygon reads off the root valuations

Blueprint `lem:newton-polygon-roots` (Kedlaya 2001b): for a split monic polynomial
`P = ∏_{y ∈ Y}(X - y)` over a ring with an additive valuation `v : F → ℚ ∪ {∞}`
whose only `∞`-valued element is `0`, the valuation multiset `v(Y)` is determined
by the coefficient-valuation data `(v(P_i))_i`.  Determination is formalized in
two-instance form (`map_v_eq_of_v_coeff_eq`): two split monic polynomials of the
same degree, over possibly different such valued rings, whose coefficients have
identical valuations have identical root-valuation multisets.

The route is division-free — no chords, convex hulls, or sorted lists.  Writing
`d j := v(P.coeff (n - j))` for `0 ≤ j ≤ n = card Y`:

* the number of roots of valuation `≤ x` is the largest `c ≤ n` minimizing
  `j ↦ d j - j·x`, encoded subtraction-free by the cross-added inequalities
  `d c + j • x ≤ d j + c • x` (`IsLeCutIndex`, `isLeCutIndex_countP`);
* the number of roots of valuation `< x` is the smallest such minimizer
  (`IsLtCutIndex`, `isLtCutIndex_countP`);
* the number of roots of valuation `∞` is `n - c` for `c` the largest index with
  `d c ≠ ∞` (`IsTopIndex`, `isTopIndex_countP`).

Each characterization pins the corresponding root count uniquely in terms of the
data `d`, and multiset extensionality on counts concludes.  The heart is the
corner equality `v_coeff_eq_sum_of_separated`: if the roots split into a low part
`Y₀` and a high part `Y₁` with every low valuation strictly below every high
valuation (and the low valuations finite), then
`v (P.coeff (card Y₁)) = ∑ v(Y₀)` *exactly* — proved by factoring `P = P₀ * P₁`
and isolating the unique minimal term `P₀.coeff 0 * P₁.leadingCoeff` of the
coefficient convolution; every other term is strictly larger by the coefficient
floors of `lem:split-coeff-floor` together with the strict low/high separation.

## References

- K. S. Kedlaya, *Power series and p-adic algebraic closures*, J. Number Theory 89
  (2001) [Ked01b], Section 3.
-/

@[expose] public section

namespace TrustworthyKedlaya

open Polynomial Multiset

/-! ### Sum bounds in `WithTop ℚ` -/

/-- A multiset of finite values has finite sum. -/
theorem sum_ne_top : ∀ {A : Multiset (WithTop ℚ)}, (∀ a ∈ A, a ≠ ⊤) → A.sum ≠ ⊤ := by
  intro A
  induction A using Multiset.induction_on with
  | empty => intro _; simp
  | cons a t ih =>
    intro h
    rw [Multiset.sum_cons]
    exact WithTop.add_ne_top.mpr ⟨h a (Multiset.mem_cons_self a t),
      ih fun b hb => h b (Multiset.mem_cons_of_mem hb)⟩

/-- A member of a multiset of values with finite sum is itself finite. -/
theorem ne_top_of_mem_of_sum_ne_top {A : Multiset (WithTop ℚ)} (hA : A.sum ≠ ⊤)
    {a : WithTop ℚ} (ha : a ∈ A) : a ≠ ⊤ := by
  intro h0
  obtain ⟨A', rfl⟩ := Multiset.exists_cons_of_mem ha
  rw [Multiset.sum_cons, h0, WithTop.top_add] at hA
  exact hA rfl

/-- Strict upper coe-bounds add: if `a < ↑p` and `b < ↑q` then `a + b < ↑(p + q)`. -/
theorem add_lt_coe_add {p q : ℚ} {a b : WithTop ℚ} (ha : a < (p : WithTop ℚ))
    (hb : b < (q : WithTop ℚ)) : a + b < ((p + q : ℚ) : WithTop ℚ) := by
  lift a to ℚ using ha.ne_top
  lift b to ℚ using hb.ne_top
  rw [← WithTop.coe_add, WithTop.coe_lt_coe]
  exact add_lt_add (WithTop.coe_lt_coe.mp ha) (WithTop.coe_lt_coe.mp hb)

/-- Strict lower coe-bounds add: if `↑p < a` and `↑q < b` then `↑(p + q) < a + b`. -/
theorem coe_add_lt_add {p q : ℚ} {a b : WithTop ℚ} (ha : (p : WithTop ℚ) < a)
    (hb : (q : WithTop ℚ) < b) : ((p + q : ℚ) : WithTop ℚ) < a + b := by
  rcases eq_or_ne a ⊤ with rfl | ha'
  · rw [WithTop.top_add]
    exact WithTop.coe_lt_top _
  · rcases eq_or_ne b ⊤ with rfl | hb'
    · rw [WithTop.add_top]
      exact WithTop.coe_lt_top _
    · lift a to ℚ using ha'
      lift b to ℚ using hb'
      rw [← WithTop.coe_add, WithTop.coe_lt_coe]
      exact add_lt_add (WithTop.coe_lt_coe.mp ha) (WithTop.coe_lt_coe.mp hb)

/-- A nonempty multiset of values strictly below `x` has sum strictly below
`card • x`. -/
theorem sum_lt_card_nsmul {x : ℚ} :
    ∀ {A : Multiset (WithTop ℚ)}, A ≠ 0 → (∀ a ∈ A, a < (x : WithTop ℚ)) →
      A.sum < A.card • (x : WithTop ℚ) := by
  intro A
  induction A using Multiset.induction_on with
  | empty => intro h _; exact absurd rfl h
  | cons a t ih =>
    intro _ h
    rcases eq_or_ne t 0 with rfl | ht
    · simp only [Multiset.sum_cons, Multiset.sum_zero, add_zero, Multiset.card_cons,
        Multiset.card_zero, zero_add, one_nsmul]
      exact h a (Multiset.mem_cons_self a 0)
    · have h1 : a < (x : WithTop ℚ) := h a (Multiset.mem_cons_self a t)
      have h2 : t.sum < ((t.card • x : ℚ) : WithTop ℚ) := by
        rw [WithTop.coe_nsmul]
        exact ih ht fun b hb => h b (Multiset.mem_cons_of_mem hb)
      rw [Multiset.sum_cons, Multiset.card_cons]
      have hcast : (t.card + 1) • (x : WithTop ℚ) = ((x + t.card • x : ℚ) : WithTop ℚ) := by
        rw [← WithTop.coe_nsmul, WithTop.coe_eq_coe, succ_nsmul, add_comm]
      rw [hcast]
      exact add_lt_coe_add h1 h2

/-- A nonempty multiset of values strictly above `x` has sum strictly above
`card • x`. -/
theorem card_nsmul_lt_sum {x : ℚ} :
    ∀ {A : Multiset (WithTop ℚ)}, A ≠ 0 → (∀ a ∈ A, (x : WithTop ℚ) < a) →
      A.card • (x : WithTop ℚ) < A.sum := by
  intro A
  induction A using Multiset.induction_on with
  | empty => intro h _; exact absurd rfl h
  | cons a t ih =>
    intro _ h
    rcases eq_or_ne t 0 with rfl | ht
    · simp only [Multiset.sum_cons, Multiset.sum_zero, add_zero, Multiset.card_cons,
        Multiset.card_zero, zero_add, one_nsmul]
      exact h a (Multiset.mem_cons_self a 0)
    · have h1 : (x : WithTop ℚ) < a := h a (Multiset.mem_cons_self a t)
      have h2 : ((t.card • x : ℚ) : WithTop ℚ) < t.sum := by
        rw [WithTop.coe_nsmul]
        exact ih ht fun b hb => h b (Multiset.mem_cons_of_mem hb)
      rw [Multiset.sum_cons, Multiset.card_cons]
      have hcast : (t.card + 1) • (x : WithTop ℚ) = ((x + t.card • x : ℚ) : WithTop ℚ) := by
        rw [← WithTop.coe_nsmul, WithTop.coe_eq_coe, succ_nsmul, add_comm]
      rw [hcast]
      exact coe_add_lt_add h1 h2

/-- Same-size multisets with all-pairs strict domination have strictly comparable
sums (the left one nonempty). -/
theorem sum_lt_sum_of_forall_lt :
    ∀ {A B : Multiset (WithTop ℚ)}, A.card = B.card → A ≠ 0 →
      (∀ a ∈ A, ∀ b ∈ B, a < b) → A.sum < B.sum := by
  intro A
  induction A using Multiset.induction_on with
  | empty => intro B _ h0 _; exact absurd rfl h0
  | cons a t ih =>
    intro B hcard _ h
    have hB : B ≠ 0 := by
      intro h0
      rw [h0, Multiset.card_zero, Multiset.card_cons] at hcard
      omega
    obtain ⟨b, hbB⟩ := Multiset.exists_mem_of_ne_zero hB
    obtain ⟨B', rfl⟩ := Multiset.exists_cons_of_mem hbB
    rw [Multiset.card_cons, Multiset.card_cons] at hcard
    have hab : a < b := h a (Multiset.mem_cons_self a t) b (Multiset.mem_cons_self b B')
    rcases eq_or_ne t 0 with rfl | ht
    · have hB' : B' = 0 := by
        rw [← Multiset.card_eq_zero]
        simp only [Multiset.card_zero] at hcard
        omega
      subst hB'
      simpa using hab
    · have hts : t.sum < B'.sum :=
        ih (by omega) ht fun a' ha' b' hb' =>
          h a' (Multiset.mem_cons_of_mem ha') b' (Multiset.mem_cons_of_mem hb')
    -- both left summands are finite, so the strict bounds add
      obtain ⟨p, hp⟩ := WithTop.ne_top_iff_exists.mp hab.ne_top
      obtain ⟨q, hq⟩ := WithTop.ne_top_iff_exists.mp hts.ne_top
      rw [Multiset.sum_cons, Multiset.sum_cons, ← hp, ← hq, ← WithTop.coe_add]
      exact coe_add_lt_add (hp ▸ hab) (hq ▸ hts)

/-! ### Cut floors: sub-multiset sums against a threshold

If a predicate `p` cuts the elements of `W` into a low part (where `p` holds, all
`≤ x`) and a high part (all `≥ x`), then for every sub-multiset `V ≤ W`, writing
`L := W.filter p`, one has `L.sum + card V • x ≤ V.sum + card L • x` — the
subtraction-free form of "`V.sum - card V • x` is minimized at `V = L`".  The
inequality is strict as soon as `card V > card L` (if the high part is strictly
above `x`) or `card V < card L` (if the low part is strictly below `x`). -/

section Cut

variable {x : ℚ} {p : WithTop ℚ → Prop} [DecidablePred p]

/-- **Cut floor**, non-strict form. -/
theorem cut_sum_le {W V : Multiset (WithTop ℚ)} (hVW : V ≤ W)
    (hlow : ∀ w ∈ W, p w → w ≤ (x : WithTop ℚ))
    (hhigh : ∀ w ∈ W, ¬ p w → (x : WithTop ℚ) ≤ w) :
    (W.filter p).sum + V.card • (x : WithTop ℚ)
      ≤ V.sum + (W.filter p).card • (x : WithTop ℚ) := by
  classical
  obtain ⟨O, hO⟩ := Multiset.le_iff_exists_add.mp (Multiset.filter_le_filter p hVW)
  have hOle : O.sum ≤ O.card • (x : WithTop ℚ) := by
    refine Multiset.sum_le_card_nsmul O _ fun o ho => ?_
    have hoW : o ∈ W.filter p := hO ▸ Multiset.mem_add.mpr (Or.inr ho)
    exact hlow o (Multiset.mem_filter.mp hoW).1 (Multiset.mem_filter.mp hoW).2
  have hV₂ : (V.filter fun w => ¬ p w).card • (x : WithTop ℚ)
      ≤ (V.filter fun w => ¬ p w).sum := by
    refine Multiset.card_nsmul_le_sum fun w hw => ?_
    exact hhigh w (Multiset.mem_of_le hVW (Multiset.mem_filter.mp hw).1)
      (Multiset.mem_filter.mp hw).2
  have hVsum : (V.filter p).sum + (V.filter fun w => ¬ p w).sum = V.sum := by
    rw [← Multiset.sum_add, Multiset.filter_add_not]
  have hVcard : (V.filter p).card + (V.filter fun w => ¬ p w).card = V.card := by
    rw [← Multiset.card_add, Multiset.filter_add_not]
  have hLsum : (W.filter p).sum = (V.filter p).sum + O.sum := by
    rw [hO, Multiset.sum_add]
  have hLcard : (W.filter p).card = (V.filter p).card + O.card := by
    rw [hO, Multiset.card_add]
  calc (W.filter p).sum + V.card • (x : WithTop ℚ)
      = ((V.filter p).sum + O.sum)
        + ((V.filter p).card • (x : WithTop ℚ)
          + (V.filter fun w => ¬ p w).card • (x : WithTop ℚ)) := by
        rw [hLsum, ← hVcard, add_nsmul]
    _ ≤ ((V.filter p).sum + O.card • (x : WithTop ℚ))
        + ((V.filter p).card • (x : WithTop ℚ) + (V.filter fun w => ¬ p w).sum) :=
        add_le_add (add_le_add_right hOle _) (add_le_add_right hV₂ _)
    _ = ((V.filter p).sum + (V.filter fun w => ¬ p w).sum)
        + ((V.filter p).card • (x : WithTop ℚ) + O.card • (x : WithTop ℚ)) := by
        abel
    _ = V.sum + (W.filter p).card • (x : WithTop ℚ) := by
        rw [hVsum, ← add_nsmul, ← hLcard]

/-- **Cut floor, strict beyond the cut**: if moreover the high part is strictly
above `x` and `V` is strictly larger than the low part, the floor is strict. -/
theorem cut_sum_lt_of_card_lt {W V : Multiset (WithTop ℚ)} (hVW : V ≤ W)
    (hlow : ∀ w ∈ W, p w → w ≤ (x : WithTop ℚ))
    (hhigh : ∀ w ∈ W, ¬ p w → (x : WithTop ℚ) < w)
    (hcard : (W.filter p).card < V.card) :
    (W.filter p).sum + V.card • (x : WithTop ℚ)
      < V.sum + (W.filter p).card • (x : WithTop ℚ) := by
  classical
  obtain ⟨O, hO⟩ := Multiset.le_iff_exists_add.mp (Multiset.filter_le_filter p hVW)
  have hOle : O.sum ≤ O.card • (x : WithTop ℚ) := by
    refine Multiset.sum_le_card_nsmul O _ fun o ho => ?_
    have hoW : o ∈ W.filter p := hO ▸ Multiset.mem_add.mpr (Or.inr ho)
    exact hlow o (Multiset.mem_filter.mp hoW).1 (Multiset.mem_filter.mp hoW).2
  have hVcard : (V.filter p).card + (V.filter fun w => ¬ p w).card = V.card := by
    rw [← Multiset.card_add, Multiset.filter_add_not]
  have hV₂0 : (V.filter fun w => ¬ p w) ≠ 0 := by
    have hc1 : (V.filter p).card ≤ (W.filter p).card :=
      Multiset.card_le_card (Multiset.filter_le_filter p hVW)
    intro h0
    rw [h0, Multiset.card_zero] at hVcard
    omega
  have hV₂lt : (V.filter fun w => ¬ p w).card • (x : WithTop ℚ)
      < (V.filter fun w => ¬ p w).sum := by
    refine card_nsmul_lt_sum hV₂0 fun w hw => ?_
    exact hhigh w (Multiset.mem_of_le hVW (Multiset.mem_filter.mp hw).1)
      (Multiset.mem_filter.mp hw).2
  have hVsum : (V.filter p).sum + (V.filter fun w => ¬ p w).sum = V.sum := by
    rw [← Multiset.sum_add, Multiset.filter_add_not]
  have hLsum : (W.filter p).sum = (V.filter p).sum + O.sum := by
    rw [hO, Multiset.sum_add]
  have hLcard : (W.filter p).card = (V.filter p).card + O.card := by
    rw [hO, Multiset.card_add]
  have hA_ne : (V.filter p).sum + O.card • (x : WithTop ℚ) ≠ ⊤ := by
    refine WithTop.add_ne_top.mpr ⟨?_, ?_⟩
    · refine sum_ne_top fun w hw => ?_
      have hle := hlow w (Multiset.mem_of_le hVW (Multiset.mem_filter.mp hw).1)
        (Multiset.mem_filter.mp hw).2
      exact (hle.trans_lt (WithTop.coe_lt_top x)).ne
    · rw [← WithTop.coe_nsmul]
      exact WithTop.coe_ne_top
  have hB_ne : (V.filter p).card • (x : WithTop ℚ) ≠ ⊤ := by
    rw [← WithTop.coe_nsmul]
    exact WithTop.coe_ne_top
  calc (W.filter p).sum + V.card • (x : WithTop ℚ)
      = ((V.filter p).sum + O.sum)
        + ((V.filter p).card • (x : WithTop ℚ)
          + (V.filter fun w => ¬ p w).card • (x : WithTop ℚ)) := by
        rw [hLsum, ← hVcard, add_nsmul]
    _ ≤ ((V.filter p).sum + O.card • (x : WithTop ℚ))
        + ((V.filter p).card • (x : WithTop ℚ)
          + (V.filter fun w => ¬ p w).card • (x : WithTop ℚ)) := by
        refine add_le_add_left (add_le_add_right hOle _) _
    _ < ((V.filter p).sum + O.card • (x : WithTop ℚ))
        + ((V.filter p).card • (x : WithTop ℚ) + (V.filter fun w => ¬ p w).sum) := by
        exact WithTop.add_lt_add_left hA_ne (WithTop.add_lt_add_left hB_ne hV₂lt)
    _ = ((V.filter p).sum + (V.filter fun w => ¬ p w).sum)
        + ((V.filter p).card • (x : WithTop ℚ) + O.card • (x : WithTop ℚ)) := by
        abel
    _ = V.sum + (W.filter p).card • (x : WithTop ℚ) := by
        rw [hVsum, ← add_nsmul, ← hLcard]

/-- **Cut floor, strict below the cut**: if moreover the low part is strictly
below `x` and `V` is strictly smaller than the low part, the floor is strict. -/
theorem cut_sum_lt_of_lt_card {W V : Multiset (WithTop ℚ)} (hVW : V ≤ W)
    (hlow : ∀ w ∈ W, p w → w < (x : WithTop ℚ))
    (hhigh : ∀ w ∈ W, ¬ p w → (x : WithTop ℚ) ≤ w)
    (hcard : V.card < (W.filter p).card) :
    (W.filter p).sum + V.card • (x : WithTop ℚ)
      < V.sum + (W.filter p).card • (x : WithTop ℚ) := by
  classical
  obtain ⟨O, hO⟩ := Multiset.le_iff_exists_add.mp (Multiset.filter_le_filter p hVW)
  have hVcard : (V.filter p).card + (V.filter fun w => ¬ p w).card = V.card := by
    rw [← Multiset.card_add, Multiset.filter_add_not]
  have hLcard : (W.filter p).card = (V.filter p).card + O.card := by
    rw [hO, Multiset.card_add]
  have hO0 : O ≠ 0 := by
    intro h0
    rw [h0, Multiset.card_zero] at hLcard
    omega
  have hOlt : O.sum < O.card • (x : WithTop ℚ) := by
    refine sum_lt_card_nsmul hO0 fun o ho => ?_
    have hoW : o ∈ W.filter p := hO ▸ Multiset.mem_add.mpr (Or.inr ho)
    exact hlow o (Multiset.mem_filter.mp hoW).1 (Multiset.mem_filter.mp hoW).2
  have hV₂ : (V.filter fun w => ¬ p w).card • (x : WithTop ℚ)
      ≤ (V.filter fun w => ¬ p w).sum := by
    refine Multiset.card_nsmul_le_sum fun w hw => ?_
    exact hhigh w (Multiset.mem_of_le hVW (Multiset.mem_filter.mp hw).1)
      (Multiset.mem_filter.mp hw).2
  have hVsum : (V.filter p).sum + (V.filter fun w => ¬ p w).sum = V.sum := by
    rw [← Multiset.sum_add, Multiset.filter_add_not]
  have hLsum : (W.filter p).sum = (V.filter p).sum + O.sum := by
    rw [hO, Multiset.sum_add]
  have hVp_ne : (V.filter p).sum ≠ ⊤ := by
    refine sum_ne_top fun w hw => ?_
    exact (hlow w (Multiset.mem_of_le hVW (Multiset.mem_filter.mp hw).1)
      (Multiset.mem_filter.mp hw).2).ne_top
  have hsmul_ne : V.card • (x : WithTop ℚ) ≠ ⊤ := by
    rw [← WithTop.coe_nsmul]
    exact WithTop.coe_ne_top
  calc (W.filter p).sum + V.card • (x : WithTop ℚ)
      = ((V.filter p).sum + O.sum) + V.card • (x : WithTop ℚ) := by rw [hLsum]
    _ < ((V.filter p).sum + O.card • (x : WithTop ℚ)) + V.card • (x : WithTop ℚ) :=
        WithTop.add_lt_add_right hsmul_ne (WithTop.add_lt_add_left hVp_ne hOlt)
    _ = ((V.filter p).sum + O.card • (x : WithTop ℚ))
        + ((V.filter p).card • (x : WithTop ℚ)
          + (V.filter fun w => ¬ p w).card • (x : WithTop ℚ)) := by
        rw [← hVcard, add_nsmul]
    _ ≤ ((V.filter p).sum + O.card • (x : WithTop ℚ))
        + ((V.filter p).card • (x : WithTop ℚ) + (V.filter fun w => ¬ p w).sum) :=
        add_le_add_right (add_le_add_right hV₂ _) _
    _ = ((V.filter p).sum + (V.filter fun w => ¬ p w).sum)
        + ((V.filter p).card • (x : WithTop ℚ) + O.card • (x : WithTop ℚ)) := by
        abel
    _ = V.sum + (W.filter p).card • (x : WithTop ℚ) := by
        rw [hVsum, ← add_nsmul, ← hLcard]

end Cut

/-! ### Corner equality -/

variable {F : Type*} [CommRing F] (v : AddValuation F (WithTop ℚ))

/-- **Corner equality.**  If the root multiset `Y` splits into a low part
(`q` holds, finite valuations) and a high part, with every low valuation strictly
below every high valuation, then the coefficient of `X ^ (number of high roots)`
in `∏_{y ∈ Y}(X - y)` has valuation *exactly* the sum of the low valuations.

This is the vertex case of the Newton-polygon dictionary: the term of the
coefficient convolution coming from (constant coefficient of the low factor) ×
(leading coefficient of the high factor) is the strict minimum among all terms. -/
theorem v_coeff_eq_sum_of_separated [Nontrivial F] (Y : Multiset F)
    (q : F → Prop) [DecidablePred q]
    (hfin : ∀ y ∈ Y, q y → v y ≠ ⊤)
    (hsep : ∀ y ∈ Y, q y → ∀ y' ∈ Y, ¬ q y' → v y < v y') :
    v (((Y.map fun y => X - C y).prod).coeff (Y.filter fun y => ¬ q y).card)
      = ((Y.filter q).map v).sum := by
  classical
  set Y₀ := Y.filter q with hY₀def
  set Y₁ := Y.filter (fun y => ¬ q y) with hY₁def
  have hsplit : Y₀ + Y₁ = Y := Multiset.filter_add_not q Y
  set P₀ : F[X] := (Y₀.map fun y => X - C y).prod with hP₀def
  set P₁ : F[X] := (Y₁.map fun y => X - C y).prod with hP₁def
  have hP : (Y.map fun y => X - C y).prod = P₀ * P₁ := by
    rw [← hsplit, Multiset.map_add, Multiset.prod_add]
  have hσ_ne : ((Y₀.map v).sum : WithTop ℚ) ≠ ⊤ := by
    refine sum_ne_top fun a ha => ?_
    obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp ha
    exact hfin y (Multiset.mem_filter.mp hy).1 (Multiset.mem_filter.mp hy).2
  -- the two ends of the convolution
  have hP₁monic : P₁.Monic :=
    monic_multiset_prod_of_monic _ _ fun y _ => monic_X_sub_C y
  have hP₁deg : P₁.natDegree = Y₁.card := by
    rw [hP₁def, natDegree_multiset_prod_X_sub_C_eq_card]
  have hP₁top : P₁.coeff Y₁.card = 1 := by
    rw [← hP₁deg]
    exact hP₁monic.coeff_natDegree
  have hP₀c : v (P₀.coeff 0) = (Y₀.map v).sum := by
    rw [hP₀def, Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_multiset_prod,
      Multiset.map_map, AddValuation.map_multiset_prod, Multiset.map_map]
    congr 1
    refine Multiset.map_congr rfl fun y _ => ?_
    simp only [Function.comp_apply, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_C, zero_sub]
    exact v.map_neg y
  have hmain : v (P₀.coeff 0 * P₁.coeff Y₁.card) = (Y₀.map v).sum := by
    rw [hP₁top, mul_one, hP₀c]
  -- all other terms of the convolution are strictly larger
  have hterm : ∀ pr ∈ (Finset.antidiagonal Y₁.card).erase ((0 : ℕ), Y₁.card),
      (Y₀.map v).sum < v (P₀.coeff pr.1 * P₁.coeff pr.2) := by
    rintro ⟨i, k⟩ hpr
    rw [Finset.mem_erase, Finset.mem_antidiagonal] at hpr
    obtain ⟨hne, hik⟩ := hpr
    have hi : 0 < i := by
      by_contra hcon
      have hi0 : i = 0 := by omega
      subst hi0
      have hk : k = Y₁.card := by omega
      subst hk
      exact hne rfl
    by_cases hin₀ : i ≤ Y₀.card
    · have hkn₁ : k ≤ Y₁.card := by omega
      obtain ⟨T₀, hT₀le, hT₀card, -, hT₀⟩ := exists_sum_le_v_coeff_prod_X_sub_C v Y₀ hin₀
      obtain ⟨T₁, hT₁le, hT₁card, -, hT₁⟩ := exists_sum_le_v_coeff_prod_X_sub_C v Y₁ hkn₁
      obtain ⟨O, hO⟩ := Multiset.le_iff_exists_add.mp hT₀le
      have hOcard : O.card = i := by
        have h1 := congrArg Multiset.card hO
        rw [Multiset.card_map, Multiset.card_add, hT₀card] at h1
        omega
      have hT₁card' : T₁.card = i := by
        rw [hT₁card]
        omega
      have hO0 : O ≠ 0 := by
        intro h0
        rw [h0, Multiset.card_zero] at hOcard
        omega
      have hOT : ∀ o ∈ O, ∀ u ∈ T₁, o < u := by
        intro o ho u hu
        have hoY₀ : o ∈ Y₀.map v := by
          rw [hO]
          exact Multiset.mem_add.mpr (Or.inr ho)
        obtain ⟨y₀, hy₀, rfl⟩ := Multiset.mem_map.mp hoY₀
        have huY₁ : u ∈ Y₁.map v := Multiset.mem_of_le hT₁le hu
        obtain ⟨y₁, hy₁, rfl⟩ := Multiset.mem_map.mp huY₁
        exact hsep y₀ (Multiset.mem_filter.mp hy₀).1 (Multiset.mem_filter.mp hy₀).2
          y₁ (Multiset.mem_filter.mp hy₁).1 (Multiset.mem_filter.mp hy₁).2
      have hOT_sum : O.sum < T₁.sum :=
        sum_lt_sum_of_forall_lt (by rw [hOcard, hT₁card']) hO0 hOT
      have hσ_split : ((Y₀.map v).sum : WithTop ℚ) = T₀.sum + O.sum := by
        rw [hO, Multiset.sum_add]
      have hT₀ne : T₀.sum ≠ ⊤ := by
        intro h0
        rw [hσ_split, h0, WithTop.top_add] at hσ_ne
        exact hσ_ne rfl
      calc ((Y₀.map v).sum : WithTop ℚ) = T₀.sum + O.sum := hσ_split
        _ < T₀.sum + T₁.sum := WithTop.add_lt_add_left hT₀ne hOT_sum
        _ ≤ v (P₀.coeff i) + v (P₁.coeff k) := add_le_add hT₀ hT₁
        _ = v (P₀.coeff i * P₁.coeff k) := (v.map_mul _ _).symm
    · have h0 : P₀.coeff i = 0 := by
        refine Polynomial.coeff_eq_zero_of_natDegree_lt ?_
        rw [hP₀def, natDegree_multiset_prod_X_sub_C_eq_card]
        omega
      rw [h0, zero_mul, v.map_zero]
      exact lt_top_iff_ne_top.mpr hσ_ne
  -- assemble
  have hmem : ((0 : ℕ), Y₁.card) ∈ Finset.antidiagonal Y₁.card :=
    Finset.mem_antidiagonal.mpr (zero_add _)
  rw [hP, Polynomial.coeff_mul, ← Finset.add_sum_erase _ _ hmem]
  have hrest : ((Y₀.map v).sum : WithTop ℚ)
      < v (∑ pr ∈ (Finset.antidiagonal Y₁.card).erase ((0 : ℕ), Y₁.card),
          P₀.coeff pr.1 * P₁.coeff pr.2) :=
    v.map_lt_sum hσ_ne hterm
  rw [v.map_add_eq_of_lt_left (hmain.trans_lt hrest)]
  exact hmain

/-! ### The three index characterizations -/

/-- `c` is the count of finite entries of the valuation profile: `d c` is finite
and `d j = ⊤` for every `j > c`. -/
def IsTopIndex (d : ℕ → WithTop ℚ) (n c : ℕ) : Prop :=
  c ≤ n ∧ d c ≠ ⊤ ∧ ∀ j ≤ n, c < j → d j = ⊤

/-- `c` is the largest minimizer of `j ↦ d j - j • x` on `[0, n]`, in cross-added
subtraction-free form. -/
def IsLeCutIndex (d : ℕ → WithTop ℚ) (n : ℕ) (x : ℚ) (c : ℕ) : Prop :=
  c ≤ n ∧ (∀ j ≤ n, d c + j • (x : WithTop ℚ) ≤ d j + c • (x : WithTop ℚ)) ∧
    ∀ j ≤ n, c < j → d c + j • (x : WithTop ℚ) < d j + c • (x : WithTop ℚ)

/-- `c` is the smallest minimizer of `j ↦ d j - j • x` on `[0, n]`, in cross-added
subtraction-free form. -/
def IsLtCutIndex (d : ℕ → WithTop ℚ) (n : ℕ) (x : ℚ) (c : ℕ) : Prop :=
  c ≤ n ∧ (∀ j ≤ n, d c + j • (x : WithTop ℚ) ≤ d j + c • (x : WithTop ℚ)) ∧
    ∀ j ≤ n, j < c → d c + j • (x : WithTop ℚ) < d j + c • (x : WithTop ℚ)

theorem IsTopIndex.unique {d : ℕ → WithTop ℚ} {n c₁ c₂ : ℕ}
    (h₁ : IsTopIndex d n c₁) (h₂ : IsTopIndex d n c₂) : c₁ = c₂ := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · exact h₂.2.1 (h₁.2.2 c₂ h₂.1 h)
  · exact h₁.2.1 (h₂.2.2 c₁ h₁.1 h)

theorem IsLeCutIndex.unique {d : ℕ → WithTop ℚ} {n : ℕ} {x : ℚ} {c₁ c₂ : ℕ}
    (h₁ : IsLeCutIndex d n x c₁) (h₂ : IsLeCutIndex d n x c₂) : c₁ = c₂ := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · exact absurd (h₁.2.2 c₂ h₂.1 h) (not_lt.mpr (h₂.2.1 c₁ h₁.1))
  · exact absurd (h₂.2.2 c₁ h₁.1 h) (not_lt.mpr (h₁.2.1 c₂ h₂.1))

theorem IsLtCutIndex.unique {d : ℕ → WithTop ℚ} {n : ℕ} {x : ℚ} {c₁ c₂ : ℕ}
    (h₁ : IsLtCutIndex d n x c₁) (h₂ : IsLtCutIndex d n x c₂) : c₁ = c₂ := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · exact absurd (h₂.2.2 c₁ h₁.1 h) (not_lt.mpr (h₁.2.1 c₂ h₂.1))
  · exact absurd (h₁.2.2 c₂ h₂.1 h) (not_lt.mpr (h₂.2.1 c₁ h₁.1))

theorem IsTopIndex.congr {d d' : ℕ → WithTop ℚ} {n c : ℕ}
    (h : IsTopIndex d n c) (hdd : ∀ j ≤ n, d' j = d j) : IsTopIndex d' n c := by
  obtain ⟨hcn, hfin, htop⟩ := h
  refine ⟨hcn, ?_, fun j hj hcj => ?_⟩
  · rw [hdd c hcn]
    exact hfin
  · rw [hdd j hj]
    exact htop j hj hcj

theorem IsLeCutIndex.congr {d d' : ℕ → WithTop ℚ} {n : ℕ} {x : ℚ} {c : ℕ}
    (h : IsLeCutIndex d n x c) (hdd : ∀ j ≤ n, d' j = d j) : IsLeCutIndex d' n x c := by
  obtain ⟨hcn, hmin, hstrict⟩ := h
  refine ⟨hcn, fun j hj => ?_, fun j hj hcj => ?_⟩
  · rw [hdd j hj, hdd c hcn]
    exact hmin j hj
  · rw [hdd j hj, hdd c hcn]
    exact hstrict j hj hcj

theorem IsLtCutIndex.congr {d d' : ℕ → WithTop ℚ} {n : ℕ} {x : ℚ} {c : ℕ}
    (h : IsLtCutIndex d n x c) (hdd : ∀ j ≤ n, d' j = d j) : IsLtCutIndex d' n x c := by
  obtain ⟨hcn, hmin, hstrict⟩ := h
  refine ⟨hcn, fun j hj => ?_, fun j hj hcj => ?_⟩
  · rw [hdd j hj, hdd c hcn]
    exact hmin j hj
  · rw [hdd j hj, hdd c hcn]
    exact hstrict j hj hcj

/-- The number of roots of valuation `≤ x` is the largest minimizer of
`j ↦ v (P.coeff (n - j)) - j • x`. -/
theorem isLeCutIndex_countP [Nontrivial F] (Y : Multiset F) (x : ℚ) :
    IsLeCutIndex (fun j => v (((Y.map fun y => X - C y).prod).coeff (Y.card - j)))
      Y.card x ((Y.map v).countP (· ≤ (x : WithTop ℚ))) := by
  classical
  have hcfilter : (Y.map v).countP (· ≤ (x : WithTop ℚ))
      = (Y.filter fun y => v y ≤ (x : WithTop ℚ)).card := Multiset.countP_map _ _ _
  have hcn : (Y.map v).countP (· ≤ (x : WithTop ℚ)) ≤ Y.card := by
    rw [hcfilter]
    exact Multiset.card_le_card (Multiset.filter_le _ _)
  have hfilter_eq : (Y.map v).filter (· ≤ (x : WithTop ℚ))
      = (Y.filter fun y => v y ≤ (x : WithTop ℚ)).map v := by
    rw [Multiset.filter_map]
    exact congrArg (Multiset.map v) (Multiset.filter_congr fun y _ => Iff.rfl)
  have hLcard : ((Y.map v).filter (· ≤ (x : WithTop ℚ))).card
      = (Y.map v).countP (· ≤ (x : WithTop ℚ)) :=
    (Multiset.countP_eq_card_filter _ _).symm
  -- corner equality at the cut
  have hindex : (Y.filter fun y => ¬ (v y ≤ (x : WithTop ℚ))).card
      = Y.card - (Y.map v).countP (· ≤ (x : WithTop ℚ)) := by
    have h1 := congrArg Multiset.card
      (Multiset.filter_add_not (fun y => v y ≤ (x : WithTop ℚ)) Y)
    rw [Multiset.card_add] at h1
    omega
  have hcorner : v (((Y.map fun y => X - C y).prod).coeff
        (Y.card - (Y.map v).countP (· ≤ (x : WithTop ℚ))))
      = ((Y.filter fun y => v y ≤ (x : WithTop ℚ)).map v).sum := by
    rw [← hindex]
    exact v_coeff_eq_sum_of_separated v Y _
      (fun y _ hy => (hy.trans_lt (WithTop.coe_lt_top x)).ne)
      (fun y _ hy y' _ hy' => hy.trans_lt (not_le.mp hy'))
  refine ⟨hcn, fun j hj => ?_, fun j hj hcj => ?_⟩
  · obtain ⟨T, hTle, hTcard, -, hT⟩ := exists_sum_le_v_coeff_prod_X_sub_C v Y
      (i := Y.card - j) (Nat.sub_le _ _)
    have hTcard' : T.card = j := by
      rw [hTcard]
      omega
    have hcut := cut_sum_le (p := (· ≤ (x : WithTop ℚ))) hTle
      (fun w _ hw => hw) (fun w _ hw => (not_le.mp hw).le)
    rw [hfilter_eq, Multiset.card_map, ← hcfilter, hTcard'] at hcut
    have hgoal : v (((Y.map fun y => X - C y).prod).coeff
          (Y.card - (Y.map v).countP (· ≤ (x : WithTop ℚ)))) + j • (x : WithTop ℚ)
        ≤ v (((Y.map fun y => X - C y).prod).coeff (Y.card - j))
          + ((Y.map v).countP (· ≤ (x : WithTop ℚ))) • (x : WithTop ℚ) := by
      rw [hcorner]
      exact hcut.trans (add_le_add_left hT _)
    exact hgoal
  · obtain ⟨T, hTle, hTcard, -, hT⟩ := exists_sum_le_v_coeff_prod_X_sub_C v Y
      (i := Y.card - j) (Nat.sub_le _ _)
    have hTcard' : T.card = j := by
      rw [hTcard]
      omega
    have hcut := cut_sum_lt_of_card_lt (p := (· ≤ (x : WithTop ℚ))) hTle
      (fun w _ hw => hw) (fun w _ hw => not_le.mp hw)
      (by rw [hLcard, hTcard']; exact hcj)
    rw [hfilter_eq, Multiset.card_map, ← hcfilter, hTcard'] at hcut
    have hgoal : v (((Y.map fun y => X - C y).prod).coeff
          (Y.card - (Y.map v).countP (· ≤ (x : WithTop ℚ)))) + j • (x : WithTop ℚ)
        < v (((Y.map fun y => X - C y).prod).coeff (Y.card - j))
          + ((Y.map v).countP (· ≤ (x : WithTop ℚ))) • (x : WithTop ℚ) := by
      rw [hcorner]
      exact hcut.trans_le (add_le_add_left hT _)
    exact hgoal

/-- The number of roots of valuation `< x` is the smallest minimizer of
`j ↦ v (P.coeff (n - j)) - j • x`. -/
theorem isLtCutIndex_countP [Nontrivial F] (Y : Multiset F) (x : ℚ) :
    IsLtCutIndex (fun j => v (((Y.map fun y => X - C y).prod).coeff (Y.card - j)))
      Y.card x ((Y.map v).countP (· < (x : WithTop ℚ))) := by
  classical
  have hcfilter : (Y.map v).countP (· < (x : WithTop ℚ))
      = (Y.filter fun y => v y < (x : WithTop ℚ)).card := Multiset.countP_map _ _ _
  have hcn : (Y.map v).countP (· < (x : WithTop ℚ)) ≤ Y.card := by
    rw [hcfilter]
    exact Multiset.card_le_card (Multiset.filter_le _ _)
  have hfilter_eq : (Y.map v).filter (· < (x : WithTop ℚ))
      = (Y.filter fun y => v y < (x : WithTop ℚ)).map v := by
    rw [Multiset.filter_map]
    exact congrArg (Multiset.map v) (Multiset.filter_congr fun y _ => Iff.rfl)
  have hLcard : ((Y.map v).filter (· < (x : WithTop ℚ))).card
      = (Y.map v).countP (· < (x : WithTop ℚ)) :=
    (Multiset.countP_eq_card_filter _ _).symm
  have hindex : (Y.filter fun y => ¬ (v y < (x : WithTop ℚ))).card
      = Y.card - (Y.map v).countP (· < (x : WithTop ℚ)) := by
    have h1 := congrArg Multiset.card
      (Multiset.filter_add_not (fun y => v y < (x : WithTop ℚ)) Y)
    rw [Multiset.card_add] at h1
    omega
  have hcorner : v (((Y.map fun y => X - C y).prod).coeff
        (Y.card - (Y.map v).countP (· < (x : WithTop ℚ))))
      = ((Y.filter fun y => v y < (x : WithTop ℚ)).map v).sum := by
    rw [← hindex]
    exact v_coeff_eq_sum_of_separated v Y _
      (fun y _ hy => (hy.trans (WithTop.coe_lt_top x)).ne)
      (fun y _ hy y' _ hy' => hy.trans_le (not_lt.mp hy'))
  refine ⟨hcn, fun j hj => ?_, fun j hj hjc => ?_⟩
  · obtain ⟨T, hTle, hTcard, -, hT⟩ := exists_sum_le_v_coeff_prod_X_sub_C v Y
      (i := Y.card - j) (Nat.sub_le _ _)
    have hTcard' : T.card = j := by
      rw [hTcard]
      omega
    have hcut := cut_sum_le (p := (· < (x : WithTop ℚ))) hTle
      (fun w _ hw => hw.le) (fun w _ hw => not_lt.mp hw)
    rw [hfilter_eq, Multiset.card_map, ← hcfilter, hTcard'] at hcut
    have hgoal : v (((Y.map fun y => X - C y).prod).coeff
          (Y.card - (Y.map v).countP (· < (x : WithTop ℚ)))) + j • (x : WithTop ℚ)
        ≤ v (((Y.map fun y => X - C y).prod).coeff (Y.card - j))
          + ((Y.map v).countP (· < (x : WithTop ℚ))) • (x : WithTop ℚ) := by
      rw [hcorner]
      exact hcut.trans (add_le_add_left hT _)
    exact hgoal
  · obtain ⟨T, hTle, hTcard, -, hT⟩ := exists_sum_le_v_coeff_prod_X_sub_C v Y
      (i := Y.card - j) (Nat.sub_le _ _)
    have hTcard' : T.card = j := by
      rw [hTcard]
      omega
    have hcut := cut_sum_lt_of_lt_card (p := (· < (x : WithTop ℚ))) hTle
      (fun w _ hw => hw) (fun w _ hw => not_lt.mp hw)
      (by rw [hLcard, hTcard']; exact hjc)
    rw [hfilter_eq, Multiset.card_map, ← hcfilter, hTcard'] at hcut
    have hgoal : v (((Y.map fun y => X - C y).prod).coeff
          (Y.card - (Y.map v).countP (· < (x : WithTop ℚ)))) + j • (x : WithTop ℚ)
        < v (((Y.map fun y => X - C y).prod).coeff (Y.card - j))
          + ((Y.map v).countP (· < (x : WithTop ℚ))) • (x : WithTop ℚ) := by
      rw [hcorner]
      exact hcut.trans_le (add_le_add_left hT _)
    exact hgoal

/-- The number of roots of finite valuation is the largest index `c` with
`v (P.coeff (n - c)) ≠ ⊤`. -/
theorem isTopIndex_countP [Nontrivial F] (hv : ∀ y : F, v y = ⊤ → y = 0)
    (Y : Multiset F) :
    IsTopIndex (fun j => v (((Y.map fun y => X - C y).prod).coeff (Y.card - j)))
      Y.card ((Y.map v).countP (fun w => w ≠ ⊤)) := by
  classical
  have hcfilter : (Y.map v).countP (fun w => w ≠ ⊤)
      = (Y.filter fun y => v y ≠ ⊤).card := Multiset.countP_map _ _ _
  have hcn : (Y.map v).countP (fun w => w ≠ ⊤) ≤ Y.card := by
    rw [hcfilter]
    exact Multiset.card_le_card (Multiset.filter_le _ _)
  have hindex : (Y.filter fun y => ¬ (v y ≠ ⊤)).card
      = Y.card - (Y.map v).countP (fun w => w ≠ ⊤) := by
    have h1 := congrArg Multiset.card (Multiset.filter_add_not (fun y => v y ≠ ⊤) Y)
    rw [Multiset.card_add] at h1
    omega
  refine ⟨hcn, ?_, fun j hj hcj => ?_⟩
  · have hcorner : v (((Y.map fun y => X - C y).prod).coeff
          (Y.card - (Y.map v).countP (fun w => w ≠ ⊤)))
        = ((Y.filter fun y => v y ≠ ⊤).map v).sum := by
      rw [← hindex]
      exact v_coeff_eq_sum_of_separated v Y _ (fun y _ hy => hy)
        (fun y _ hy y' _ hy' =>
          lt_of_lt_of_eq (lt_top_iff_ne_top.mpr hy) (not_not.mp hy').symm)
    have hgoal : v (((Y.map fun y => X - C y).prod).coeff
        (Y.card - (Y.map v).countP (fun w => w ≠ ⊤))) ≠ ⊤ := by
      rw [hcorner]
      refine sum_ne_top fun a ha => ?_
      obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp ha
      exact (Multiset.mem_filter.mp hy).2
    exact hgoal
  · -- beyond the finite count the coefficients vanish identically
    have hzeros : ((Y.filter fun y => ¬ (v y ≠ ⊤)).map fun y => X - C y)
        = Multiset.replicate (Y.card - (Y.map v).countP (fun w => w ≠ ⊤)) (X : F[X]) := by
      rw [Multiset.eq_replicate]
      constructor
      · rw [Multiset.card_map, hindex]
      · intro b hb
        obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp hb
        have h0 : y = 0 := hv y (not_not.mp (Multiset.mem_filter.mp hy).2)
        rw [h0, Polynomial.C_0, sub_zero]
    have hP : (Y.map fun y => X - C y).prod
        = ((Y.filter fun y => v y ≠ ⊤).map fun y => X - C y).prod
          * X ^ (Y.card - (Y.map v).countP (fun w => w ≠ ⊤)) := by
      conv_lhs => rw [← Multiset.filter_add_not (fun y => v y ≠ ⊤) Y]
      rw [Multiset.map_add, Multiset.prod_add, hzeros, Multiset.prod_replicate]
    have hgoal : v (((Y.map fun y => X - C y).prod).coeff (Y.card - j)) = ⊤ := by
      rw [hP, Polynomial.coeff_mul_X_pow',
        if_neg (by omega : ¬ (Y.card - (Y.map v).countP (fun w => w ≠ ⊤) ≤ Y.card - j))]
      exact v.map_zero
    exact hgoal

/-! ### The main theorem -/

/-- Multisets of values in `ℚ ∪ {∞}` are determined by their cardinality together
with the counts of entries `≤ x` and `< x` (all rational `x`) and of finite
entries. -/
theorem multiset_eq_of_countP_cuts {M₁ M₂ : Multiset (WithTop ℚ)}
    (hcard : M₁.card = M₂.card)
    (htop : M₁.countP (fun w => w ≠ ⊤) = M₂.countP (fun w => w ≠ ⊤))
    (hle : ∀ x : ℚ, M₁.countP (· ≤ (x : WithTop ℚ)) = M₂.countP (· ≤ (x : WithTop ℚ)))
    (hlt : ∀ x : ℚ, M₁.countP (· < (x : WithTop ℚ)) = M₂.countP (· < (x : WithTop ℚ))) :
    M₁ = M₂ := by
  classical
  refine Multiset.ext.mpr fun a => ?_
  -- auxiliary counting identities
  have hkey_top : ∀ M : Multiset (WithTop ℚ),
      M.count ⊤ + M.countP (fun w => w ≠ ⊤) = M.card := by
    intro M
    have h1 := congrArg Multiset.card (Multiset.filter_add_not (fun w => w = ⊤) M)
    rw [Multiset.card_add] at h1
    have h2 : M.count ⊤ = (M.filter fun w => w = ⊤).card := by
      rw [Multiset.count, Multiset.countP_eq_card_filter]
      exact congrArg Multiset.card (Multiset.filter_congr fun w _ => eq_comm)
    have h3 : M.countP (fun w => w ≠ ⊤) = (M.filter fun w => ¬ (w = ⊤)).card :=
      Multiset.countP_eq_card_filter _ _
    omega
  have hkey_coe : ∀ (M : Multiset (WithTop ℚ)) (t : ℚ),
      M.countP (· < (t : WithTop ℚ)) + M.count (t : WithTop ℚ)
        = M.countP (· ≤ (t : WithTop ℚ)) := by
    intro M t
    have h1 := Multiset.filter_add_filter (· < (t : WithTop ℚ)) (· = (t : WithTop ℚ)) M
    have h2 : (M.filter fun w => w < (t : WithTop ℚ) ∨ w = (t : WithTop ℚ))
        = M.filter (· ≤ (t : WithTop ℚ)) :=
      Multiset.filter_congr fun w _ => (le_iff_lt_or_eq (a := w) (b := (t : WithTop ℚ))).symm
    have h3 : (M.filter fun w => w < (t : WithTop ℚ) ∧ w = (t : WithTop ℚ)) = 0 := by
      rw [Multiset.filter_eq_nil]
      rintro w - ⟨hlt', rfl⟩
      exact lt_irrefl _ hlt'
    rw [h2, h3, add_zero] at h1
    have h4 := congrArg Multiset.card h1
    rw [Multiset.card_add] at h4
    have h5 : M.count (t : WithTop ℚ) = (M.filter fun w => w = (t : WithTop ℚ)).card := by
      rw [Multiset.count, Multiset.countP_eq_card_filter]
      exact congrArg Multiset.card (Multiset.filter_congr fun w _ => eq_comm)
    rw [Multiset.countP_eq_card_filter, Multiset.countP_eq_card_filter]
    omega
  induction a using WithTop.recTopCoe with
  | top =>
    have k₁ := hkey_top M₁
    have k₂ := hkey_top M₂
    omega
  | coe t =>
    have k₁ := hkey_coe M₁ t
    have k₂ := hkey_coe M₂ t
    have h₁ := hle t
    have h₂ := hlt t
    omega

/-- **The Newton polygon reads off the root valuations**
(`lem:newton-polygon-roots`; Kedlaya 2001b, Section 3).  Let `Y₁, Y₂` be root
multisets of the same size over (possibly different) commutative rings carrying
`ℚ ∪ {∞}`-valued additive valuations whose only `∞`-valued element is `0`.  If the
split monic polynomials `∏_{y ∈ Y₁}(X - y)` and `∏_{y ∈ Y₂}(X - y)` have
coefficientwise identical valuations, then the valuation multisets `v₁(Y₁)` and
`v₂(Y₂)` coincide.  In other words, the root-valuation multiset is determined by
the coefficient-valuation data. -/
theorem map_v_eq_of_v_coeff_eq {F₁ : Type*} [CommRing F₁] [Nontrivial F₁]
    {F₂ : Type*} [CommRing F₂] [Nontrivial F₂]
    (v₁ : AddValuation F₁ (WithTop ℚ)) (v₂ : AddValuation F₂ (WithTop ℚ))
    (hv₁ : ∀ y : F₁, v₁ y = ⊤ → y = 0) (hv₂ : ∀ y : F₂, v₂ y = ⊤ → y = 0)
    (Y₁ : Multiset F₁) (Y₂ : Multiset F₂) (hcard : Y₁.card = Y₂.card)
    (hcoeff : ∀ i ≤ Y₁.card,
      v₁ (((Y₁.map fun y => X - C y).prod).coeff i)
        = v₂ (((Y₂.map fun y => X - C y).prod).coeff i)) :
    Y₁.map v₁ = Y₂.map v₂ := by
  classical
  -- the two coefficient-valuation profiles agree up to degree
  have hd : ∀ j ≤ Y₁.card,
      v₁ (((Y₁.map fun y => X - C y).prod).coeff (Y₁.card - j))
        = v₂ (((Y₂.map fun y => X - C y).prod).coeff (Y₁.card - j)) :=
    fun j _ => hcoeff (Y₁.card - j) (Nat.sub_le _ _)
  -- transported characterizations for the second instance
  have htop₂ : IsTopIndex
      (fun j => v₁ (((Y₁.map fun y => X - C y).prod).coeff (Y₁.card - j)))
      Y₁.card ((Y₂.map v₂).countP (fun w => w ≠ ⊤)) := by
    have h₂ := isTopIndex_countP v₂ hv₂ Y₂
    rw [← hcard] at h₂
    exact h₂.congr hd
  have hle₂ : ∀ x : ℚ, IsLeCutIndex
      (fun j => v₁ (((Y₁.map fun y => X - C y).prod).coeff (Y₁.card - j)))
      Y₁.card x ((Y₂.map v₂).countP (· ≤ (x : WithTop ℚ))) := by
    intro x
    have h₂ := isLeCutIndex_countP v₂ Y₂ x
    rw [← hcard] at h₂
    exact h₂.congr hd
  have hlt₂ : ∀ x : ℚ, IsLtCutIndex
      (fun j => v₁ (((Y₁.map fun y => X - C y).prod).coeff (Y₁.card - j)))
      Y₁.card x ((Y₂.map v₂).countP (· < (x : WithTop ℚ))) := by
    intro x
    have h₂ := isLtCutIndex_countP v₂ Y₂ x
    rw [← hcard] at h₂
    exact h₂.congr hd
  -- count agreement
  have htop : (Y₁.map v₁).countP (fun w => w ≠ ⊤)
      = (Y₂.map v₂).countP (fun w => w ≠ ⊤) :=
    (isTopIndex_countP v₁ hv₁ Y₁).unique htop₂
  have hle : ∀ x : ℚ, (Y₁.map v₁).countP (· ≤ (x : WithTop ℚ))
      = (Y₂.map v₂).countP (· ≤ (x : WithTop ℚ)) :=
    fun x => (isLeCutIndex_countP v₁ Y₁ x).unique (hle₂ x)
  have hlt : ∀ x : ℚ, (Y₁.map v₁).countP (· < (x : WithTop ℚ))
      = (Y₂.map v₂).countP (· < (x : WithTop ℚ)) :=
    fun x => (isLtCutIndex_countP v₁ Y₁ x).unique (hlt₂ x)
  have hcards : (Y₁.map v₁).card = (Y₂.map v₂).card := by
    rw [Multiset.card_map, Multiset.card_map, hcard]
  exact multiset_eq_of_countP_cuts hcards htop hle hlt

/-! ### Congruence robustness -/

/-- **The Newton-polygon dictionary is congruence-robust**
(`lem:polygon-congruence`; Kedlaya 2001b, Section 3).  Let `Y, Z` be root
multisets of the same size `n` over a commutative ring carrying a
`ℚ ∪ {∞}`-valued additive valuation `v` whose only `∞`-valued element is `0`,
and write `P = ∏_{y ∈ Y}(X - y)`, `Q = ∏_{z ∈ Z}(X - z)`.  If for some `k > 0`
every coefficient difference obeys `σ_{n-i}(v(Y)) + k ≤ v ((P - Q).coeff i)` —
the floor delivered, exactly as in `exists_root_sub_valuation_le`, by a
size-`(n-i)` sub-multiset witness `T ≤ Y.map v` — then `Z.map v = Y.map v`.

This upgrades `map_v_eq_of_v_coeff_eq`: a congruence cannot control coefficient
valuations above the Newton polygon, but it pins them below the depth
`σ_{n-i} + k`, which covers the polygon's corners (where
`v (P.coeff (n - j)) = σ_j` exactly); at every other index the cut floors beat
the congruence depth, so the extreme-minimizer characterizations transfer from
the coefficient profile of `P` to that of `Q` and the root-valuation counts
agree — the `∞`-count included, since a floor `σ_j = ∞` forces the matching
coefficients to have valuation `∞` on both sides. -/
theorem map_v_eq_of_v_coeff_sub [Nontrivial F] (hv : ∀ y : F, v y = ⊤ → y = 0)
    (Y Z : Multiset F) (hcard : Y.card = Z.card) {k : ℚ} (hk : 0 < k)
    (hcong : ∀ i < Y.card, ∃ T ≤ Y.map v, T.card = Y.card - i ∧
      T.sum + (k : WithTop ℚ) ≤
        v ((((Y.map fun y => X - C y).prod) - ((Z.map fun y => X - C y).prod)).coeff i)) :
    Z.map v = Y.map v := by
  classical
  -- both products are monic of degree `Y.card`
  have hPmonic : ((Y.map fun y => X - C y).prod).Monic :=
    monic_multiset_prod_of_monic _ _ fun y _ => monic_X_sub_C y
  have hQmonic : ((Z.map fun y => X - C y).prod).Monic :=
    monic_multiset_prod_of_monic _ _ fun y _ => monic_X_sub_C y
  have hPdeg : ((Y.map fun y => X - C y).prod).natDegree = Y.card :=
    natDegree_multiset_prod_X_sub_C_eq_card Y
  have hQdeg : ((Z.map fun y => X - C y).prod).natDegree = Y.card := by
    rw [natDegree_multiset_prod_X_sub_C_eq_card, hcard]
  have hlead : v (((Z.map fun y => X - C y).prod).coeff (Y.card - 0))
      = v (((Y.map fun y => X - C y).prod).coeff (Y.card - 0)) := by
    rw [Nat.sub_zero]
    conv_lhs => rw [← hQdeg, hQmonic.coeff_natDegree]
    conv_rhs => rw [← hPdeg, hPmonic.coeff_natDegree]
  -- coefficientwise, below the congruence depth the two valuation profiles agree;
  -- at or above it, both sides clear the floor `T.sum + k`
  have hdisj : ∀ j ≤ Y.card,
      v (((Z.map fun y => X - C y).prod).coeff (Y.card - j))
        = v (((Y.map fun y => X - C y).prod).coeff (Y.card - j)) ∨
      ∃ T ≤ Y.map v, T.card = j ∧
        T.sum + (k : WithTop ℚ)
          ≤ v (((Y.map fun y => X - C y).prod).coeff (Y.card - j)) ∧
        T.sum + (k : WithTop ℚ)
          ≤ v (((Z.map fun y => X - C y).prod).coeff (Y.card - j)) := by
    intro j hjn
    rcases Nat.eq_zero_or_pos j with rfl | hj1
    · exact Or.inl hlead
    · obtain ⟨T, hT, hTcard, hTbound⟩ := hcong (Y.card - j) (by omega)
      have hTcard' : T.card = j := by rw [hTcard]; omega
      have hQP : ((Z.map fun y => X - C y).prod).coeff (Y.card - j)
          = ((Y.map fun y => X - C y).prod).coeff (Y.card - j)
            - (((Y.map fun y => X - C y).prod)
                - ((Z.map fun y => X - C y).prod)).coeff (Y.card - j) := by
        rw [Polynomial.coeff_sub]
        ring
      rcases lt_or_ge (v (((Y.map fun y => X - C y).prod).coeff (Y.card - j)))
          (v ((((Y.map fun y => X - C y).prod)
            - ((Z.map fun y => X - C y).prod)).coeff (Y.card - j))) with hlt | hge
      · refine Or.inl ?_
        rw [hQP, v.map_sub_eq_of_lt_left hlt]
      · refine Or.inr ⟨T, hT, hTcard', hTbound.trans hge, ?_⟩
        rw [hQP]
        exact v.map_le_sub (hTbound.trans hge) hTbound
  -- transfer the `≤ x` characterization to the profile of `Q`
  have hle₂ : ∀ x : ℚ, IsLeCutIndex
      (fun j => v (((Z.map fun y => X - C y).prod).coeff (Y.card - j)))
      Y.card x ((Y.map v).countP (· ≤ (x : WithTop ℚ))) := by
    intro x
    obtain ⟨hcn, hmin₁, hstrict₁⟩ := isLeCutIndex_countP v Y x
    have hcfilter : (Y.map v).countP (· ≤ (x : WithTop ℚ))
        = (Y.filter fun y => v y ≤ (x : WithTop ℚ)).card := Multiset.countP_map _ _ _
    have hfilter_eq : (Y.map v).filter (· ≤ (x : WithTop ℚ))
        = (Y.filter fun y => v y ≤ (x : WithTop ℚ)).map v := by
      rw [Multiset.filter_map]
      exact congrArg (Multiset.map v) (Multiset.filter_congr fun y _ => Iff.rfl)
    have hindex : (Y.filter fun y => ¬ (v y ≤ (x : WithTop ℚ))).card
        = Y.card - (Y.map v).countP (· ≤ (x : WithTop ℚ)) := by
      have h1 := congrArg Multiset.card
        (Multiset.filter_add_not (fun y => v y ≤ (x : WithTop ℚ)) Y)
      rw [Multiset.card_add] at h1
      omega
    have hcorner : v (((Y.map fun y => X - C y).prod).coeff
          (Y.card - (Y.map v).countP (· ≤ (x : WithTop ℚ))))
        = ((Y.filter fun y => v y ≤ (x : WithTop ℚ)).map v).sum := by
      rw [← hindex]
      exact v_coeff_eq_sum_of_separated v Y _
        (fun y _ hy => (hy.trans_lt (WithTop.coe_lt_top x)).ne)
        (fun y _ hy y' _ hy' => hy.trans_lt (not_le.mp hy'))
    have hLfin : ((Y.filter fun y => v y ≤ (x : WithTop ℚ)).map v).sum ≠ ⊤ := by
      refine sum_ne_top fun a ha => ?_
      obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp ha
      exact ((Multiset.mem_filter.mp hy).2.trans_lt (WithTop.coe_lt_top x)).ne
    -- cut floors against the corner, for arbitrary size-`j` witnesses
    have hfloor : ∀ T : Multiset (WithTop ℚ), T ≤ Y.map v →
        ((Y.filter fun y => v y ≤ (x : WithTop ℚ)).map v).sum + T.card • (x : WithTop ℚ)
          ≤ T.sum + ((Y.map v).countP (· ≤ (x : WithTop ℚ))) • (x : WithTop ℚ) := by
      intro T hT
      have hcut := cut_sum_le (p := (· ≤ (x : WithTop ℚ))) hT
        (fun w _ hw => hw) (fun w _ hw => (not_le.mp hw).le)
      rwa [hfilter_eq, Multiset.card_map, ← hcfilter] at hcut
    have hfloor_lt : ∀ T : Multiset (WithTop ℚ), T ≤ Y.map v →
        (Y.map v).countP (· ≤ (x : WithTop ℚ)) < T.card →
        ((Y.filter fun y => v y ≤ (x : WithTop ℚ)).map v).sum + T.card • (x : WithTop ℚ)
          < T.sum + ((Y.map v).countP (· ≤ (x : WithTop ℚ))) • (x : WithTop ℚ) := by
      intro T hT hc
      have hcut := cut_sum_lt_of_card_lt (p := (· ≤ (x : WithTop ℚ))) hT
        (fun w _ hw => hw) (fun w _ hw => not_le.mp hw)
        (by rw [hfilter_eq, Multiset.card_map, ← hcfilter]; exact hc)
      rwa [hfilter_eq, Multiset.card_map, ← hcfilter] at hcut
    -- the corner of the profile of `Q` matches the corner of `P`
    have hpin : v (((Z.map fun y => X - C y).prod).coeff
          (Y.card - (Y.map v).countP (· ≤ (x : WithTop ℚ))))
        = v (((Y.map fun y => X - C y).prod).coeff
          (Y.card - (Y.map v).countP (· ≤ (x : WithTop ℚ)))) := by
      rcases hdisj _ hcn with heq | ⟨T, hT, hTcard, hTP, hTQ⟩
      · exact heq
      · exfalso
        have h1 : T.sum + (k : WithTop ℚ)
            ≤ ((Y.filter fun y => v y ≤ (x : WithTop ℚ)).map v).sum := by
          rw [← hcorner]
          exact hTP
        have h2 := hfloor T hT
        rw [hTcard] at h2
        have h3 : ((Y.filter fun y => v y ≤ (x : WithTop ℚ)).map v).sum ≤ T.sum :=
          (WithTop.add_le_add_iff_right
            (by rw [← WithTop.coe_nsmul]; exact WithTop.coe_ne_top)).mp h2
        have hTfin : T.sum ≠ ⊤ := by
          intro h0
          rw [h0, WithTop.top_add] at h1
          exact hLfin (top_le_iff.mp h1)
        obtain ⟨q, hq⟩ := WithTop.ne_top_iff_exists.mp hTfin
        obtain ⟨l, hl⟩ := WithTop.ne_top_iff_exists.mp hLfin
        rw [← hq, ← hl] at h1 h3
        rw [← WithTop.coe_add, WithTop.coe_le_coe] at h1
        rw [WithTop.coe_le_coe] at h3
        linarith
    refine ⟨hcn, fun j hjn => ?_, fun j hjn hcj => ?_⟩
    · have hgoal : v (((Z.map fun y => X - C y).prod).coeff
            (Y.card - (Y.map v).countP (· ≤ (x : WithTop ℚ)))) + j • (x : WithTop ℚ)
          ≤ v (((Z.map fun y => X - C y).prod).coeff (Y.card - j))
            + ((Y.map v).countP (· ≤ (x : WithTop ℚ))) • (x : WithTop ℚ) := by
        rcases hdisj j hjn with heq | ⟨T, hT, hTcard, hTP, hTQ⟩
        · rw [hpin, heq]
          exact hmin₁ j hjn
        · rw [hpin, hcorner]
          have h2 := hfloor T hT
          rw [hTcard] at h2
          refine h2.trans (add_le_add_left ?_ _)
          exact le_trans (le_add_of_nonneg_right (by exact_mod_cast hk.le)) hTQ
      exact hgoal
    · have hgoal : v (((Z.map fun y => X - C y).prod).coeff
            (Y.card - (Y.map v).countP (· ≤ (x : WithTop ℚ)))) + j • (x : WithTop ℚ)
          < v (((Z.map fun y => X - C y).prod).coeff (Y.card - j))
            + ((Y.map v).countP (· ≤ (x : WithTop ℚ))) • (x : WithTop ℚ) := by
        rcases hdisj j hjn with heq | ⟨T, hT, hTcard, hTP, hTQ⟩
        · rw [hpin, heq]
          exact hstrict₁ j hjn hcj
        · rw [hpin, hcorner]
          have h2 := hfloor_lt T hT (by rw [hTcard]; exact hcj)
          rw [hTcard] at h2
          refine h2.trans_le (add_le_add_left ?_ _)
          exact le_trans (le_add_of_nonneg_right (by exact_mod_cast hk.le)) hTQ
      exact hgoal
  -- transfer the `< x` characterization to the profile of `Q`
  have hlt₂ : ∀ x : ℚ, IsLtCutIndex
      (fun j => v (((Z.map fun y => X - C y).prod).coeff (Y.card - j)))
      Y.card x ((Y.map v).countP (· < (x : WithTop ℚ))) := by
    intro x
    obtain ⟨hcn, hmin₁, hstrict₁⟩ := isLtCutIndex_countP v Y x
    have hcfilter : (Y.map v).countP (· < (x : WithTop ℚ))
        = (Y.filter fun y => v y < (x : WithTop ℚ)).card := Multiset.countP_map _ _ _
    have hfilter_eq : (Y.map v).filter (· < (x : WithTop ℚ))
        = (Y.filter fun y => v y < (x : WithTop ℚ)).map v := by
      rw [Multiset.filter_map]
      exact congrArg (Multiset.map v) (Multiset.filter_congr fun y _ => Iff.rfl)
    have hindex : (Y.filter fun y => ¬ (v y < (x : WithTop ℚ))).card
        = Y.card - (Y.map v).countP (· < (x : WithTop ℚ)) := by
      have h1 := congrArg Multiset.card
        (Multiset.filter_add_not (fun y => v y < (x : WithTop ℚ)) Y)
      rw [Multiset.card_add] at h1
      omega
    have hcorner : v (((Y.map fun y => X - C y).prod).coeff
          (Y.card - (Y.map v).countP (· < (x : WithTop ℚ))))
        = ((Y.filter fun y => v y < (x : WithTop ℚ)).map v).sum := by
      rw [← hindex]
      exact v_coeff_eq_sum_of_separated v Y _
        (fun y _ hy => (hy.trans (WithTop.coe_lt_top x)).ne)
        (fun y _ hy y' _ hy' => hy.trans_le (not_lt.mp hy'))
    have hLfin : ((Y.filter fun y => v y < (x : WithTop ℚ)).map v).sum ≠ ⊤ := by
      refine sum_ne_top fun a ha => ?_
      obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp ha
      exact ((Multiset.mem_filter.mp hy).2.trans (WithTop.coe_lt_top x)).ne
    have hfloor : ∀ T : Multiset (WithTop ℚ), T ≤ Y.map v →
        ((Y.filter fun y => v y < (x : WithTop ℚ)).map v).sum + T.card • (x : WithTop ℚ)
          ≤ T.sum + ((Y.map v).countP (· < (x : WithTop ℚ))) • (x : WithTop ℚ) := by
      intro T hT
      have hcut := cut_sum_le (p := (· < (x : WithTop ℚ))) hT
        (fun w _ hw => hw.le) (fun w _ hw => not_lt.mp hw)
      rwa [hfilter_eq, Multiset.card_map, ← hcfilter] at hcut
    have hfloor_lt : ∀ T : Multiset (WithTop ℚ), T ≤ Y.map v →
        T.card < (Y.map v).countP (· < (x : WithTop ℚ)) →
        ((Y.filter fun y => v y < (x : WithTop ℚ)).map v).sum + T.card • (x : WithTop ℚ)
          < T.sum + ((Y.map v).countP (· < (x : WithTop ℚ))) • (x : WithTop ℚ) := by
      intro T hT hc
      have hcut := cut_sum_lt_of_lt_card (p := (· < (x : WithTop ℚ))) hT
        (fun w _ hw => hw) (fun w _ hw => not_lt.mp hw)
        (by rw [hfilter_eq, Multiset.card_map, ← hcfilter]; exact hc)
      rwa [hfilter_eq, Multiset.card_map, ← hcfilter] at hcut
    have hpin : v (((Z.map fun y => X - C y).prod).coeff
          (Y.card - (Y.map v).countP (· < (x : WithTop ℚ))))
        = v (((Y.map fun y => X - C y).prod).coeff
          (Y.card - (Y.map v).countP (· < (x : WithTop ℚ)))) := by
      rcases hdisj _ hcn with heq | ⟨T, hT, hTcard, hTP, hTQ⟩
      · exact heq
      · exfalso
        have h1 : T.sum + (k : WithTop ℚ)
            ≤ ((Y.filter fun y => v y < (x : WithTop ℚ)).map v).sum := by
          rw [← hcorner]
          exact hTP
        have h2 := hfloor T hT
        rw [hTcard] at h2
        have h3 : ((Y.filter fun y => v y < (x : WithTop ℚ)).map v).sum ≤ T.sum :=
          (WithTop.add_le_add_iff_right
            (by rw [← WithTop.coe_nsmul]; exact WithTop.coe_ne_top)).mp h2
        have hTfin : T.sum ≠ ⊤ := by
          intro h0
          rw [h0, WithTop.top_add] at h1
          exact hLfin (top_le_iff.mp h1)
        obtain ⟨q, hq⟩ := WithTop.ne_top_iff_exists.mp hTfin
        obtain ⟨l, hl⟩ := WithTop.ne_top_iff_exists.mp hLfin
        rw [← hq, ← hl] at h1 h3
        rw [← WithTop.coe_add, WithTop.coe_le_coe] at h1
        rw [WithTop.coe_le_coe] at h3
        linarith
    refine ⟨hcn, fun j hjn => ?_, fun j hjn hjc => ?_⟩
    · have hgoal : v (((Z.map fun y => X - C y).prod).coeff
            (Y.card - (Y.map v).countP (· < (x : WithTop ℚ)))) + j • (x : WithTop ℚ)
          ≤ v (((Z.map fun y => X - C y).prod).coeff (Y.card - j))
            + ((Y.map v).countP (· < (x : WithTop ℚ))) • (x : WithTop ℚ) := by
        rcases hdisj j hjn with heq | ⟨T, hT, hTcard, hTP, hTQ⟩
        · rw [hpin, heq]
          exact hmin₁ j hjn
        · rw [hpin, hcorner]
          have h2 := hfloor T hT
          rw [hTcard] at h2
          refine h2.trans (add_le_add_left ?_ _)
          exact le_trans (le_add_of_nonneg_right (by exact_mod_cast hk.le)) hTQ
      exact hgoal
    · have hgoal : v (((Z.map fun y => X - C y).prod).coeff
            (Y.card - (Y.map v).countP (· < (x : WithTop ℚ)))) + j • (x : WithTop ℚ)
          < v (((Z.map fun y => X - C y).prod).coeff (Y.card - j))
            + ((Y.map v).countP (· < (x : WithTop ℚ))) • (x : WithTop ℚ) := by
        rcases hdisj j hjn with heq | ⟨T, hT, hTcard, hTP, hTQ⟩
        · rw [hpin, heq]
          exact hstrict₁ j hjn hjc
        · rw [hpin, hcorner]
          have h2 := hfloor_lt T hT (by rw [hTcard]; exact hjc)
          rw [hTcard] at h2
          refine h2.trans_le (add_le_add_left ?_ _)
          exact le_trans (le_add_of_nonneg_right (by exact_mod_cast hk.le)) hTQ
      exact hgoal
  -- transfer the finite-count characterization to the profile of `Q`
  have htop₂ : IsTopIndex
      (fun j => v (((Z.map fun y => X - C y).prod).coeff (Y.card - j)))
      Y.card ((Y.map v).countP (fun w => w ≠ ⊤)) := by
    obtain ⟨hcn, hfin₁, htop₁⟩ := isTopIndex_countP v hv Y
    have hcfilter : (Y.map v).countP (fun w => w ≠ ⊤)
        = (Y.filter fun y => v y ≠ ⊤).card := Multiset.countP_map _ _ _
    have hfilter_eq : (Y.map v).filter (fun w => w ≠ ⊤)
        = (Y.filter fun y => v y ≠ ⊤).map v := by
      rw [Multiset.filter_map]
      exact congrArg (Multiset.map v) (Multiset.filter_congr fun y _ => Iff.rfl)
    have hindex : (Y.filter fun y => ¬ (v y ≠ ⊤)).card
        = Y.card - (Y.map v).countP (fun w => w ≠ ⊤) := by
      have h1 := congrArg Multiset.card (Multiset.filter_add_not (fun y => v y ≠ ⊤) Y)
      rw [Multiset.card_add] at h1
      omega
    have hcorner : v (((Y.map fun y => X - C y).prod).coeff
          (Y.card - (Y.map v).countP (fun w => w ≠ ⊤)))
        = ((Y.filter fun y => v y ≠ ⊤).map v).sum := by
      rw [← hindex]
      exact v_coeff_eq_sum_of_separated v Y _ (fun y _ hy => hy)
        (fun y _ hy y' _ hy' =>
          lt_of_lt_of_eq (lt_top_iff_ne_top.mpr hy) (not_not.mp hy').symm)
    have hLfin : ((Y.filter fun y => v y ≠ ⊤).map v).sum ≠ ⊤ := by
      refine sum_ne_top fun a ha => ?_
      obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp ha
      exact (Multiset.mem_filter.mp hy).2
    refine ⟨hcn, ?_, fun j hjn hcj => ?_⟩
    · have hgoal : v (((Z.map fun y => X - C y).prod).coeff
            (Y.card - (Y.map v).countP (fun w => w ≠ ⊤))) ≠ ⊤ := by
        rcases hdisj _ hcn with heq | ⟨T, hT, hTcard, hTP, hTQ⟩
        · rw [heq]
          exact hfin₁
        · exfalso
          have hTfin : T.sum ≠ ⊤ := by
            intro h0
            rw [h0, WithTop.top_add, hcorner] at hTP
            exact hLfin (top_le_iff.mp hTP)
          -- a size-`count` sub-multiset of finite sum is the finite part itself
          have hTsub : T ≤ (Y.map v).filter (fun w => w ≠ ⊤) :=
            Multiset.le_filter.mpr ⟨hT, fun a ha => ne_top_of_mem_of_sum_ne_top hTfin ha⟩
          have hTeq : T = (Y.map v).filter (fun w => w ≠ ⊤) := by
            refine Multiset.eq_of_le_of_card_le hTsub ?_
            rw [hTcard, Multiset.countP_eq_card_filter]
          have hTsum : T.sum = ((Y.filter fun y => v y ≠ ⊤).map v).sum := by
            rw [hTeq, hfilter_eq]
          rw [hcorner, hTsum] at hTP
          obtain ⟨l, hl⟩ := WithTop.ne_top_iff_exists.mp hLfin
          rw [← hl, ← WithTop.coe_add, WithTop.coe_le_coe] at hTP
          linarith
      exact hgoal
    · have hgoal : v (((Z.map fun y => X - C y).prod).coeff (Y.card - j)) = ⊤ := by
        rcases hdisj j hjn with heq | ⟨T, hT, hTcard, hTP, hTQ⟩
        · rw [heq]
          exact htop₁ j hjn hcj
        · -- a sub-multiset larger than the finite part contains an `∞` entry
          have hTtop : T.sum = ⊤ := by
            by_contra h0
            have hTsub : T ≤ (Y.map v).filter (fun w => w ≠ ⊤) :=
              Multiset.le_filter.mpr ⟨hT, fun a ha => ne_top_of_mem_of_sum_ne_top h0 ha⟩
            have hle := Multiset.card_le_card hTsub
            rw [hTcard, ← Multiset.countP_eq_card_filter] at hle
            omega
          rw [hTtop, WithTop.top_add] at hTQ
          exact top_le_iff.mp hTQ
      exact hgoal
  -- the counts agree, and multiset extensionality on counts concludes
  have htop_eq : (Z.map v).countP (fun w => w ≠ ⊤) = (Y.map v).countP (fun w => w ≠ ⊤) := by
    have h₂ := isTopIndex_countP v hv Z
    rw [← hcard] at h₂
    exact h₂.unique htop₂
  have hle_eq : ∀ x : ℚ, (Z.map v).countP (· ≤ (x : WithTop ℚ))
      = (Y.map v).countP (· ≤ (x : WithTop ℚ)) := by
    intro x
    have h₂ := isLeCutIndex_countP v Z x
    rw [← hcard] at h₂
    exact h₂.unique (hle₂ x)
  have hlt_eq : ∀ x : ℚ, (Z.map v).countP (· < (x : WithTop ℚ))
      = (Y.map v).countP (· < (x : WithTop ℚ)) := by
    intro x
    have h₂ := isLtCutIndex_countP v Z x
    rw [← hcard] at h₂
    exact h₂.unique (hlt₂ x)
  refine multiset_eq_of_countP_cuts ?_ htop_eq hle_eq hlt_eq
  rw [Multiset.card_map, Multiset.card_map]
  exact hcard.symm

/-! ### Θ-capped congruence robustness

For the reverse propagation the congruence floors are only available after capping
the root valuations at a threshold `Θ`: the witnesses are sub-multisets of the
capped multiset `(Y.map v).map (fun w => min w Θ)`.  Below the cap (`x < Θ` for
`≤`-cuts, `x ≤ Θ` for `<`-cuts) capping changes neither the filters nor the
counts, and every cut at or beyond the cap is full; this suffices to pin the
capped valuation multiset of `Z`. -/

private theorem min_le_coe_iff_of_lt {w : WithTop ℚ} {x Θ : ℚ} (hx : x < Θ) :
    min w (Θ : WithTop ℚ) ≤ (x : WithTop ℚ) ↔ w ≤ (x : WithTop ℚ) :=
  ⟨fun h => (min_le_iff.mp h).resolve_right (not_le.mpr (WithTop.coe_lt_coe.mpr hx)),
    fun h => (min_le_left _ _).trans h⟩

private theorem min_lt_coe_iff_of_le {w : WithTop ℚ} {x Θ : ℚ} (hx : x ≤ Θ) :
    min w (Θ : WithTop ℚ) < (x : WithTop ℚ) ↔ w < (x : WithTop ℚ) :=
  ⟨fun h => (min_lt_iff.mp h).resolve_right (not_lt.mpr (WithTop.coe_le_coe.mpr hx)),
    fun h => (min_le_left _ _).trans_lt h⟩

/-- Below the cap, capping does not change the `≤ x` filter — even as a multiset. -/
theorem filter_le_map_min_of_lt {W : Multiset (WithTop ℚ)} {x Θ : ℚ} (hx : x < Θ) :
    (W.map fun w => min w (Θ : WithTop ℚ)).filter (· ≤ (x : WithTop ℚ))
      = W.filter (· ≤ (x : WithTop ℚ)) := by
  classical
  have h1 : (W.map fun w => min w (Θ : WithTop ℚ)).filter (· ≤ (x : WithTop ℚ))
      = (W.filter (· ≤ (x : WithTop ℚ))).map (fun w => min w (Θ : WithTop ℚ)) := by
    rw [Multiset.filter_map]
    exact congrArg (Multiset.map _) (Multiset.filter_congr fun w _ => min_le_coe_iff_of_lt hx)
  have h2 : (W.filter (· ≤ (x : WithTop ℚ))).map (fun w => min w (Θ : WithTop ℚ))
      = (W.filter (· ≤ (x : WithTop ℚ))).map id :=
    Multiset.map_congr rfl fun w hw =>
      min_eq_left (le_trans (Multiset.mem_filter.mp hw).2 (WithTop.coe_le_coe.mpr hx.le))
  rw [h1, h2, Multiset.map_id]

/-- At or below the cap, capping does not change the `< x` filter — even as a multiset. -/
theorem filter_lt_map_min_of_le {W : Multiset (WithTop ℚ)} {x Θ : ℚ} (hx : x ≤ Θ) :
    (W.map fun w => min w (Θ : WithTop ℚ)).filter (· < (x : WithTop ℚ))
      = W.filter (· < (x : WithTop ℚ)) := by
  classical
  have h1 : (W.map fun w => min w (Θ : WithTop ℚ)).filter (· < (x : WithTop ℚ))
      = (W.filter (· < (x : WithTop ℚ))).map (fun w => min w (Θ : WithTop ℚ)) := by
    rw [Multiset.filter_map]
    exact congrArg (Multiset.map _) (Multiset.filter_congr fun w _ => min_lt_coe_iff_of_le hx)
  have h2 : (W.filter (· < (x : WithTop ℚ))).map (fun w => min w (Θ : WithTop ℚ))
      = (W.filter (· < (x : WithTop ℚ))).map id :=
    Multiset.map_congr rfl fun w hw =>
      min_eq_left (le_trans (le_of_lt (Multiset.mem_filter.mp hw).2) (WithTop.coe_le_coe.mpr hx))
  rw [h1, h2, Multiset.map_id]

/-- Below the cap, capping does not change the `≤ x` count. -/
theorem countP_le_map_min_of_lt {W : Multiset (WithTop ℚ)} {x Θ : ℚ} (hx : x < Θ) :
    (W.map fun w => min w (Θ : WithTop ℚ)).countP (· ≤ (x : WithTop ℚ))
      = W.countP (· ≤ (x : WithTop ℚ)) := by
  classical
  rw [Multiset.countP_eq_card_filter, Multiset.countP_eq_card_filter, filter_le_map_min_of_lt hx]

/-- At or below the cap, capping does not change the `< x` count. -/
theorem countP_lt_map_min_of_le {W : Multiset (WithTop ℚ)} {x Θ : ℚ} (hx : x ≤ Θ) :
    (W.map fun w => min w (Θ : WithTop ℚ)).countP (· < (x : WithTop ℚ))
      = W.countP (· < (x : WithTop ℚ)) := by
  classical
  rw [Multiset.countP_eq_card_filter, Multiset.countP_eq_card_filter, filter_lt_map_min_of_le hx]

/-- At or beyond the cap, the `≤ x` cut of a capped multiset is full. -/
theorem countP_le_map_min_of_ge {W : Multiset (WithTop ℚ)} {x Θ : ℚ} (hx : Θ ≤ x) :
    (W.map fun w => min w (Θ : WithTop ℚ)).countP (· ≤ (x : WithTop ℚ)) = W.card := by
  classical
  have h : ∀ a ∈ W.map (fun w => min w (Θ : WithTop ℚ)), a ≤ (x : WithTop ℚ) := by
    intro a ha
    obtain ⟨w, -, rfl⟩ := Multiset.mem_map.mp ha
    exact (min_le_right _ _).trans (WithTop.coe_le_coe.mpr hx)
  rw [Multiset.countP_eq_card.mpr h, Multiset.card_map]

/-- Beyond the cap, the `< x` cut of a capped multiset is full. -/
theorem countP_lt_map_min_of_gt {W : Multiset (WithTop ℚ)} {x Θ : ℚ} (hx : Θ < x) :
    (W.map fun w => min w (Θ : WithTop ℚ)).countP (· < (x : WithTop ℚ)) = W.card := by
  classical
  have h : ∀ a ∈ W.map (fun w => min w (Θ : WithTop ℚ)), a < (x : WithTop ℚ) := by
    intro a ha
    obtain ⟨w, -, rfl⟩ := Multiset.mem_map.mp ha
    exact (min_le_right _ _).trans_lt (WithTop.coe_lt_coe.mpr hx)
  rw [Multiset.countP_eq_card.mpr h, Multiset.card_map]

/-- Capped multisets have no `∞` entries: the finite-entry count is full. -/
theorem countP_ne_top_map_min {W : Multiset (WithTop ℚ)} {Θ : ℚ} :
    (W.map fun w => min w (Θ : WithTop ℚ)).countP (fun w => w ≠ ⊤) = W.card := by
  classical
  have h : ∀ a ∈ W.map (fun w => min w (Θ : WithTop ℚ)), a ≠ ⊤ := by
    intro a ha
    obtain ⟨w, -, rfl⟩ := Multiset.mem_map.mp ha
    exact ((min_le_right w _).trans_lt (WithTop.coe_lt_top Θ)).ne
  rw [Multiset.countP_eq_card.mpr h, Multiset.card_map]

/-- **The Θ-capped Newton-polygon dictionary is congruence-robust**
(`lem:polygon-congruence-capped`; Kedlaya 2001b, Section 3).  Let `Y, Z` be root
multisets of the same size `n` over a commutative ring carrying a
`ℚ ∪ {∞}`-valued additive valuation `v`, and write `P = ∏_{y ∈ Y}(X - y)`,
`Q = ∏_{z ∈ Z}(X - z)`.  If for some `k > 0` every coefficient difference is
floored as `T.sum + k ≤ v ((P - Q).coeff i)` by a size-`(n - i)` sub-multiset
`T` of the `Θ`-capped valuation multiset `(Y.map v).map (fun w => min w Θ)`,
then the `Θ`-capped valuation multisets of `Z` and `Y` coincide.

This is the `Θ`-capped variant of `map_v_eq_of_v_coeff_sub`, used by the reverse
propagation (Kedlaya 2001b, Section 3).  The hypothesis is weaker — capped
floors are smaller — and the conclusion correspondingly weaker: only the capped
multisets are pinned.  Cuts below the cap (`x < Θ` for `≤`-cuts, `x ≤ Θ` for
`<`-cuts) see no difference between the capped and uncapped multisets, so the
extreme-minimizer characterizations still transfer there, while every cut at or
beyond the cap is full on both sides.  No hypothesis on `∞`-valued elements is
needed: capped multisets have no `∞` entries, so the `∞`-count comparison is
trivial. -/
theorem map_v_min_eq_of_v_coeff_sub [Nontrivial F]
    (Y Z : Multiset F) (hcard : Y.card = Z.card) {Θ : ℚ} {k : ℚ} (hk : 0 < k)
    (hcong : ∀ i < Y.card, ∃ T ≤ (Y.map v).map (fun w => min w (Θ : WithTop ℚ)),
      T.card = Y.card - i ∧
      T.sum + (k : WithTop ℚ) ≤
        v ((((Y.map fun y => X - C y).prod) - ((Z.map fun y => X - C y).prod)).coeff i)) :
    (Z.map v).map (fun w => min w (Θ : WithTop ℚ))
      = (Y.map v).map (fun w => min w (Θ : WithTop ℚ)) := by
  classical
  -- both products are monic of degree `Y.card`
  have hPmonic : ((Y.map fun y => X - C y).prod).Monic :=
    monic_multiset_prod_of_monic _ _ fun y _ => monic_X_sub_C y
  have hQmonic : ((Z.map fun y => X - C y).prod).Monic :=
    monic_multiset_prod_of_monic _ _ fun y _ => monic_X_sub_C y
  have hPdeg : ((Y.map fun y => X - C y).prod).natDegree = Y.card :=
    natDegree_multiset_prod_X_sub_C_eq_card Y
  have hQdeg : ((Z.map fun y => X - C y).prod).natDegree = Y.card := by
    rw [natDegree_multiset_prod_X_sub_C_eq_card, hcard]
  have hlead : v (((Z.map fun y => X - C y).prod).coeff (Y.card - 0))
      = v (((Y.map fun y => X - C y).prod).coeff (Y.card - 0)) := by
    rw [Nat.sub_zero]
    conv_lhs => rw [← hQdeg, hQmonic.coeff_natDegree]
    conv_rhs => rw [← hPdeg, hPmonic.coeff_natDegree]
  -- coefficientwise, below the congruence depth the two valuation profiles agree;
  -- at or above it, both sides clear the capped floor `T.sum + k`
  have hdisj : ∀ j ≤ Y.card,
      v (((Z.map fun y => X - C y).prod).coeff (Y.card - j))
        = v (((Y.map fun y => X - C y).prod).coeff (Y.card - j)) ∨
      ∃ T ≤ (Y.map v).map (fun w => min w (Θ : WithTop ℚ)), T.card = j ∧
        T.sum + (k : WithTop ℚ)
          ≤ v (((Y.map fun y => X - C y).prod).coeff (Y.card - j)) ∧
        T.sum + (k : WithTop ℚ)
          ≤ v (((Z.map fun y => X - C y).prod).coeff (Y.card - j)) := by
    intro j hjn
    rcases Nat.eq_zero_or_pos j with rfl | hj1
    · exact Or.inl hlead
    · obtain ⟨T, hT, hTcard, hTbound⟩ := hcong (Y.card - j) (by omega)
      have hTcard' : T.card = j := by rw [hTcard]; omega
      have hQP : ((Z.map fun y => X - C y).prod).coeff (Y.card - j)
          = ((Y.map fun y => X - C y).prod).coeff (Y.card - j)
            - (((Y.map fun y => X - C y).prod)
                - ((Z.map fun y => X - C y).prod)).coeff (Y.card - j) := by
        rw [Polynomial.coeff_sub]
        ring
      rcases lt_or_ge (v (((Y.map fun y => X - C y).prod).coeff (Y.card - j)))
          (v ((((Y.map fun y => X - C y).prod)
            - ((Z.map fun y => X - C y).prod)).coeff (Y.card - j))) with hlt | hge
      · refine Or.inl ?_
        rw [hQP, v.map_sub_eq_of_lt_left hlt]
      · refine Or.inr ⟨T, hT, hTcard', hTbound.trans hge, ?_⟩
        rw [hQP]
        exact v.map_le_sub (hTbound.trans hge) hTbound
  -- transfer the `≤ x` characterization, below the cap, to the profile of `Q`
  have hle₂ : ∀ x : ℚ, x < Θ → IsLeCutIndex
      (fun j => v (((Z.map fun y => X - C y).prod).coeff (Y.card - j)))
      Y.card x ((Y.map v).countP (· ≤ (x : WithTop ℚ))) := by
    intro x hx
    obtain ⟨hcn, hmin₁, hstrict₁⟩ := isLeCutIndex_countP v Y x
    have hcfilter : (Y.map v).countP (· ≤ (x : WithTop ℚ))
        = (Y.filter fun y => v y ≤ (x : WithTop ℚ)).card := Multiset.countP_map _ _ _
    have hfilter_eq : (Y.map v).filter (· ≤ (x : WithTop ℚ))
        = (Y.filter fun y => v y ≤ (x : WithTop ℚ)).map v := by
      rw [Multiset.filter_map]
      exact congrArg (Multiset.map v) (Multiset.filter_congr fun y _ => Iff.rfl)
    have hindex : (Y.filter fun y => ¬ (v y ≤ (x : WithTop ℚ))).card
        = Y.card - (Y.map v).countP (· ≤ (x : WithTop ℚ)) := by
      have h1 := congrArg Multiset.card
        (Multiset.filter_add_not (fun y => v y ≤ (x : WithTop ℚ)) Y)
      rw [Multiset.card_add] at h1
      omega
    have hcorner : v (((Y.map fun y => X - C y).prod).coeff
          (Y.card - (Y.map v).countP (· ≤ (x : WithTop ℚ))))
        = ((Y.filter fun y => v y ≤ (x : WithTop ℚ)).map v).sum := by
      rw [← hindex]
      exact v_coeff_eq_sum_of_separated v Y _
        (fun y _ hy => (hy.trans_lt (WithTop.coe_lt_top x)).ne)
        (fun y _ hy y' _ hy' => hy.trans_lt (not_le.mp hy'))
    have hLfin : ((Y.filter fun y => v y ≤ (x : WithTop ℚ)).map v).sum ≠ ⊤ := by
      refine sum_ne_top fun a ha => ?_
      obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp ha
      exact ((Multiset.mem_filter.mp hy).2.trans_lt (WithTop.coe_lt_top x)).ne
    -- cut floors against the corner, for arbitrary capped size-`j` witnesses
    have hfloor : ∀ T : Multiset (WithTop ℚ),
        T ≤ (Y.map v).map (fun w => min w (Θ : WithTop ℚ)) →
        ((Y.filter fun y => v y ≤ (x : WithTop ℚ)).map v).sum + T.card • (x : WithTop ℚ)
          ≤ T.sum + ((Y.map v).countP (· ≤ (x : WithTop ℚ))) • (x : WithTop ℚ) := by
      intro T hT
      have hcut := cut_sum_le (p := (· ≤ (x : WithTop ℚ))) hT
        (fun w _ hw => hw) (fun w _ hw => (not_le.mp hw).le)
      rwa [filter_le_map_min_of_lt hx, hfilter_eq, Multiset.card_map, ← hcfilter] at hcut
    have hfloor_lt : ∀ T : Multiset (WithTop ℚ),
        T ≤ (Y.map v).map (fun w => min w (Θ : WithTop ℚ)) →
        (Y.map v).countP (· ≤ (x : WithTop ℚ)) < T.card →
        ((Y.filter fun y => v y ≤ (x : WithTop ℚ)).map v).sum + T.card • (x : WithTop ℚ)
          < T.sum + ((Y.map v).countP (· ≤ (x : WithTop ℚ))) • (x : WithTop ℚ) := by
      intro T hT hc
      have hcut := cut_sum_lt_of_card_lt (p := (· ≤ (x : WithTop ℚ))) hT
        (fun w _ hw => hw) (fun w _ hw => not_le.mp hw)
        (by rw [filter_le_map_min_of_lt hx, hfilter_eq, Multiset.card_map, ← hcfilter]; exact hc)
      rwa [filter_le_map_min_of_lt hx, hfilter_eq, Multiset.card_map, ← hcfilter] at hcut
    -- the corner of the profile of `Q` matches the corner of `P`
    have hpin : v (((Z.map fun y => X - C y).prod).coeff
          (Y.card - (Y.map v).countP (· ≤ (x : WithTop ℚ))))
        = v (((Y.map fun y => X - C y).prod).coeff
          (Y.card - (Y.map v).countP (· ≤ (x : WithTop ℚ)))) := by
      rcases hdisj _ hcn with heq | ⟨T, hT, hTcard, hTP, hTQ⟩
      · exact heq
      · exfalso
        have h1 : T.sum + (k : WithTop ℚ)
            ≤ ((Y.filter fun y => v y ≤ (x : WithTop ℚ)).map v).sum := by
          rw [← hcorner]
          exact hTP
        have h2 := hfloor T hT
        rw [hTcard] at h2
        have h3 : ((Y.filter fun y => v y ≤ (x : WithTop ℚ)).map v).sum ≤ T.sum :=
          (WithTop.add_le_add_iff_right
            (by rw [← WithTop.coe_nsmul]; exact WithTop.coe_ne_top)).mp h2
        have hTfin : T.sum ≠ ⊤ := by
          intro h0
          rw [h0, WithTop.top_add] at h1
          exact hLfin (top_le_iff.mp h1)
        obtain ⟨q, hq⟩ := WithTop.ne_top_iff_exists.mp hTfin
        obtain ⟨l, hl⟩ := WithTop.ne_top_iff_exists.mp hLfin
        rw [← hq, ← hl] at h1 h3
        rw [← WithTop.coe_add, WithTop.coe_le_coe] at h1
        rw [WithTop.coe_le_coe] at h3
        linarith
    refine ⟨hcn, fun j hjn => ?_, fun j hjn hcj => ?_⟩
    · have hgoal : v (((Z.map fun y => X - C y).prod).coeff
            (Y.card - (Y.map v).countP (· ≤ (x : WithTop ℚ)))) + j • (x : WithTop ℚ)
          ≤ v (((Z.map fun y => X - C y).prod).coeff (Y.card - j))
            + ((Y.map v).countP (· ≤ (x : WithTop ℚ))) • (x : WithTop ℚ) := by
        rcases hdisj j hjn with heq | ⟨T, hT, hTcard, hTP, hTQ⟩
        · rw [hpin, heq]
          exact hmin₁ j hjn
        · rw [hpin, hcorner]
          have h2 := hfloor T hT
          rw [hTcard] at h2
          refine h2.trans (add_le_add_left ?_ _)
          exact le_trans (le_add_of_nonneg_right (by exact_mod_cast hk.le)) hTQ
      exact hgoal
    · have hgoal : v (((Z.map fun y => X - C y).prod).coeff
            (Y.card - (Y.map v).countP (· ≤ (x : WithTop ℚ)))) + j • (x : WithTop ℚ)
          < v (((Z.map fun y => X - C y).prod).coeff (Y.card - j))
            + ((Y.map v).countP (· ≤ (x : WithTop ℚ))) • (x : WithTop ℚ) := by
        rcases hdisj j hjn with heq | ⟨T, hT, hTcard, hTP, hTQ⟩
        · rw [hpin, heq]
          exact hstrict₁ j hjn hcj
        · rw [hpin, hcorner]
          have h2 := hfloor_lt T hT (by rw [hTcard]; exact hcj)
          rw [hTcard] at h2
          refine h2.trans_le (add_le_add_left ?_ _)
          exact le_trans (le_add_of_nonneg_right (by exact_mod_cast hk.le)) hTQ
      exact hgoal
  -- transfer the `< x` characterization, at or below the cap, to the profile of `Q`
  have hlt₂ : ∀ x : ℚ, x ≤ Θ → IsLtCutIndex
      (fun j => v (((Z.map fun y => X - C y).prod).coeff (Y.card - j)))
      Y.card x ((Y.map v).countP (· < (x : WithTop ℚ))) := by
    intro x hx
    obtain ⟨hcn, hmin₁, hstrict₁⟩ := isLtCutIndex_countP v Y x
    have hcfilter : (Y.map v).countP (· < (x : WithTop ℚ))
        = (Y.filter fun y => v y < (x : WithTop ℚ)).card := Multiset.countP_map _ _ _
    have hfilter_eq : (Y.map v).filter (· < (x : WithTop ℚ))
        = (Y.filter fun y => v y < (x : WithTop ℚ)).map v := by
      rw [Multiset.filter_map]
      exact congrArg (Multiset.map v) (Multiset.filter_congr fun y _ => Iff.rfl)
    have hindex : (Y.filter fun y => ¬ (v y < (x : WithTop ℚ))).card
        = Y.card - (Y.map v).countP (· < (x : WithTop ℚ)) := by
      have h1 := congrArg Multiset.card
        (Multiset.filter_add_not (fun y => v y < (x : WithTop ℚ)) Y)
      rw [Multiset.card_add] at h1
      omega
    have hcorner : v (((Y.map fun y => X - C y).prod).coeff
          (Y.card - (Y.map v).countP (· < (x : WithTop ℚ))))
        = ((Y.filter fun y => v y < (x : WithTop ℚ)).map v).sum := by
      rw [← hindex]
      exact v_coeff_eq_sum_of_separated v Y _
        (fun y _ hy => (hy.trans (WithTop.coe_lt_top x)).ne)
        (fun y _ hy y' _ hy' => hy.trans_le (not_lt.mp hy'))
    have hLfin : ((Y.filter fun y => v y < (x : WithTop ℚ)).map v).sum ≠ ⊤ := by
      refine sum_ne_top fun a ha => ?_
      obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp ha
      exact ((Multiset.mem_filter.mp hy).2.trans (WithTop.coe_lt_top x)).ne
    have hfloor : ∀ T : Multiset (WithTop ℚ),
        T ≤ (Y.map v).map (fun w => min w (Θ : WithTop ℚ)) →
        ((Y.filter fun y => v y < (x : WithTop ℚ)).map v).sum + T.card • (x : WithTop ℚ)
          ≤ T.sum + ((Y.map v).countP (· < (x : WithTop ℚ))) • (x : WithTop ℚ) := by
      intro T hT
      have hcut := cut_sum_le (p := (· < (x : WithTop ℚ))) hT
        (fun w _ hw => hw.le) (fun w _ hw => not_lt.mp hw)
      rwa [filter_lt_map_min_of_le hx, hfilter_eq, Multiset.card_map, ← hcfilter] at hcut
    have hfloor_lt : ∀ T : Multiset (WithTop ℚ),
        T ≤ (Y.map v).map (fun w => min w (Θ : WithTop ℚ)) →
        T.card < (Y.map v).countP (· < (x : WithTop ℚ)) →
        ((Y.filter fun y => v y < (x : WithTop ℚ)).map v).sum + T.card • (x : WithTop ℚ)
          < T.sum + ((Y.map v).countP (· < (x : WithTop ℚ))) • (x : WithTop ℚ) := by
      intro T hT hc
      have hcut := cut_sum_lt_of_lt_card (p := (· < (x : WithTop ℚ))) hT
        (fun w _ hw => hw) (fun w _ hw => not_lt.mp hw)
        (by rw [filter_lt_map_min_of_le hx, hfilter_eq, Multiset.card_map, ← hcfilter]; exact hc)
      rwa [filter_lt_map_min_of_le hx, hfilter_eq, Multiset.card_map, ← hcfilter] at hcut
    have hpin : v (((Z.map fun y => X - C y).prod).coeff
          (Y.card - (Y.map v).countP (· < (x : WithTop ℚ))))
        = v (((Y.map fun y => X - C y).prod).coeff
          (Y.card - (Y.map v).countP (· < (x : WithTop ℚ)))) := by
      rcases hdisj _ hcn with heq | ⟨T, hT, hTcard, hTP, hTQ⟩
      · exact heq
      · exfalso
        have h1 : T.sum + (k : WithTop ℚ)
            ≤ ((Y.filter fun y => v y < (x : WithTop ℚ)).map v).sum := by
          rw [← hcorner]
          exact hTP
        have h2 := hfloor T hT
        rw [hTcard] at h2
        have h3 : ((Y.filter fun y => v y < (x : WithTop ℚ)).map v).sum ≤ T.sum :=
          (WithTop.add_le_add_iff_right
            (by rw [← WithTop.coe_nsmul]; exact WithTop.coe_ne_top)).mp h2
        have hTfin : T.sum ≠ ⊤ := by
          intro h0
          rw [h0, WithTop.top_add] at h1
          exact hLfin (top_le_iff.mp h1)
        obtain ⟨q, hq⟩ := WithTop.ne_top_iff_exists.mp hTfin
        obtain ⟨l, hl⟩ := WithTop.ne_top_iff_exists.mp hLfin
        rw [← hq, ← hl] at h1 h3
        rw [← WithTop.coe_add, WithTop.coe_le_coe] at h1
        rw [WithTop.coe_le_coe] at h3
        linarith
    refine ⟨hcn, fun j hjn => ?_, fun j hjn hjc => ?_⟩
    · have hgoal : v (((Z.map fun y => X - C y).prod).coeff
            (Y.card - (Y.map v).countP (· < (x : WithTop ℚ)))) + j • (x : WithTop ℚ)
          ≤ v (((Z.map fun y => X - C y).prod).coeff (Y.card - j))
            + ((Y.map v).countP (· < (x : WithTop ℚ))) • (x : WithTop ℚ) := by
        rcases hdisj j hjn with heq | ⟨T, hT, hTcard, hTP, hTQ⟩
        · rw [hpin, heq]
          exact hmin₁ j hjn
        · rw [hpin, hcorner]
          have h2 := hfloor T hT
          rw [hTcard] at h2
          refine h2.trans (add_le_add_left ?_ _)
          exact le_trans (le_add_of_nonneg_right (by exact_mod_cast hk.le)) hTQ
      exact hgoal
    · have hgoal : v (((Z.map fun y => X - C y).prod).coeff
            (Y.card - (Y.map v).countP (· < (x : WithTop ℚ)))) + j • (x : WithTop ℚ)
          < v (((Z.map fun y => X - C y).prod).coeff (Y.card - j))
            + ((Y.map v).countP (· < (x : WithTop ℚ))) • (x : WithTop ℚ) := by
        rcases hdisj j hjn with heq | ⟨T, hT, hTcard, hTP, hTQ⟩
        · rw [hpin, heq]
          exact hstrict₁ j hjn hjc
        · rw [hpin, hcorner]
          have h2 := hfloor_lt T hT (by rw [hTcard]; exact hjc)
          rw [hTcard] at h2
          refine h2.trans_le (add_le_add_left ?_ _)
          exact le_trans (le_add_of_nonneg_right (by exact_mod_cast hk.le)) hTQ
      exact hgoal
  -- the capped counts agree, and multiset extensionality on counts concludes
  have htop_eq : ((Z.map v).map (fun w => min w (Θ : WithTop ℚ))).countP (fun w => w ≠ ⊤)
      = ((Y.map v).map (fun w => min w (Θ : WithTop ℚ))).countP (fun w => w ≠ ⊤) := by
    rw [countP_ne_top_map_min, countP_ne_top_map_min, Multiset.card_map, Multiset.card_map,
      hcard]
  have hle_eq : ∀ x : ℚ,
      ((Z.map v).map (fun w => min w (Θ : WithTop ℚ))).countP (· ≤ (x : WithTop ℚ))
        = ((Y.map v).map (fun w => min w (Θ : WithTop ℚ))).countP (· ≤ (x : WithTop ℚ)) := by
    intro x
    rcases lt_or_ge x Θ with hx | hx
    · rw [countP_le_map_min_of_lt hx, countP_le_map_min_of_lt hx]
      have h₂ := isLeCutIndex_countP v Z x
      rw [← hcard] at h₂
      exact h₂.unique (hle₂ x hx)
    · rw [countP_le_map_min_of_ge hx, countP_le_map_min_of_ge hx, Multiset.card_map,
        Multiset.card_map, hcard]
  have hlt_eq : ∀ x : ℚ,
      ((Z.map v).map (fun w => min w (Θ : WithTop ℚ))).countP (· < (x : WithTop ℚ))
        = ((Y.map v).map (fun w => min w (Θ : WithTop ℚ))).countP (· < (x : WithTop ℚ)) := by
    intro x
    rcases lt_or_ge Θ x with hx | hx
    · rw [countP_lt_map_min_of_gt hx, countP_lt_map_min_of_gt hx, Multiset.card_map,
        Multiset.card_map, hcard]
    · rw [countP_lt_map_min_of_le hx, countP_lt_map_min_of_le hx]
      have h₂ := isLtCutIndex_countP v Z x
      rw [← hcard] at h₂
      exact h₂.unique (hlt₂ x hx)
  refine multiset_eq_of_countP_cuts ?_ htop_eq hle_eq hlt_eq
  rw [Multiset.card_map, Multiset.card_map, Multiset.card_map, Multiset.card_map]
  exact hcard.symm

end TrustworthyKedlaya
