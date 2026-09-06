/-
Copyright (c) 2026 Shanwen Wang, Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import TrustworthyKedlaya.Kedlaya.ShadowCollapse

/-!
# Sums of shadows have UP truncations

The truncation engine behind the truncationwise-UP predicate `IsTruncUP`
(`TrustworthyKedlaya.Kedlaya.WittCarryUP`): for UP series `u₁, …, u_k` and an integer cutoff
`θ`, the restriction to `(-∞, θ)` of the canonical coefficient function of
`∑ⱼ S(uⱼ) ∈ 𝕃_[p]` is UP.

The proof is a strong induction on the integer gap `θ - v`, where `v` is a common
integer lower bound for the supports.  One round of the pair collapse
(`TrustworthyKedlaya.Kedlaya.ShadowCollapse`) rewrites the sum as
`S(w) + ∑ₗ S(u'ₗ) + E` with `w = ∑ uⱼ`, carry series `u'ₗ` supported in
`[v+1, ∞)`, and `v_p(E) ≥ θ + 1`; splitting `w` at `v + 1` and absorbing the top
part into the carries reduces the gap by one.  The bookkeeping happens through
the **canonical coefficient series** `coeffSeries x ∈ 𝔽̄_p((t^ℚ))` of `x ∈ 𝕃_[p]`
and its truncations `trunc θ x`; the isometry (`val_shadow_sub`) turns valuation
bounds into agreement of truncations.

## Main statements

- `TrustworthyKedlaya.pAdicHahnSeries.coeffSeries` / `trunc`: the canonical
  coefficient function as a Hahn series, and its restriction below a cutoff.
- `TrustworthyKedlaya.pAdicHahnSeries.trunc_eq_of_le_val_sub`: elements at
  `p`-adic distance `≥ θ` have equal truncations below `θ`.
- `TrustworthyKedlaya.pAdicHahnSeries.exists_carry_list`: the iterated pair
  collapse for a finite list of shadows.
- `TrustworthyKedlaya.pAdicHahnSeries.isUP_trunc_list_sum_shadow`: the engine.

## References

- K. S. Kedlaya, *Power series and p-adic algebraic closures*, J. Number Theory 89
  (2001) [Ked01b], proof of Theorem 7.
-/

@[expose] public section

namespace TrustworthyKedlaya.pAdicHahnSeries

open WittVector

variable {p : ℕ} [hp : Fact (Nat.Prime p)]

/-! ### The canonical coefficient series and its truncations -/

/-- The canonical coefficient function of `x ∈ 𝕃_[p]`, packaged as a Hahn series
over `𝔽̄_p`.  Inverse to `shadow` on both sides. -/
noncomputable def coeffSeries (x : 𝕃_[p]) : HahnSeries ℚ (𝔽ᵃ_[p]) :=
  ⟨x.coeff, support_IsPWO x⟩

@[simp]
theorem coeff_coeffSeries (x : 𝕃_[p]) (q : ℚ) :
    (coeffSeries x).coeff q = x.coeff q := rfl

@[simp]
theorem shadow_coeffSeries (x : 𝕃_[p]) : shadow (coeffSeries x) = x :=
  fromCoeff_of_coeff_eq_self x

@[simp]
theorem coeffSeries_shadow (u : HahnSeries ℚ (𝔽ᵃ_[p])) : coeffSeries (shadow u) = u :=
  HahnSeries.ext (coeff_shadow u)

/-- The truncation of `x ∈ 𝕃_[p]` below the cutoff `θ`: the restriction of the
canonical coefficient function to exponents `< θ`. -/
noncomputable def trunc (θ : ℚ) (x : 𝕃_[p]) : HahnSeries ℚ (𝔽ᵃ_[p]) :=
  hahnRestrict (Set.Iio θ) (coeffSeries x)

theorem coeff_trunc_of_lt {θ q : ℚ} (h : q < θ) (x : 𝕃_[p]) :
    (trunc θ x).coeff q = x.coeff q :=
  coeff_hahnRestrict_of_mem _ (Set.mem_Iio.mpr h)

theorem coeff_trunc_of_le {θ q : ℚ} (h : θ ≤ q) (x : 𝕃_[p]) :
    (trunc θ x).coeff q = 0 :=
  coeff_hahnRestrict_of_notMem _ (by simp only [Set.mem_Iio, not_lt]; exact h)

theorem trunc_shadow (θ : ℚ) (u : HahnSeries ℚ (𝔽ᵃ_[p])) :
    trunc θ (shadow u) = hahnRestrict (Set.Iio θ) u := by
  rw [trunc, coeffSeries_shadow]

/-- **Agreement below the valuation of the difference**: if `v_p(x - x') ≥ θ`, the
truncations of `x` and `x'` below `θ` coincide.  The isometry `val_shadow_sub`
identifies the valuation with the `t`-adic order of the difference of the canonical
coefficient functions. -/
theorem trunc_eq_of_le_val_sub {x x' : 𝕃_[p]} {θ : ℚ}
    (h : (θ : WithTop ℚ) ≤ val p (x - x')) : trunc θ x = trunc θ x' := by
  have hiso := val_shadow_sub (coeffSeries x) (coeffSeries x')
  rw [shadow_coeffSeries, shadow_coeffSeries] at hiso
  apply HahnSeries.ext
  funext q
  by_cases hq : q < θ
  · rw [coeff_trunc_of_lt hq, coeff_trunc_of_lt hq]
    have hz : (coeffSeries x - coeffSeries x').coeff q = 0 := by
      refine HahnSeries.coeff_eq_zero_of_lt_orderTop ?_
      rw [← hiso]
      exact lt_of_lt_of_le (by exact_mod_cast hq) h
    rw [HahnSeries.coeff_sub, coeff_coeffSeries, coeff_coeffSeries, sub_eq_zero] at hz
    exact hz
  · rw [coeff_trunc_of_le (not_lt.mp hq), coeff_trunc_of_le (not_lt.mp hq)]

/-- A support bound below `v` on a Hahn series gives the valuation bound `v` on its
shadow. -/
theorem le_val_shadow_of_forall_coeff_eq_zero {u : HahnSeries ℚ (𝔽ᵃ_[p])} {v : ℚ}
    (h : ∀ q < v, u.coeff q = 0) : (v : WithTop ℚ) ≤ val p (shadow u) := by
  rw [val_shadow]
  exact HahnSeries.le_orderTop_iff_forall.mpr fun j hj => h j (by exact_mod_cast hj)

/-! ### List-level bookkeeping -/

/-- A finite sum of UP series is UP. -/
theorem isUP_list_sum (L : List (HahnSeries ℚ (𝔽ᵃ_[p]))) (h : ∀ u ∈ L, UP.IsUP p u) :
    UP.IsUP p L.sum := by
  induction L with
  | nil =>
    rw [List.sum_nil]
    exact UP.isUP_zero p
  | cons u L ih =>
    rw [List.sum_cons]
    exact (h u (by simp)).add (ih fun z hz => h z (by simp [hz]))

/-- Coefficients of a list sum vanish where all summands vanish. -/
theorem coeff_list_sum_eq_zero {q : ℚ} (L : List (HahnSeries ℚ (𝔽ᵃ_[p])))
    (h : ∀ u ∈ L, u.coeff q = 0) : L.sum.coeff q = 0 := by
  induction L with
  | nil => simp
  | cons u L ih =>
    rw [List.sum_cons, HahnSeries.coeff_add, h u (by simp),
      ih fun z hz => h z (by simp [hz]), add_zero]

/-- A common valuation lower bound on all entries bounds the valuation of the list
sum. -/
theorem le_val_list_sum {g : WithTop ℚ} (L : List (𝕃_[p])) (h : ∀ x ∈ L, g ≤ val p x) :
    g ≤ val p L.sum := by
  induction L with
  | nil =>
    rw [List.sum_nil, val_zero_eq_top]
    exact le_top
  | cons x L ih =>
    rw [List.sum_cons]
    exact (val p).map_le_add (h x (by simp)) (ih fun z hz => h z (by simp [hz]))

/-- Restriction of Hahn series distributes over addition. -/
theorem hahnRestrict_add {S : Type*} [AddMonoid S] (T : Set ℚ) (x y : HahnSeries ℚ S) :
    hahnRestrict T (x + y) = hahnRestrict T x + hahnRestrict T y := by
  apply HahnSeries.ext
  funext q
  by_cases hq : q ∈ T
  · rw [HahnSeries.coeff_add, coeff_hahnRestrict_of_mem _ hq,
      coeff_hahnRestrict_of_mem _ hq, coeff_hahnRestrict_of_mem _ hq,
      HahnSeries.coeff_add]
  · rw [HahnSeries.coeff_add, coeff_hahnRestrict_of_notMem _ hq,
      coeff_hahnRestrict_of_notMem _ hq, coeff_hahnRestrict_of_notMem _ hq, add_zero]

/-- The two restrictions at a cutoff reassemble the series. -/
theorem hahnRestrict_Iio_add_Ici {S : Type*} [AddMonoid S] (θ : ℚ)
    (x : HahnSeries ℚ S) :
    hahnRestrict (Set.Iio θ) x + hahnRestrict (Set.Ici θ) x = x := by
  apply HahnSeries.ext
  funext q
  rw [HahnSeries.coeff_add]
  by_cases hq : q < θ
  · rw [coeff_hahnRestrict_of_mem x (Set.mem_Iio.mpr hq),
      coeff_hahnRestrict_of_notMem x (by simp only [Set.mem_Ici, not_le]; exact hq),
      add_zero]
  · rw [coeff_hahnRestrict_of_notMem x (by simpa using hq),
      coeff_hahnRestrict_of_mem x (Set.mem_Ici.mpr (not_lt.mp hq)), zero_add]

/-- **Disjointly supported Hahn series have additive shadows**: the sum of the
canonical (Teichmüller) representatives is again a Teichmüller series, so no
carries occur (the `shadow`-level counterpart of
`fromCoeff_add_of_disjoint_support`). -/
theorem shadow_add_of_disjoint {a b : HahnSeries ℚ (𝔽ᵃ_[p])}
    (hd : ∀ q, a.coeff q = 0 ∨ b.coeff q = 0) :
    shadow (a + b) = shadow a + shadow b := by
  rw [shadow_eq_mkLp, shadow_eq_mkLp, shadow_eq_mkLp, ← map_add]
  congr 1
  apply HahnSeries.ext
  funext q
  rw [HahnSeries.coeff_add]
  change teichmuller p ((a + b).coeff q)
    = teichmuller p (a.coeff q) + teichmuller p (b.coeff q)
  rw [HahnSeries.coeff_add]
  rcases hd q with h | h <;> simp [h, teichmuller_zero]

/-! ### The iterated pair collapse -/

/-- **Iterated pair collapse**: a finite sum of shadows of series supported at or
above `v` equals the shadow of the plain sum, plus a finite list of shadows of UP
carry series supported at or above `v + 1`, up to an error of valuation at least
`v + K + 1`.  Induction on the list, one `le_val_shadow_add_collapse` per entry. -/
theorem exists_carry_list (v : ℚ) (K : ℕ) :
    ∀ L : List (HahnSeries ℚ (𝔽ᵃ_[p])),
      (∀ u ∈ L, UP.IsUP p u) → (∀ u ∈ L, ∀ q < v, u.coeff q = 0) →
      ∃ P : List (HahnSeries ℚ (𝔽ᵃ_[p])),
        (∀ z ∈ P, UP.IsUP p z) ∧ (∀ z ∈ P, ∀ q < v + 1, z.coeff q = 0) ∧
        ((v + (K + 1) : ℚ) : WithTop ℚ)
          ≤ val p ((L.map shadow).sum - shadow L.sum - (P.map shadow).sum) := by
  intro L
  induction L with
  | nil =>
    intro _ _
    refine ⟨[], by simp, by simp, ?_⟩
    simp only [List.map_nil, List.sum_nil]
    rw [shadow_zero, sub_zero, sub_zero, val_zero_eq_top]
    exact le_top
  | cons y L ih =>
    intro hUP hsupp
    have hyUP : UP.IsUP p y := hUP y (by simp)
    have hysupp : ∀ q < v, y.coeff q = 0 := hsupp y (by simp)
    have hLUP : ∀ u ∈ L, UP.IsUP p u := fun u hu => hUP u (by simp [hu])
    have hLsupp : ∀ u ∈ L, ∀ q < v, u.coeff q = 0 := fun u hu => hsupp u (by simp [hu])
    obtain ⟨P', hP'UP, hP'supp, hP'val⟩ := ih hLUP hLsupp
    have hwUP : UP.IsUP p L.sum := isUP_list_sum L hLUP
    have hwsupp : ∀ q < v, L.sum.coeff q = 0 := fun q hq =>
      coeff_list_sum_eq_zero L fun u hu => hLsupp u hu q hq
    -- the carry list of this collapse step
    set C : List (HahnSeries ℚ (𝔽ᵃ_[p])) := (Finset.Icc 1 K).toList.map
      (fun i : ℕ => HahnSeries.single (i : ℚ) (1 : 𝔽ᵃ_[p])
        * UP.coeffwise p (carryDigit p i) (carryDigit_zero_zero p i) y L.sum) with hC
    have hCsum : (C.map shadow).sum
        = ∑ i ∈ Finset.Icc 1 K, shadow (HahnSeries.single (i : ℚ) (1 : 𝔽ᵃ_[p])
            * UP.coeffwise p (carryDigit p i) (carryDigit_zero_zero p i) y L.sum) := by
      rw [hC, List.map_map]
      exact Finset.sum_map_toList _ _
    have hCUP : ∀ z ∈ C, UP.IsUP p z := by
      intro z hz
      rw [hC, List.mem_map] at hz
      obtain ⟨i, _, rfl⟩ := hz
      exact isUP_single_mul_coeffwise_carry hyUP hwUP i
    have hCsupp : ∀ z ∈ C, ∀ q < v + 1, z.coeff q = 0 := by
      intro z hz q hq
      rw [hC, List.mem_map] at hz
      obtain ⟨i, hi, rfl⟩ := hz
      rw [Finset.mem_toList, Finset.mem_Icc] at hi
      rw [HahnSeries.coeff_single_mul, one_mul, UP.coeff_coeffwise]
      have hqi : q - i < v := by
        have h1 : (1 : ℚ) ≤ (i : ℚ) := by exact_mod_cast hi.1
        linarith
      rw [hysupp _ hqi, hwsupp _ hqi, carryDigit_zero_zero]
    have hcol := le_val_shadow_add_collapse y L.sum hysupp hwsupp K
    refine ⟨C ++ P', ?_, ?_, ?_⟩
    · intro z hz
      rcases List.mem_append.mp hz with h | h
      exacts [hCUP z h, hP'UP z h]
    · intro z hz
      rcases List.mem_append.mp hz with h | h
      exacts [hCsupp z h, hP'supp z h]
    · have hsplit : ((y :: L).map shadow).sum - shadow (y :: L).sum
            - (((C ++ P').map shadow).sum)
          = (shadow y + shadow L.sum - shadow (y + L.sum) - (C.map shadow).sum)
            + ((L.map shadow).sum - shadow L.sum - (P'.map shadow).sum) := by
        rw [List.map_cons, List.sum_cons, List.sum_cons, List.map_append,
          List.sum_append]
        ring
      rw [hsplit]
      refine (val p).map_le_add ?_ hP'val
      rw [hCsum]
      exact hcol

/-! ### The engine: strong induction on the integer gap -/

/-- Degenerate case of the engine: when the cutoff is at or below the common support
bound, the truncation vanishes. -/
private theorem isUP_trunc_of_le {θ v : ℤ} (hθv : θ ≤ v)
    (L : List (HahnSeries ℚ (𝔽ᵃ_[p])))
    (hsupp : ∀ u ∈ L, ∀ q < (v : ℚ), u.coeff q = 0) :
    UP.IsUP p (trunc (θ : ℚ) (L.map shadow).sum) := by
  have hval : (((v : ℚ)) : WithTop ℚ) ≤ val p (L.map shadow).sum := by
    refine le_val_list_sum _ fun x hx => ?_
    rw [List.mem_map] at hx
    obtain ⟨u, hu, rfl⟩ := hx
    exact le_val_shadow_of_forall_coeff_eq_zero (hsupp u hu)
  have h0 : trunc (θ : ℚ) (L.map shadow).sum = 0 := by
    apply HahnSeries.ext
    funext q
    by_cases hq : q < (θ : ℚ)
    · rw [coeff_trunc_of_lt hq]
      refine coeff_eq_zero_of_lt_val (lt_of_lt_of_le ?_ hval)
      have hqv : q < (v : ℚ) := lt_of_lt_of_le hq (by exact_mod_cast hθv)
      exact_mod_cast hqv
    · rw [coeff_trunc_of_le (not_lt.mp hq)]
      simp
  rw [h0]
  exact UP.isUP_zero p

/-- Induction core for `isUP_trunc_list_sum_shadow`: induction on an upper bound `g` for
the integer gap `θ - v` between the cutoff and the common support bound. -/
private theorem isUP_trunc_aux :
    ∀ g : ℕ, ∀ θ v : ℤ, (θ - v).toNat ≤ g →
      ∀ L : List (HahnSeries ℚ (𝔽ᵃ_[p])),
        (∀ u ∈ L, UP.IsUP p u) → (∀ u ∈ L, ∀ q < (v : ℚ), u.coeff q = 0) →
        UP.IsUP p (trunc (θ : ℚ) (L.map shadow).sum) := by
  intro g
  induction g with
  | zero =>
    intro θ v hg L _ hsupp
    exact isUP_trunc_of_le (by omega) L hsupp
  | succ g ihg =>
    intro θ v hg L hUP hsupp
    by_cases hθv : θ ≤ v
    · exact isUP_trunc_of_le hθv L hsupp
    · push Not at hθv
      -- the gap `K = θ - v ≥ 1`; one collapse round at bound `K`
      set K : ℕ := (θ - v).toNat with hK
      have hvKθ : (v : ℚ) + K = (θ : ℚ) := by
        have h1 : ((θ - v).toNat : ℤ) = θ - v :=
          Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ θ - v)
        have h2 : (K : ℚ) = (θ : ℚ) - (v : ℚ) := by
          rw [hK]
          exact_mod_cast congrArg (Int.cast : ℤ → ℚ) h1
        rw [h2]
        ring
      obtain ⟨P, hPUP, hPsupp, hPval⟩ := exists_carry_list (v : ℚ) K L hUP hsupp
      have hwUP : UP.IsUP p L.sum := isUP_list_sum L hUP
      -- split the plain sum at `v + 1`
      set w₀ : HahnSeries ℚ (𝔽ᵃ_[p]) :=
        hahnRestrict (Set.Iio (((v + 1 : ℤ)) : ℚ)) L.sum with hw₀
      set w₁ : HahnSeries ℚ (𝔽ᵃ_[p]) :=
        hahnRestrict (Set.Ici (((v + 1 : ℤ)) : ℚ)) L.sum with hw₁
      have hw01 : L.sum = w₀ + w₁ := (hahnRestrict_Iio_add_Ici _ _).symm
      have hw0UP : UP.IsUP p w₀ := hwUP.hahnRestrict_Iio_intCast (v + 1)
      have hw1UP : UP.IsUP p w₁ := hwUP.hahnRestrict_Ici_intCast (v + 1)
      have hw0w1disj : ∀ q, w₀.coeff q = 0 ∨ w₁.coeff q = 0 := by
        intro q
        by_cases hq : q < ((v + 1 : ℤ) : ℚ)
        · exact Or.inr (coeff_hahnRestrict_of_notMem _
            (by simp only [Set.mem_Ici, not_le]; exact hq))
        · exact Or.inl (coeff_hahnRestrict_of_notMem _ (by simpa using hq))
      have hshw : shadow L.sum = shadow w₀ + shadow w₁ := by
        conv_lhs => rw [hw01]
        exact shadow_add_of_disjoint hw0w1disj
      -- the reduced list at level `v + 1`
      have hw1supp : ∀ q < ((v + 1 : ℤ) : ℚ), w₁.coeff q = 0 := fun q hq =>
        coeff_hahnRestrict_of_notMem _ (by simp only [Set.mem_Ici, not_le]; exact hq)
      have hPsupp' : ∀ z ∈ P, ∀ q < ((v + 1 : ℤ) : ℚ), z.coeff q = 0 := by
        intro z hz q hq
        refine hPsupp z hz q ?_
        have hq' : q < ((v : ℚ)) + 1 := by exact_mod_cast hq
        exact hq'
      have hRsupp : ∀ u ∈ w₁ :: P, ∀ q < ((v + 1 : ℤ) : ℚ), u.coeff q = 0 := by
        intro u hu
        rcases List.mem_cons.mp hu with rfl | hu
        · exact hw1supp
        · exact hPsupp' u hu
      have hRUP : ∀ u ∈ w₁ :: P, UP.IsUP p u := by
        intro u hu
        rcases List.mem_cons.mp hu with rfl | hu
        · exact hw1UP
        · exact hPUP u hu
      -- induction hypothesis on the reduced list: gap dropped by one
      have hRtrunc : UP.IsUP p (trunc (θ : ℚ) (((w₁ :: P).map shadow).sum)) :=
        ihg θ (v + 1) (by omega) (w₁ :: P) hRUP hRsupp
      -- the reduced sum has valuation at least `v + 1` …
      have hRval : ((((v + 1 : ℤ) : ℚ)) : WithTop ℚ)
          ≤ val p (((w₁ :: P).map shadow).sum) := by
        refine le_val_list_sum _ fun x hx => ?_
        rw [List.mem_map] at hx
        obtain ⟨u, hu, rfl⟩ := hx
        exact le_val_shadow_of_forall_coeff_eq_zero (hRsupp u hu)
      -- … so its coefficient series is supported at or above `v + 1`, disjointly
      -- from `w₀`
      have hw0Rdisj : ∀ q, w₀.coeff q = 0
          ∨ (coeffSeries (((w₁ :: P).map shadow).sum)).coeff q = 0 := by
        intro q
        by_cases hq : q < ((v + 1 : ℤ) : ℚ)
        · refine Or.inr ?_
          rw [coeff_coeffSeries]
          exact coeff_eq_zero_of_lt_val (lt_of_lt_of_le (by exact_mod_cast hq) hRval)
        · exact Or.inl (coeff_hahnRestrict_of_notMem _ (by simpa using hq))
      -- the candidate: `w₀` plus the coefficient series of the reduced sum
      have hkey : shadow (w₀ + coeffSeries (((w₁ :: P).map shadow).sum))
          = shadow L.sum + (P.map shadow).sum := by
        rw [shadow_add_of_disjoint hw0Rdisj, shadow_coeffSeries, List.map_cons,
          List.sum_cons, hshw]
        ring
      -- the defect has valuation at least `θ + 1 ≥ θ`
      have hEval : ((θ : ℚ) : WithTop ℚ) ≤ val p ((L.map shadow).sum
          - shadow (w₀ + coeffSeries (((w₁ :: P).map shadow).sum))) := by
        rw [hkey, show (L.map shadow).sum - (shadow L.sum + (P.map shadow).sum)
          = (L.map shadow).sum - shadow L.sum - (P.map shadow).sum by ring]
        refine le_trans ?_ hPval
        rw [WithTop.coe_le_coe, ← hvKθ]
        linarith
      -- truncations agree; the right-hand side is UP
      have htr : trunc (θ : ℚ) (L.map shadow).sum
          = hahnRestrict (Set.Iio (θ : ℚ)) w₀
            + trunc (θ : ℚ) (((w₁ :: P).map shadow).sum) := by
        rw [trunc_eq_of_le_val_sub hEval, trunc_shadow, hahnRestrict_add]
        rfl
      rw [htr]
      exact (hw0UP.hahnRestrict_Iio_intCast θ).add hRtrunc

/-- Every entry of a finite list of Hahn series vanishes below some common integer
bound (each support is well ordered, hence bounded below). -/
theorem exists_int_support_bound (L : List (HahnSeries ℚ (𝔽ᵃ_[p]))) :
    ∃ v : ℤ, ∀ u ∈ L, ∀ q < (v : ℚ), u.coeff q = 0 := by
  induction L with
  | nil => exact ⟨0, by simp⟩
  | cons u L ih =>
    obtain ⟨v', hv'⟩ := ih
    by_cases hu : u = 0
    · refine ⟨v', fun z hz q hq => ?_⟩
      rcases List.mem_cons.mp hz with rfl | hz
      · rw [hu]
        simp
      · exact hv' z hz q hq
    · -- a nonzero series vanishes below the floor of its order
      obtain ⟨vu, hvu⟩ : ∃ vu : ℤ, ∀ q < (vu : ℚ), u.coeff q = 0 :=
        ⟨⌊u.order⌋, fun q hq => HahnSeries.coeff_eq_zero_of_lt_order
          (lt_of_lt_of_le hq (Int.floor_le _))⟩
      refine ⟨min v' vu, fun z hz q hq => ?_⟩
      have hqv' : ((min v' vu : ℤ) : ℚ) ≤ (v' : ℚ) := by
        exact_mod_cast min_le_left v' vu
      have hqvu : ((min v' vu : ℤ) : ℚ) ≤ (vu : ℚ) := by
        exact_mod_cast min_le_right v' vu
      rcases List.mem_cons.mp hz with rfl | hz
      · exact hvu q (lt_of_lt_of_le hq hqvu)
      · exact hv' z hz q (lt_of_lt_of_le hq hqv')

/-- **Sums of shadows have UP truncations**: for UP
series `u₁, …, u_k` and an integer cutoff `θ`, the restriction to `(-∞, θ)` of the
canonical coefficient function of `∑ⱼ S(uⱼ)` is UP. -/
theorem isUP_trunc_list_sum_shadow (L : List (HahnSeries ℚ (𝔽ᵃ_[p])))
    (hUP : ∀ u ∈ L, UP.IsUP p u) (θ : ℤ) :
    UP.IsUP p (trunc (θ : ℚ) (L.map shadow).sum) := by
  obtain ⟨v, hv⟩ := exists_int_support_bound L
  exact isUP_trunc_aux (θ - v).toNat θ v le_rfl L hUP hv

end TrustworthyKedlaya.pAdicHahnSeries
