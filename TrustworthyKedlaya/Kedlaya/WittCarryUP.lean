/-
Copyright (c) 2026 Shanwen Wang, Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import TrustworthyKedlaya.Kedlaya.EngineTruncUP

/-!
# Witt carries preserve uniform periodicity

The set `B'` of truncationwise-UP elements of `𝕃_[p]` — those `g` whose canonical
coefficient function restricts to a UP series below every natural cutoff — contains
the shadow of every UP series, is closed under addition and negation, and is
`p`-adically closed.  In particular it contains every
`p`-adic limit of finite sums of shadows of UP series, which is how the steered
Newton iteration (`TrustworthyKedlaya.Kedlaya.IntegralToAlgCoeff`) consumes it.

The membership predicate is `TrustworthyKedlaya.pAdicHahnSeries.IsTruncUP`.
Addition runs through the truncation engine
(`TrustworthyKedlaya.Kedlaya.EngineTruncUP`): approximate both summands by the shadows of
their truncations and apply `isUP_trunc_list_sum_shadow` to the two-element list.
Negation reduces to finite sums via the telescoping identity
`-g = ∑_{i ≤ K} (p-1) pⁱ g - p^{K+1} g` and the shift rule
`trunc θ (p·g) = t · trunc (θ-1) g`.

## Main statements

- `TrustworthyKedlaya.pAdicHahnSeries.IsTruncUP`: the membership predicate of `B'`.
- `TrustworthyKedlaya.pAdicHahnSeries.isTruncUP_shadow`: shadows of UP series.
- `TrustworthyKedlaya.pAdicHahnSeries.IsTruncUP.add` / `isTruncUP_sum` /
  `IsTruncUP.neg`: additive closure.
- `TrustworthyKedlaya.pAdicHahnSeries.isTruncUP_of_forall_exists_near`:
  `p`-adic closedness.

## References

- K. S. Kedlaya, *Power series and p-adic algebraic closures*, J. Number Theory 89
  (2001) [Ked01b], proof of Theorem 7.
-/

@[expose] public section

namespace TrustworthyKedlaya.pAdicHahnSeries

open WittVector

variable {p : ℕ} [hp : Fact (Nat.Prime p)]

/-- The membership predicate of **`B'`**: `g ∈ 𝕃_[p]` is *truncationwise UP* if the
restriction of its canonical coefficient function below every natural cutoff is
UP. -/
def IsTruncUP (g : 𝕃_[p]) : Prop :=
  ∀ n : ℕ, UP.IsUP p (trunc (n : ℚ) g)

/-! ### Generalities: coefficient bounds and integer cutoffs -/

/-- Coefficient vanishing below `v` bounds the valuation from below. -/
theorem le_val_of_forall_coeff_eq_zero {x : 𝕃_[p]} {v : ℚ}
    (h : ∀ q < v, x.coeff q = 0) : (v : WithTop ℚ) ≤ val p x := by
  have h' := le_val_shadow_of_forall_coeff_eq_zero (u := coeffSeries x)
    (fun q hq => by rw [coeff_coeffSeries]; exact h q hq)
  rwa [shadow_coeffSeries] at h'

/-- Lowering the cutoff refines the truncation by a restriction. -/
theorem trunc_eq_hahnRestrict_trunc {θ θ' : ℚ} (h : θ ≤ θ') (g : 𝕃_[p]) :
    trunc θ g = hahnRestrict (Set.Iio θ) (trunc θ' g) := by
  apply HahnSeries.ext
  funext q
  by_cases hq : q < θ
  · rw [coeff_trunc_of_lt hq, coeff_hahnRestrict_of_mem _ (Set.mem_Iio.mpr hq),
      coeff_trunc_of_lt (lt_of_lt_of_le hq h)]
  · rw [coeff_trunc_of_le (not_lt.mp hq),
      coeff_hahnRestrict_of_notMem _ (by simpa using hq)]

/-- A truncationwise-UP element has UP truncations below every *integer* cutoff,
not only the natural ones. -/
theorem IsTruncUP.trunc_intCast {g : 𝕃_[p]} (hg : IsTruncUP g) (m : ℤ) :
    UP.IsUP p (trunc (m : ℚ) g) := by
  have hle : (m : ℚ) ≤ (m.toNat : ℚ) := by exact_mod_cast Int.self_le_toNat m
  rw [trunc_eq_hahnRestrict_trunc hle]
  exact (hg m.toNat).hahnRestrict_Iio_intCast m

/-- The shadow map approximates an element by its truncation to order `θ`. -/
theorem le_val_sub_shadow_trunc (θ : ℚ) (g : 𝕃_[p]) :
    (θ : WithTop ℚ) ≤ val p (g - shadow (trunc θ g)) := by
  have hiso := val_shadow_sub (coeffSeries g) (trunc θ g)
  rw [shadow_coeffSeries] at hiso
  rw [hiso]
  refine HahnSeries.le_orderTop_iff_forall.mpr fun j hj => ?_
  have hjθ : j < θ := by exact_mod_cast hj
  rw [HahnSeries.coeff_sub, coeff_coeffSeries, coeff_trunc_of_lt hjθ, sub_self]

/-! ### Shadows, zero, and `p`-adic closedness -/

/-- **`B'` contains the shadow of every UP series**: the canonical coefficient
function of `S(u)` is `u` itself. -/
theorem isTruncUP_shadow {u : HahnSeries ℚ (𝔽ᵃ_[p])} (hu : UP.IsUP p u) :
    IsTruncUP (shadow u) := by
  intro n
  rw [trunc_shadow]
  have h := hu.hahnRestrict_Iio_intCast (n : ℤ)
  rwa [show (((n : ℤ) : ℚ)) = (n : ℚ) by push_cast; rfl] at h

theorem isTruncUP_zero : IsTruncUP (0 : 𝕃_[p]) := by
  intro n
  have h0 : trunc ((n : ℕ) : ℚ) (0 : 𝕃_[p]) = 0 := by
    apply HahnSeries.ext
    funext q
    by_cases hq : q < ((n : ℕ) : ℚ)
    · rw [coeff_trunc_of_lt hq]
      simp [coeff_zero_eq]
    · rw [coeff_trunc_of_le (not_lt.mp hq)]
      simp
  rw [h0]
  exact UP.isUP_zero p

/-- **`B'` is `p`-adically closed**: an
element approximable to arbitrary `p`-adic precision by members of `B'` is itself
a member — its truncation below `n` coincides with that of an approximant at
distance `≥ n`. -/
theorem isTruncUP_of_forall_exists_near {g : 𝕃_[p]}
    (h : ∀ n : ℕ, ∃ g' : 𝕃_[p],
      IsTruncUP g' ∧ ((n : ℚ) : WithTop ℚ) ≤ val p (g - g')) :
    IsTruncUP g := by
  intro n
  obtain ⟨g', hg', hval⟩ := h n
  rw [trunc_eq_of_le_val_sub hval]
  exact hg' n

/-! ### Additive closure -/

/-- **`B'` is closed under addition**: replace
each summand by the shadow of its truncation below `n` (distance `≥ n`), and run
the truncation engine on the two shadows. -/
theorem IsTruncUP.add {g g' : 𝕃_[p]} (hg : IsTruncUP g) (hg' : IsTruncUP g') :
    IsTruncUP (g + g') := by
  intro n
  have h3 : ((n : ℚ) : WithTop ℚ) ≤ val p ((g + g')
      - (shadow (trunc (n : ℚ) g) + shadow (trunc (n : ℚ) g'))) := by
    have h12 := (val p).map_le_add (le_val_sub_shadow_trunc (n : ℚ) g)
      (le_val_sub_shadow_trunc (n : ℚ) g')
    rw [show g - shadow (trunc (n : ℚ) g) + (g' - shadow (trunc (n : ℚ) g'))
      = g + g' - (shadow (trunc (n : ℚ) g) + shadow (trunc (n : ℚ) g')) by
        ring] at h12
    exact h12
  rw [trunc_eq_of_le_val_sub h3]
  have heng := isUP_trunc_list_sum_shadow [trunc (n : ℚ) g, trunc (n : ℚ) g']
    (by
      intro u hu
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl
      · exact hg n
      · exact hg' n)
    (n : ℤ)
  have hlist : (([trunc (n : ℚ) g, trunc (n : ℚ) g']).map shadow).sum
      = shadow (trunc (n : ℚ) g) + shadow (trunc (n : ℚ) g') := by
    simp
  rw [hlist] at heng
  rwa [show (((n : ℤ) : ℚ)) = (n : ℚ) by push_cast; rfl] at heng

/-- `B'` is closed under finite sums. -/
theorem isTruncUP_sum {ι : Type*} (s : Finset ι) (f : ι → 𝕃_[p])
    (hf : ∀ i ∈ s, IsTruncUP (f i)) : IsTruncUP (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.cons_induction with
  | empty =>
    rw [Finset.sum_empty]
    exact isTruncUP_zero
  | cons a t ha ih =>
    rw [Finset.sum_cons]
    exact (hf a (by simp)).add (ih fun i hi => hf i (by simp [hi]))

/-- `B'` is closed under natural scalar multiples. -/
theorem IsTruncUP.nsmul {g : 𝕃_[p]} (hg : IsTruncUP g) (k : ℕ) :
    IsTruncUP (k • g) := by
  induction k with
  | zero =>
    rw [zero_nsmul]
    exact isTruncUP_zero
  | succ k ih =>
    rw [succ_nsmul]
    exact ih.add hg

/-! ### Negation via the telescoping identity -/

/-- The shift rule: the truncation of `p·g` below `θ` is the monomial shift of the
truncation of `g` below `θ - 1` (multiplying the canonical representative by `t`
preserves Teichmüller coefficients, `t - p` being null). -/
theorem trunc_p_mul (θ : ℚ) (g : 𝕃_[p]) :
    trunc θ (((p : ℕ) : 𝕃_[p]) * g)
      = HahnSeries.single (1 : ℚ) (1 : 𝔽ᵃ_[p]) * trunc (θ - 1) g := by
  apply HahnSeries.ext
  funext q
  rw [HahnSeries.coeff_single_mul, one_mul]
  by_cases hq : q < θ
  · rw [coeff_trunc_of_lt hq, p_eq_single_one, coeff_ppow_mul,
      coeff_trunc_of_lt (by linarith)]
  · rw [coeff_trunc_of_le (not_lt.mp hq), coeff_trunc_of_le (by linarith)]

/-- `B'` is stable under multiplication by `p`: truncations shift by one integer,
and integer monomial shifts preserve UP. -/
theorem IsTruncUP.p_mul {g : 𝕃_[p]} (hg : IsTruncUP g) :
    IsTruncUP (((p : ℕ) : 𝕃_[p]) * g) := by
  intro n
  rw [trunc_p_mul, show (n : ℚ) - 1 = (((n : ℤ) - 1 : ℤ) : ℚ) by push_cast; ring]
  have hone : UP.IsUP p (HahnSeries.single (1 : ℚ) (1 : 𝔽ᵃ_[p])) := by
    have h := UP.isUP_single_intCast p 1 (1 : 𝔽ᵃ_[p])
    rwa [Int.cast_one] at h
  exact hone.mul (hg.trunc_intCast ((n : ℤ) - 1))

/-- `B'` is stable under multiplication by powers of `p`. -/
theorem IsTruncUP.p_pow_mul {g : 𝕃_[p]} (hg : IsTruncUP g) (i : ℕ) :
    IsTruncUP (((p : ℕ) : 𝕃_[p]) ^ i * g) := by
  induction i with
  | zero =>
    rw [pow_zero, one_mul]
    exact hg
  | succ i ih =>
    rw [show ((p : ℕ) : 𝕃_[p]) ^ (i + 1) * g
      = ((p : ℕ) : 𝕃_[p]) * (((p : ℕ) : 𝕃_[p]) ^ i * g) by ring]
    exact ih.p_mul

/-- **`B'` is closed under negation**: below
any cutoff `n`, the telescoping identity
`-g = ∑_{i=0}^{K} (p-1) pⁱ g - p^{K+1} g` replaces `-g` by a finite sum of
members of `B'` up to an error `p^{K+1} g` of valuation `> n`. -/
theorem IsTruncUP.neg {g : 𝕃_[p]} (hg : IsTruncUP g) : IsTruncUP (-g) := by
  by_cases hg0 : g = 0
  · rw [hg0, neg_zero]
    exact isTruncUP_zero
  · intro n
    obtain ⟨q₀, hq₀⟩ : ∃ q₀ : ℚ, val p g = (q₀ : WithTop ℚ) :=
      ⟨_, by rw [val_apply, dif_neg hg0]⟩
    set K : ℕ := (⌈(n : ℚ) - q₀⌉).toNat with hK
    have hKge : (n : ℚ) ≤ (K : ℚ) + 1 + q₀ := by
      have h1 : ((n : ℚ) - q₀) ≤ ((⌈(n : ℚ) - q₀⌉ : ℤ) : ℚ) := Int.le_ceil _
      have h2 : ((⌈(n : ℚ) - q₀⌉ : ℤ) : ℚ) ≤ (K : ℚ) := by
        rw [hK]
        exact_mod_cast Int.self_le_toNat _
      linarith
    set h : 𝕃_[p] := ∑ i ∈ Finset.range (K + 1),
      (p - 1) • (((p : ℕ) : 𝕃_[p]) ^ i * g) with hh
    have hhB : IsTruncUP h :=
      isTruncUP_sum _ _ fun i _ => (hg.p_pow_mul i).nsmul (p - 1)
    have hident : h = (((p : ℕ) : 𝕃_[p]) ^ (K + 1) - 1) * g := by
      have hc : ((p - 1 : ℕ) : 𝕃_[p]) = ((p : ℕ) : 𝕃_[p]) - 1 := by
        push_cast [hp.out.one_le]
        ring
      rw [hh]
      calc ∑ i ∈ Finset.range (K + 1), (p - 1) • (((p : ℕ) : 𝕃_[p]) ^ i * g)
          = ∑ i ∈ Finset.range (K + 1),
              ((p : ℕ) : 𝕃_[p]) ^ i * (((p : ℕ) : 𝕃_[p]) - 1) * g := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [nsmul_eq_mul, hc]
            ring
        _ = (∑ i ∈ Finset.range (K + 1), ((p : ℕ) : 𝕃_[p]) ^ i)
              * (((p : ℕ) : 𝕃_[p]) - 1) * g := by
            rw [Finset.sum_mul, Finset.sum_mul]
        _ = (((p : ℕ) : 𝕃_[p]) ^ (K + 1) - 1) * g := by
            rw [geom_sum_mul]
    have hval : ((n : ℚ) : WithTop ℚ) ≤ val p (-g - h) := by
      have hdef : -g - h = -(((p : ℕ) : 𝕃_[p]) ^ (K + 1) * g) := by
        rw [hident]
        ring
      rw [hdef, (val p).map_neg, p_pow_eq_single]
      refine le_val_of_forall_coeff_eq_zero (v := (n : ℚ)) fun r hr => ?_
      rw [coeff_ppow_mul]
      refine coeff_eq_zero_of_lt_val ?_
      rw [hq₀, WithTop.coe_lt_coe]
      push_cast at hr ⊢
      linarith
    rw [trunc_eq_of_le_val_sub hval]
    exact hhB n

end TrustworthyKedlaya.pAdicHahnSeries
