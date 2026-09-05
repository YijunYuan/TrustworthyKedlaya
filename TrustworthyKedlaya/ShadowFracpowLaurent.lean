/-
Copyright (c) 2026 Shanwen Wang, Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import TrustworthyKedlaya.CRootClosed
public import TrustworthyKedlaya.IntegralToAlgCoeff

/-!
# Shadows of fractional-power Laurent series are completed-integral

The shadow of a Hahn series whose support is
contained in `(1/n)·ℤ` lies in the closure (valued topology) of the integral closure
of `ℚᶜᵘⁿ_[p]` in `𝕃_[p]`.

Every one-term series `[c]·p^q` with rational exponent `q` is integral over
`ℚᶜᵘⁿ_[p]`: it is a root of `X^d - p^{num}·[c^d]` where `d = q.den`, because
`([c]·p^q)^d = [c^d]·p^{num}`.  A series supported in `(1/n)·ℤ` has only finitely
many support points below any cutoff `N`, so its shadow is approximated to
valuation `≥ N` by the finite sums of its one-term components, which are integral;
letting `N → ∞` places the shadow in the closure.

## Main statements

- `TrustworthyKedlaya.pAdicHahnSeries.single_mem_integralClosure_QpCUn`: every
  one-term series `[c]·p^q` is integral over `ℚᶜᵘⁿ_[p]`.
- `TrustworthyKedlaya.pAdicHahnSeries.shadow_mem_closure_integralClosure_of_support_int_div`:
  the completed-integrality statement.

## References

- K. S. Kedlaya, *The algebraic closure of the power series field in positive
  characteristic*, Proc. Amer. Math. Soc. 129 (2001) [Ked01b], Section 2.
-/

@[expose] public section

namespace TrustworthyKedlaya.pAdicHahnSeries

open WittVector Polynomial
open scoped TrustworthyKedlaya.UP

variable {p : ℕ} [hp : Fact (Nat.Prime p)]

/-- Integer powers of `p` in `𝕃_[p]` are the one-term series `[1]·p^j`, for any
`j : ℤ` (the `zpow` extension of `p_pow_eq_single`). -/
theorem zpow_p_eq_single (j : ℤ) : ((p : ℕ) : 𝕃_[p]) ^ j = single ((j : ℤ) : ℚ) 1 := by
  cases j with
  | ofNat i =>
    rw [Int.ofNat_eq_natCast, zpow_natCast, p_pow_eq_single]
    norm_num
  | negSucc i =>
    rw [zpow_negSucc, p_pow_eq_single]
    refine (eq_inv_of_mul_eq_one_left ?_).symm
    rw [single_mul_single, one_mul]
    have hpos : ((Int.negSucc i : ℤ) : ℚ) + ((i + 1 : ℕ) : ℚ) = 0 := by
      push_cast [Int.negSucc_eq]
      ring
    rw [hpos]
    exact single_zero_one

/-- Multiplying a Teichmüller digit by an integer power of `p` shifts it to
position `j`: `p^j · [x] = [x]·p^j`. -/
theorem zpow_p_mul_single_zero (j : ℤ) (x : 𝔽ᵃ_[p]) :
    ((p : ℕ) : 𝕃_[p]) ^ j * single 0 x = single ((j : ℤ) : ℚ) x := by
  rw [zpow_p_eq_single, single_mul_single, add_zero, one_mul]

/-- **One-term series are integral over `ℚᶜᵘⁿ_[p]`**: the series `[c]·p^q` is a root
of the monic polynomial `X^d - p^{num}·[c^d]` with `d = q.den`, `num = q.num`. -/
theorem single_mem_integralClosure_QpCUn (q : ℚ) (c : 𝔽ᵃ_[p]) :
    single (p := p) q c ∈ integralClosure ℚᶜᵘⁿ_[p] 𝕃_[p] := by
  refine ⟨X ^ q.den - C ((p : ℚᶜᵘⁿ_[p]) ^ q.num *
    algebraMap ℤᶜᵘⁿ_[p] ℚᶜᵘⁿ_[p] (teichmuller p (c ^ q.den))),
    monic_X_pow_sub_C _ q.den_nz, ?_⟩
  rw [eval₂_sub, eval₂_X_pow, eval₂_C, single_pow]
  have hden0 : ((q.den : ℚ)) ≠ 0 := by exact_mod_cast q.den_nz
  have hq : (q.den : ℚ) * q = ((q.num : ℤ) : ℚ) := by
    rw [mul_comm]
    exact ((div_eq_iff hden0).mp (Rat.num_div_den q)).symm
  have htower : algebraMap ℚᶜᵘⁿ_[p] 𝕃_[p] (algebraMap ℤᶜᵘⁿ_[p] ℚᶜᵘⁿ_[p]
      (teichmuller p (c ^ q.den))) = ZpUn_embd (teichmuller p (c ^ q.den)) := by
    change QpCUn_embd (algebraMap ℤᶜᵘⁿ_[p] ℚᶜᵘⁿ_[p] _) = ZpUn_embd _
    unfold QpCUn_embd
    exact IsFractionRing.lift_algebraMap (g := ZpUn_embd) ZpUn_embd_injective _
  rw [map_mul, map_zpow₀, map_natCast, htower, ZpUn_embd_teichmuller,
    zpow_p_mul_single_zero, hq, sub_self]

/-- The shadow of a finite sum of Hahn one-term series is the corresponding sum of
`𝕃_[p]` one-term series: distinct positions never interact, so no carries occur. -/
theorem shadow_finsetSum_single (s : Finset ℚ) (f : ℚ → 𝔽ᵃ_[p]) :
    shadow (∑ q ∈ s, HahnSeries.single q (f q)) = ∑ q ∈ s, single q (f q) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, shadow_zero]
  | insert a t ha ih =>
    have hd : ∀ r, (HahnSeries.single a (f a)).coeff r = 0 ∨
        (∑ q ∈ t, HahnSeries.single q (f q)).coeff r = 0 := by
      intro r
      by_cases hr : r = a
      · subst hr
        refine Or.inr ?_
        rw [HahnSeries.coeff_sum]
        exact Finset.sum_eq_zero fun b hb =>
          HahnSeries.coeff_single_of_ne fun hc => ha (hc ▸ hb)
      · exact Or.inl (HahnSeries.coeff_single_of_ne hr)
    rw [Finset.sum_insert ha, Finset.sum_insert ha, shadow_add_of_disjoint hd,
      shadow_hahn_single, ih]

/-- **Shadows of fractional-power Laurent series are completed-integral**: the shadow
of a Hahn series with support in `(1/n)·ℤ` lies in the closure of the integral
closure of `ℚᶜᵘⁿ_[p]`. -/
theorem shadow_mem_closure_integralClosure_of_support_int_div (n : ℕ+)
    {h : HahnSeries ℚ (𝔽ᵃ_[p])}
    (hsupp : ∀ s ∈ h.support, ∃ k : ℤ, s = (k : ℚ) / (n : ℚ)) :
    shadow h ∈ closure (integralClosure ℚᶜᵘⁿ_[p] 𝕃_[p]).carrier := by
  classical
  refine mem_closure_of_forall_exists_near fun N => ?_
  -- the support truncated below `N` is finite: it sits inside the image of an
  -- integer interval under `j ↦ j / n`
  have hfin : (h.support ∩ Set.Iio ((N : ℚ))).Finite := by
    by_cases hne : (h.support ∩ Set.Iio ((N : ℚ))).Nonempty
    · obtain ⟨q₀, hq₀s, -⟩ := hne
      have hsuppne : h.support.Nonempty := ⟨q₀, hq₀s⟩
      have hnQ : (0 : ℚ) < ((n : ℕ) : ℚ) := by exact_mod_cast n.pos
      refine Set.Finite.subset (Set.Finite.image (fun j : ℤ => (j : ℚ) / ((n : ℕ) : ℚ))
        (Set.finite_Icc ⌈h.isWF_support.min hsuppne * ((n : ℕ) : ℚ)⌉
          ⌊(N : ℚ) * ((n : ℕ) : ℚ)⌋)) ?_
      rintro q ⟨hq_supp, hq_lt⟩
      obtain ⟨k, hk⟩ := hsupp q hq_supp
      have hkq : (k : ℚ) = q * ((n : ℕ) : ℚ) := by
        rw [hk, div_mul_cancel₀ _ hnQ.ne']
      refine ⟨k, ?_, hk.symm⟩
      rw [Set.mem_Icc]
      constructor
      · rw [Int.ceil_le, hkq]
        exact mul_le_mul_of_nonneg_right (h.isWF_support.min_le hsuppne hq_supp) hnQ.le
      · rw [Int.le_floor, hkq]
        exact mul_le_mul_of_nonneg_right (Set.mem_Iio.mp hq_lt).le hnQ.le
    · rw [Set.not_nonempty_iff_eq_empty] at hne
      rw [hne]
      exact Set.finite_empty
  -- the approximant: the finite sum of one-term components below `N`
  refine ⟨∑ q ∈ hfin.toFinset, single q (h.coeff q),
    Subalgebra.sum_mem _ fun q _ => single_mem_integralClosure_QpCUn q _, ?_⟩
  rw [← shadow_finsetSum_single hfin.toFinset h.coeff, val_shadow_sub]
  refine HahnSeries.le_orderTop_iff_forall.mpr fun j hj => ?_
  have hjN : j < (N : ℚ) := by exact_mod_cast hj
  rw [HahnSeries.coeff_sub, HahnSeries.coeff_sum]
  by_cases hjmem : j ∈ hfin.toFinset
  · rw [Finset.sum_eq_single_of_mem j hjmem
      (fun b _ hbj => HahnSeries.coeff_single_of_ne (Ne.symm hbj)),
      HahnSeries.coeff_single_same, sub_self]
  · have hj0 : h.coeff j = 0 := by
      by_contra hc
      exact hjmem (hfin.mem_toFinset.mpr ⟨hc, hjN⟩)
    rw [hj0, Finset.sum_eq_zero fun b hb =>
      HahnSeries.coeff_single_of_ne fun hjb => hjmem (by rw [hjb]; exact hb), sub_zero]

end TrustworthyKedlaya.pAdicHahnSeries
