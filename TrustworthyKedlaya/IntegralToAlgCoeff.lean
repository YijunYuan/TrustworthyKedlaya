/-
Copyright (c) 2026 Shanwen Wang, Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import TrustworthyKedlaya.TruncUPClosure
public import TrustworthyKedlaya.WittCarryUPMul
public import TrustworthyKedlaya.ShadowCongruence
public import TrustworthyKedlaya.NewtonPolygonRoots
public import TrustworthyKedlaya.LaurentClosure
public import TrustworthyKedlaya.LpAlgClosed
public import TrustworthyKedlaya.TeichCarry
public import TrustworthyKedlaya.IntTruncation

/-!
# Integral elements have coefficient functions from algebraic series

Blueprint `prop:integral-to-alg-coeff` (Kedlaya 2001b, Theorem 7, first part, with
the recentering of the second part; Kedlaya 2017, Theorem 13.5): every `f ∈ 𝕃_[p]`
integral over `ℚᵘⁿ_[p]` lies in the closure of the set of elements whose canonical
coefficient function is the coefficient function of a Hahn series algebraic over
`𝔽̄_p((t))`.  By `lem:trunc-up-closure` that closure is the set `B'` of
truncationwise-UP elements, so the statement reduces to `IsTruncUP f`.

The proof is a Newton iteration steered towards `f`, restarted at every step:

* `ℚᵘⁿ_[p]` lands in `B'` (`isTruncUP_algebraMap_QpUn`): a Witt vector is the
  `p`-adic limit of its Teichmüller digit partial sums, which are integer
  combinations of shadows of monomials, and `B'` is `p`-adically closed; a general
  element of `ℚᵘⁿ_[p]` is a Witt vector divided by a power of `p`.
* One step (`exists_isTruncUP_approx_of_root`): given a monic `Q` over `𝕃_[p]`
  with coefficients in `B'` and all roots of valuation `≥ 0`, and a designated
  root `r`, truncate every coefficient below a single natural cutoff `θ` that
  exceeds both the sum of the finite root valuations plus one and every finite
  coefficient valuation.  The truncations are UP, hence algebraic over
  `𝔽̄_p((t))`; the hat polynomial they form splits in the relative algebraic
  closure of `𝔽̄_p((t))` inside the Hahn field, its coefficient valuations agree
  with those of `Q`, so the Newton polygon forces equal root-valuation multisets
  (`lem:newton-polygon-roots`), and the continuity of roots
  (`lem:roots-continuity`, reverse direction) matches `r` with the shadow of an
  algebraic root to depth `val r + 1/n`.
* Iteration (`exists_isTruncUP_near_root`): recenter `Q` by `X + C g` and repeat;
  the recentered coefficients stay in `B'` because `B'` is a subring
  (`lem:witt-carry-up`, `lem:witt-carry-up-mul`), and the recentered roots stay
  nonnegative.  The gain `1/n` per step makes the partial sums converge to `f`.
* Scaling (`isTruncUP_of_isIntegral_QpUn`): a general annihilator is first scaled
  by `p^N` to force all roots into the valuation ring; `B'` absorbs the scaling
  because it contains all integer monomials `[a]·p^m` and is a subring.

## Main statements

- `TrustworthyKedlaya.pAdicHahnSeries.isTruncUP_algebraMap_QpUn`: `ℚᵘⁿ_[p] ⊆ B'`.
- `TrustworthyKedlaya.pAdicHahnSeries.isTruncUP_of_isIntegral_QpUn`: integral
  elements over `ℚᵘⁿ_[p]` are truncationwise UP.
- `TrustworthyKedlaya.pAdicHahnSeries.mem_closure_algebraic_coeff_of_isIntegral`:
  `prop:integral-to-alg-coeff`.

## References

- K. S. Kedlaya, *The algebraic closure of the power series field in positive
  characteristic*, Proc. Amer. Math. Soc. 129 (2001) [Ked01b], Theorem 7.
- K. S. Kedlaya, *On the algebraicity of generalized power series*, Beiträge
  Algebra Geom. 58 (2017) [Ked17], Theorem 13.5.
-/

@[expose] public section

namespace TrustworthyKedlaya.pAdicHahnSeries

open WittVector Polynomial LaurentSeries
open scoped TrustworthyKedlaya.UP

variable {p : ℕ} [hp : Fact (Nat.Prime p)]

/-! ### `ℚᵘⁿ_[p]` lands in `B'` -/

/-- The one-term `p`-adic Hahn series is the shadow of the one-term Hahn series. -/
theorem shadow_hahn_single (q : ℚ) (a : 𝔽ᵃ_[p]) :
    shadow (HahnSeries.single q a) = single q a := by
  apply ext_coeff
  rw [coeff_shadow, coeff_single]
  funext r
  rw [HahnSeries.coeff_single]
  by_cases h : r = q
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]

/-- Natural number constants lie in `B'`. -/
theorem isTruncUP_natCast (n : ℕ) : IsTruncUP ((n : 𝕃_[p])) := by
  rw [← mem_truncUPSubring]
  exact natCast_mem (truncUPSubring p) n

/-- Integer-position one-term series lie in `B'`. -/
theorem isTruncUP_single_intCast (m : ℤ) (a : 𝔽ᵃ_[p]) :
    IsTruncUP (single ((m : ℤ) : ℚ) a) := by
  rw [← shadow_hahn_single]
  exact isTruncUP_shadow (UP.isUP_single_intCast p m a)

/-- The image of a Teichmüller lift in `𝕃_[p]` is the one-term series `[a]·p⁰`. -/
theorem ZpUn_embd_teichmuller (a : 𝔽ᵃ_[p]) :
    ZpUn_embd (teichmuller p a) = single (p := p) 0 a := by
  rw [single, fromCoeff, lifted_fromCoeff_single]
  rfl

/-- The image of a Witt vector in `𝕃_[p]` has nonnegative valuation. -/
theorem le_val_ZpUn_embd (b : ℤᵘⁿ_[p]) :
    ((0 : ℚ) : WithTop ℚ) ≤ val p (ZpUn_embd b) :=
  le_val_mkLp_of_coeff_eq_zero fun q hq =>
    HahnSeries.coeff_single_of_ne (by exact_mod_cast hq.ne)

/-- **Witt vectors are truncationwise UP**: the image of `ℤᵘⁿ_[p]` in `𝕃_[p]` lies
in `B'`.  The Teichmüller digit partial sums are `B'`-combinations of one-term
series and approximate the Witt vector to arbitrary `p`-adic depth. -/
theorem isTruncUP_ZpUn_embd (a : ℤᵘⁿ_[p]) : IsTruncUP (ZpUn_embd a) := by
  refine isTruncUP_of_forall_exists_near fun n => ?_
  refine ⟨∑ i ∈ Finset.Iic n, single (p := p) 0 (teichDigit p i a) * ((p : ℕ) : 𝕃_[p]) ^ i,
    ?_, ?_⟩
  · refine isTruncUP_sum _ _ fun i _ => ?_
    exact (isTruncUP_single_intCast 0 _).mul ((isTruncUP_natCast p).pow i)
  · obtain ⟨w, hw⟩ := sub_sum_teichDigit_dvd p a n
    have hmap := congrArg (ZpUn_embd (p := p)) hw
    rw [map_sub, map_sum] at hmap
    simp only [map_mul, map_pow, map_natCast, ZpUn_embd_teichmuller] at hmap
    rw [hmap, (val p).map_mul]
    have hppow : val p (((p : ℕ) : 𝕃_[p]) ^ (n + 1)) = (((n + 1 : ℕ) : ℚ) : WithTop ℚ) := by
      rw [p_pow_eq_single, val_single _ one_ne_zero]
    rw [hppow]
    calc ((n : ℚ) : WithTop ℚ)
        ≤ (((n + 1 : ℕ) : ℚ) : WithTop ℚ) := by
          rw [WithTop.coe_le_coe]; exact_mod_cast Nat.le_succ n
      _ = (((n + 1 : ℕ) : ℚ) : WithTop ℚ) + 0 := by rw [add_zero]
      _ ≤ (((n + 1 : ℕ) : ℚ) : WithTop ℚ) + val p (ZpUn_embd w) :=
          add_le_add le_rfl (le_val_ZpUn_embd w)

/-- **`ℚᵘⁿ_[p]` lands in `B'`** (the coefficient step of `prop:integral-to-alg-coeff`):
the canonical coefficient function of an element of `ℚᵘⁿ_[p]` is a Laurent series,
so the element is truncationwise UP. -/
theorem isTruncUP_algebraMap_QpUn (c : ℚᵘⁿ_[p]) :
    IsTruncUP (algebraMap ℚᵘⁿ_[p] 𝕃_[p] c) := by
  by_cases hc : c = 0
  · rw [hc, map_zero]
    exact isTruncUP_zero
  -- clear the denominator: `p^k · c` has valuation `≤ 1`, hence lifts to `ℤᵘⁿ_[p]`
  obtain ⟨k, hk⟩ : ∃ k : ℕ, Valued.v (((p : ℚᵘⁿ_[p]) ^ k) * c) ≤ 1 := by
    have hvc : Valued.v c ≠ 0 := by
      simpa using (Valuation.ne_zero_iff Valued.v).mpr hc
    refine ⟨(WithZero.log (Valued.v c)).toNat, ?_⟩
    rw [Valued.v.map_mul, show ((p : ℚᵘⁿ_[p]) ^ ((WithZero.log (Valued.v c)).toNat : ℕ))
        = (p : ℚᵘⁿ_[p]) ^ (((WithZero.log (Valued.v c)).toNat : ℤ)) from (zpow_natCast _ _).symm,
      valued_v_p_zpow]
    calc (((Multiplicative.ofAdd (-((WithZero.log (Valued.v c)).toNat : ℤ)) :
            Multiplicative ℤ)) : WithZero (Multiplicative ℤ)) * Valued.v c
        = WithZero.exp (-((WithZero.log (Valued.v c)).toNat : ℤ)) * Valued.v c := by
          rw [WithZero.exp_eq_coe_ofAdd]
      _ = WithZero.exp (-((WithZero.log (Valued.v c)).toNat : ℤ)
            + WithZero.log (Valued.v c)) := by
          rw [WithZero.exp_add, WithZero.exp_log hvc]
      _ ≤ WithZero.exp 0 := by
          refine WithZero.exp_le_exp.mpr ?_
          have := Int.self_le_toNat (WithZero.log (Valued.v c))
          omega
      _ = 1 := WithZero.exp_zero
  obtain ⟨a, ha⟩ := existsCanonicalExpansionAux.exists_lift_of_valued_le_one hk
  -- push down to `𝕃_[p]` and cancel the `p`-power by the monomial `[1]·p^{-k}`
  have htower : algebraMap ℚᵘⁿ_[p] 𝕃_[p] (algebraMap ℤᵘⁿ_[p] ℚᵘⁿ_[p] a) = ZpUn_embd a := by
    change QpUn_embd (algebraMap ℤᵘⁿ_[p] ℚᵘⁿ_[p] a) = ZpUn_embd a
    unfold QpUn_embd
    exact IsFractionRing.lift_algebraMap (g := ZpUn_embd) ZpUn_embd_injective a
  have himg : ((p : ℕ) : 𝕃_[p]) ^ k * algebraMap ℚᵘⁿ_[p] 𝕃_[p] c = ZpUn_embd a := by
    have h1 := congrArg (algebraMap ℚᵘⁿ_[p] 𝕃_[p]) ha
    rw [map_mul, map_pow, map_natCast] at h1
    rw [← h1]
    exact htower
  have hcancel : single (p := p) ((-(k : ℤ) : ℤ) : ℚ) 1 * (((p : ℕ) : 𝕃_[p]) ^ k) = 1 := by
    rw [p_pow_eq_single, single_mul_single, one_mul]
    rw [show ((-(k : ℤ) : ℤ) : ℚ) + (k : ℚ) = 0 by push_cast; ring]
    exact single_zero_one
  have hfinal : algebraMap ℚᵘⁿ_[p] 𝕃_[p] c
      = single (p := p) ((-(k : ℤ) : ℤ) : ℚ) 1 * ZpUn_embd a := by
    rw [← himg, ← mul_assoc, hcancel, one_mul]
  rw [hfinal]
  exact (isTruncUP_single_intCast _ _).mul (isTruncUP_ZpUn_embd a)

end TrustworthyKedlaya.pAdicHahnSeries
