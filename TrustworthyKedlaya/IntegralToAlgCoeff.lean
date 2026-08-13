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

/-! ### Truncation order bookkeeping -/

/-- The truncation of `0` is `0`. -/
theorem trunc_zero (θ : ℚ) : trunc θ (0 : 𝕃_[p]) = 0 := by
  apply HahnSeries.ext
  funext q
  by_cases hq : q < θ
  · rw [coeff_trunc_of_lt hq, coeff_zero_eq]
    rfl
  · rw [coeff_trunc_of_le (not_lt.mp hq)]
    rfl

/-- The order of the canonical coefficient series is the valuation. -/
theorem orderTop_coeffSeries (x : 𝕃_[p]) : (coeffSeries x).orderTop = val p x := by
  rw [← val_shadow, shadow_coeffSeries]

/-- A truncation below a cutoff strictly above the valuation retains the leading
term, hence has order equal to the valuation. -/
theorem orderTop_trunc_of_val_lt {x : 𝕃_[p]} {θ : ℚ}
    (h : val p x < (θ : WithTop ℚ)) : (trunc θ x).orderTop = val p x := by
  have hne : val p x ≠ ⊤ := h.ne_top
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp hne
  have hmθ : m < θ := by
    rw [← WithTop.coe_lt_coe]
    rw [← hm] at h
    exact_mod_cast h
  refine le_antisymm ?_ ?_
  · rw [← hm]
    refine HahnSeries.orderTop_le_of_coeff_ne_zero ?_
    rw [coeff_trunc_of_lt hmθ]
    exact coeff_val_ne_zero hm.symm
  · rw [← hm]
    refine HahnSeries.le_orderTop_iff_forall.mpr fun j hj => ?_
    by_cases hjθ : j < θ
    · rw [coeff_trunc_of_lt hjθ]
      refine coeff_eq_zero_of_lt_val ?_
      rw [← hm]
      exact_mod_cast hj
    · exact coeff_trunc_of_le (not_lt.mp hjθ) x

/-! ### Sub-multiset sum bounds -/

/-- A multiset of `WithTop ℚ` values with a finite sum consists of finite values,
and its sum is read off after `untop'`. -/
theorem multiset_untop'_sum_of_sum_coe {T : Multiset (WithTop ℚ)} {c : ℚ}
    (hc : T.sum = (c : WithTop ℚ)) :
    (T.map (fun w => WithTop.untopD 0 w)).sum = c := by
  classical
  induction T using Multiset.induction_on generalizing c with
  | empty =>
    rw [Multiset.sum_zero] at hc
    rw [Multiset.map_zero, Multiset.sum_zero]
    exact_mod_cast hc
  | cons a T ih =>
    rw [Multiset.sum_cons] at hc
    have ha : a ≠ ⊤ := by
      intro htop
      rw [htop, WithTop.top_add] at hc
      exact WithTop.top_ne_coe hc
    obtain ⟨a', ha'⟩ := WithTop.ne_top_iff_exists.mp ha
    have hT : T.sum ≠ ⊤ := by
      intro htop
      rw [htop, WithTop.add_top] at hc
      exact WithTop.top_ne_coe hc
    obtain ⟨c', hc'⟩ := WithTop.ne_top_iff_exists.mp hT
    have hsum : a' + c' = c := by
      rw [← WithTop.coe_inj, WithTop.coe_add, ha', hc']
      exact hc
    rw [Multiset.map_cons, Multiset.sum_cons, ih hc'.symm, ← ha']
    rw [WithTop.untopD_coe]
    exact hsum

/-- **Sub-multiset sums are bounded by the total finite mass**: if `T ≤ W`, all
elements of `W` are nonnegative, and `T.sum` is finite, then `T.sum` is at most the
sum of the finite parts of `W`. -/
theorem multiset_sum_le_untop'_sum {W T : Multiset (WithTop ℚ)}
    (hW : ∀ w ∈ W, (0 : WithTop ℚ) ≤ w) (hT : T ≤ W) {c : ℚ}
    (hc : T.sum = (c : WithTop ℚ)) :
    c ≤ (W.map (fun w => WithTop.untopD 0 w)).sum := by
  obtain ⟨U, rfl⟩ := Multiset.le_iff_exists_add.mp hT
  rw [Multiset.map_add, Multiset.sum_add, ← multiset_untop'_sum_of_sum_coe hc]
  refine le_add_of_nonneg_right ?_
  refine Multiset.sum_nonneg fun x hx => ?_
  obtain ⟨u, hu, rfl⟩ := Multiset.mem_map.mp hx
  have h0 : (0 : WithTop ℚ) ≤ u := hW u (Multiset.mem_add.mpr (Or.inr hu))
  induction u using WithTop.recTopCoe with
  | top => exact le_refl 0
  | coe a => exact_mod_cast h0

/-! ### One steered Newton step -/

/-- **One steered Newton step** (`prop:integral-to-alg-coeff`, iteration body): let
`Q` be a monic polynomial of degree `n ≥ 1` over `𝕃_[p]` with all coefficients in
`B'` and all roots of valuation `≥ 0`, and let `r` be a root.  Then some `h ∈ B'`
(the shadow of a root of the truncated hat polynomial, algebraic over `𝔽̄_p((t))`)
approximates `r` with a gain: `val (r - h) ≥ val r + 1/n`. -/
theorem exists_isTruncUP_approx_of_root
    {Q : Polynomial (𝕃_[p])} (hmonic : Q.Monic) {n : ℕ} (hdeg : Q.natDegree = n)
    (hn : 0 < n) (hcoeffs : ∀ i, IsTruncUP (Q.coeff i))
    (hroots : ∀ z ∈ Q.roots, (0 : WithTop ℚ) ≤ val p z)
    {r : 𝕃_[p]} (hr : r ∈ Q.roots) :
    ∃ h : 𝕃_[p], IsTruncUP h ∧
      val p r + ((1 / (n : ℚ) : ℚ) : WithTop ℚ) ≤ val p (r - h) := by
  classical
  by_cases hr0 : r = 0
  · exact ⟨0, isTruncUP_zero, by rw [hr0, sub_zero, val_zero_eq_top]; exact le_top⟩
  obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.mp
    ((not_iff_not.mpr (val_eq_top_iff (p := p))).mpr hr0)
  set Z : Multiset (𝕃_[p]) := Q.roots with hZ
  have hsplits : Q.Splits := IsAlgClosed.splits Q
  have hQprod : Q = (Z.map fun z => X - Polynomial.C z).prod :=
    hsplits.eq_prod_roots_of_monic hmonic
  have hZcard : Z.card = n := by
    have h := congrArg Polynomial.natDegree hQprod
    rw [hdeg, natDegree_multiset_prod_X_sub_C_eq_card] at h
    exact h.symm
  set W : Multiset (WithTop ℚ) := Z.map (val p) with hW0def
  have hW0 : ∀ w ∈ W, (0 : WithTop ℚ) ≤ w := by
    intro w hw
    obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.mp hw
    exact hroots z hz
  -- every coefficient of `Q` has nonnegative valuation
  have hvalcoeff : ∀ i, i ≤ n → (0 : WithTop ℚ) ≤ val p (Q.coeff i) := by
    intro i hi
    obtain ⟨T, hTle, _, _, hTsum⟩ :=
      exists_sum_le_v_coeff_prod_X_sub_C (val p) Z (i := i) (by rw [hZcard]; exact hi)
    rw [← hQprod] at hTsum
    refine le_trans (Multiset.sum_nonneg fun w hw => hW0 w (Multiset.mem_of_le hTle hw)) hTsum
  -- the single natural cutoff
  have huntopD_nonneg : ∀ w : WithTop ℚ, (0 : WithTop ℚ) ≤ w → 0 ≤ WithTop.untopD 0 w := by
    intro w hw
    induction w using WithTop.recTopCoe with
    | top => exact le_refl 0
    | coe a => exact_mod_cast hw
  set R₀ : ℚ := (W.map (fun w => WithTop.untopD 0 w)).sum with hR₀
  set Nb : ℕ := ⌈R₀⌉₊ + 1 with hNb
  set Vb : ℚ := ∑ i ∈ Finset.range n, WithTop.untopD 0 (val p (Q.coeff i)) with hVb
  set θ : ℕ := Nb + (⌈Vb⌉₊ + 1) with hθ
  have hNθ : Nb ≤ θ := Nat.le_add_right _ _
  have hθgt : ∀ i < n, Q.coeff i ≠ 0 → val p (Q.coeff i) < (((θ : ℕ) : ℚ) : WithTop ℚ) := by
    intro i hi hne
    obtain ⟨v, hv⟩ := WithTop.ne_top_iff_exists.mp
      ((not_iff_not.mpr (val_eq_top_iff (p := p))).mpr hne)
    rw [← hv, WithTop.coe_lt_coe]
    have hvV : v ≤ Vb := by
      have hveq : WithTop.untopD 0 (val p (Q.coeff i)) = v := by
        rw [← hv, WithTop.untopD_coe]
      rw [← hveq, hVb]
      refine Finset.single_le_sum (f := fun j => WithTop.untopD 0 (val p (Q.coeff j)))
        (fun j hj => huntopD_nonneg _ (hvalcoeff j (le_of_lt (Finset.mem_range.mp hj))))
        (Finset.mem_range.mpr hi)
    have hceil : Vb ≤ (⌈Vb⌉₊ : ℚ) := Nat.le_ceil Vb
    have hlt : (⌈Vb⌉₊ : ℚ) < ((θ : ℕ) : ℚ) := by
      rw [hθ]
      push_cast
      have : (1 : ℚ) ≤ (Nb : ℚ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by omega)
      linarith
    linarith
  -- the truncated coefficients are UP, hence algebraic over the Laurent field
  have hUPtrunc : ∀ i, UP.IsUP p (trunc ((θ : ℕ) : ℚ) (Q.coeff i)) := fun i => hcoeffs i θ
  have halg : ∀ i, trunc ((θ : ℕ) : ℚ) (Q.coeff i)
      ∈ algebraicClosure ((𝔽ᵃ_[p])⸨X⸩) (HahnSeries ℚ (𝔽ᵃ_[p])) := fun i =>
    mem_algebraicClosure_iff'.mpr (hUPtrunc i).isIntegral
  -- the hat polynomial over the relative algebraic closure
  set K : IntermediateField ((𝔽ᵃ_[p])⸨X⸩) (HahnSeries ℚ (𝔽ᵃ_[p])) :=
    algebraicClosure ((𝔽ᵃ_[p])⸨X⸩) (HahnSeries ℚ (𝔽ᵃ_[p])) with hK
  set QhatK : Polynomial K := X ^ n + ∑ i ∈ Finset.range n,
    Polynomial.C (⟨trunc ((θ : ℕ) : ℚ) (Q.coeff i), halg i⟩ : K) * X ^ i with hQhatK
  have hsumdeg : (∑ i ∈ Finset.range n,
      Polynomial.C (⟨trunc ((θ : ℕ) : ℚ) (Q.coeff i), halg i⟩ : K) * X ^ i).degree
      < ((n : ℕ) : WithBot ℕ) := by
    refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _) ?_
    rw [Finset.sup_lt_iff (by exact_mod_cast WithBot.bot_lt_coe n)]
    intro i hi
    refine lt_of_le_of_lt (Polynomial.degree_C_mul_X_pow_le _ _) ?_
    exact_mod_cast Finset.mem_range.mp hi
  have hQhatKmonic : QhatK.Monic := Polynomial.monic_X_pow_add hsumdeg
  have hQhatKcoeff : ∀ i < n, QhatK.coeff i
      = (⟨trunc ((θ : ℕ) : ℚ) (Q.coeff i), halg i⟩ : K) := by
    intro i hi
    rw [hQhatK, Polynomial.coeff_add, Polynomial.coeff_X_pow, if_neg (Nat.ne_of_lt hi),
      zero_add, Polynomial.finsetSum_coeff]
    rw [Finset.sum_congr rfl fun j _ => Polynomial.coeff_C_mul_X_pow _ _ _]
    rw [Finset.sum_ite_eq (Finset.range n) i]
    rw [if_pos (Finset.mem_range.mpr hi)]
  have hQhatKdeg : QhatK.natDegree = n := by
    have hdegQ : QhatK.degree = ((n : ℕ) : WithBot ℕ) := by
      rw [hQhatK, Polynomial.degree_add_eq_left_of_degree_lt
        (by rw [Polynomial.degree_X_pow]; exact hsumdeg), Polynomial.degree_X_pow]
    exact Polynomial.natDegree_eq_of_degree_eq_some hdegQ
  -- split the hat polynomial over the relative algebraic closure
  set Ytil : Multiset K := QhatK.roots with hYtil
  have hKsplits : QhatK.Splits := IsAlgClosed.splits QhatK
  have hQhatKprod : QhatK = (Ytil.map fun y => X - Polynomial.C y).prod :=
    hKsplits.eq_prod_roots_of_monic hQhatKmonic
  have hYtilcard : Ytil.card = n := by
    have h := congrArg Polynomial.natDegree hQhatKprod
    rw [hQhatKdeg, natDegree_multiset_prod_X_sub_C_eq_card] at h
    exact h.symm
  -- push down to the Hahn field
  set φ : K →+* HahnSeries ℚ (𝔽ᵃ_[p]) := algebraMap K (HahnSeries ℚ (𝔽ᵃ_[p])) with hφ
  set Y : Multiset (HahnSeries ℚ (𝔽ᵃ_[p])) := Ytil.map (fun y => φ y) with hY
  have hYcard : Y.card = n := by rw [hY, Multiset.card_map, hYtilcard]
  have hQhatprod : QhatK.map φ = (Y.map fun y => X - Polynomial.C y).prod := by
    conv_lhs => rw [hQhatKprod]
    rw [Polynomial.map_multiset_prod, hY, Multiset.map_map, Multiset.map_map]
    refine congrArg Multiset.prod (Multiset.map_congr rfl fun y _ => ?_)
    simp only [Function.comp_apply, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  have hQhatcoeff : ∀ i < n, (QhatK.map φ).coeff i = trunc ((θ : ℕ) : ℚ) (Q.coeff i) := by
    intro i hi
    rw [Polynomial.coeff_map, hQhatKcoeff i hi]
    rfl
  have hQhatcoeff_top : (QhatK.map φ).coeff n = 1 := by
    rw [Polynomial.coeff_map, ← hQhatKdeg, hQhatKmonic.coeff_natDegree, map_one]
  -- equal coefficient valuations, hence equal root-valuation multisets
  have haddval : ∀ u : HahnSeries ℚ (𝔽ᵃ_[p]), HahnSeries.addVal ℚ (𝔽ᵃ_[p]) u = u.orderTop :=
    fun u => HahnSeries.addVal_apply
  have hWeq : Y.map HahnSeries.orderTop = Z.map (val p) := by
    have h := map_v_eq_of_v_coeff_eq (HahnSeries.addVal ℚ (𝔽ᵃ_[p])) (val p)
      (fun u hu => by rwa [haddval, HahnSeries.orderTop_eq_top] at hu)
      (fun x hx => val_eq_top_iff.mp hx)
      Y Z (by rw [hYcard, hZcard])
      (fun i hi => ?_)
    · rw [← h]
      exact Multiset.map_congr rfl fun u _ => (haddval u).symm
    · rw [hYcard] at hi
      rw [← hQhatprod, ← hQprod, haddval]
      rcases lt_or_eq_of_le hi with hilt | hieq
      · rw [hQhatcoeff i hilt]
        by_cases hzero : Q.coeff i = 0
        · rw [hzero, trunc_zero, val_zero_eq_top]
          exact HahnSeries.orderTop_eq_top.mpr rfl
        · exact orderTop_trunc_of_val_lt (hθgt i hilt hzero)
      · subst hieq
        rw [hQhatcoeff_top, ← hdeg, hmonic.coeff_natDegree, HahnSeries.orderTop_one,
          (val p).map_one]
  -- the shadow congruence at gain `k = 1`
  have hcong : ∀ i < Y.card, ∃ T ≤ Y.map HahnSeries.orderTop, T.card = Y.card - i ∧
      T.sum + ((1 : ℚ) : WithTop ℚ) ≤ val p
        (shadow (((Y.map fun y => X - Polynomial.C y).prod).coeff i)
          - ((Z.map fun z => X - Polynomial.C z).prod).coeff i) := by
    intro i hi
    rw [hYcard] at hi
    obtain ⟨T, hTle, hTcard, _, hTsum⟩ :=
      exists_sum_le_v_coeff_prod_X_sub_C (val p) Z (i := i) (by rw [hZcard]; exact hi.le)
    rw [← hQprod] at hTsum
    refine ⟨T, by rwa [hWeq], by rw [hTcard, hZcard, hYcard], ?_⟩
    rw [← hQhatprod, ← hQprod, hQhatcoeff i hi]
    induction hTs : T.sum using WithTop.recTopCoe with
    | top =>
      rw [hTs] at hTsum
      have hzero : Q.coeff i = 0 := val_eq_top_iff.mp (top_le_iff.mp hTsum)
      rw [WithTop.top_add, hzero, trunc_zero, shadow_zero, sub_zero, val_zero_eq_top]
    | coe c =>
      have hcR : c ≤ R₀ := multiset_sum_le_untop'_sum hW0 hTle hTs
      have hcN : c + 1 ≤ (θ : ℚ) := by
        have h1 : c + 1 ≤ (⌈R₀⌉₊ : ℚ) + 1 := by
          have := Nat.le_ceil R₀
          linarith
        have h2 : ((⌈R₀⌉₊ : ℚ) + 1) ≤ (θ : ℚ) := by
          rw [hθ, hNb]
          push_cast
          linarith
        linarith
      rw [(val p).map_sub_swap]
      refine le_trans ?_ (le_val_sub_shadow_trunc ((θ : ℕ) : ℚ) (Q.coeff i))
      rw [← WithTop.coe_add, WithTop.coe_le_coe]
      exact hcN
  -- match the designated root with a shadow of an algebraic root
  obtain ⟨y, hyY, hyOrd, hbound⟩ := roots_continuity_reverse Y Z hWeq
    (k := 1) le_rfl hcong (z := r) hr (s := s) hs.symm
  -- the matched shadow lies in `B'`
  have hyB : IsTruncUP (shadow y) := by
    obtain ⟨ytil, _, rfl⟩ := Multiset.mem_map.mp hyY
    exact isTruncUP_shadow (UP.isUP_of_isIntegral (mem_algebraicClosure_iff'.mp ytil.2))
  refine ⟨shadow y, hyB, ?_⟩
  rw [← hs, (val p).map_sub_swap]
  refine le_trans ?_ hbound
  rw [← WithTop.coe_add, WithTop.coe_le_coe]
  have hm1 : 0 < (Y.map HahnSeries.orderTop).count ((s : ℚ) : WithTop ℚ) :=
    Multiset.count_pos.mpr (by rw [← hyOrd]; exact Multiset.mem_map_of_mem _ hyY)
  have hmn : (Y.map HahnSeries.orderTop).count ((s : ℚ) : WithTop ℚ) ≤ n := by
    refine le_trans (Multiset.count_le_card _ _) ?_
    rw [Multiset.card_map, hYcard]
  have hdiv : (1 : ℚ) / (n : ℚ)
      ≤ 1 / ((Y.map HahnSeries.orderTop).count ((s : ℚ) : WithTop ℚ) : ℚ) := by
    refine one_div_le_one_div_of_le (by exact_mod_cast hm1) (by exact_mod_cast hmn)
  linarith

end TrustworthyKedlaya.pAdicHahnSeries
