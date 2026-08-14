/-
Copyright (c) 2026 Shanwen Wang, Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import TrustworthyKedlaya.ChainStep
public import TrustworthyKedlaya.PowAmplify
public import TrustworthyKedlaya.ShadowFracpowLaurent
public import TrustworthyKedlaya.LevelCalculus

/-!
# Approximation by completed-integral elements with full unit gain

Blueprint `lem:approx-by-integral` (the published proof of Kedlaya 2001b,
Theorem 7, part 2, pp. 335–336): every nonzero truncationwise-UP element
`r ∈ B'` of valuation `s` admits `z ∈ C` (the closure of the integral closure
of `ℚᵘⁿ_[p]` in `𝕃_[p]`) with `val (r - z) ≥ s + 1` — a **full unit** of gain.

The assembly is one-shot.  Since `B' = closure A` (`lem:trunc-up-closure`),
pick a Hahn series `â` integral over `𝔽̄_p((t))` whose shadow approximates `r`
at depth `s + 1`; the ultrametric forces `v_t(â) = s` exactly.  *Descale*: a
monic integrality witness `Q` of degree `n` splits over the Hahn field
(`lem:laurent-closure-in-hahn`); applying the inverse Frobenius automorphism
`φ^{-k}` (with `p^k ≥ n`) to its coefficients yields a split polynomial with
root `ŷ = φ^{-k}(â)` of depth `s' = s/p^k` and coefficients supported in
`p^{-k}ℤ`.  The *coefficientwise shadow companion* has coefficients in `C`
(`lem:shadow-fracpow-laurent`) and deviation exactly zero, so the adapted
`ChainState` of `ChainStep.lean` applies verbatim: the polygon match and the
forward continuity of roots extract a companion root `z₀ ∈ C` with
`val z₀ = s'` and `val (S(ŷ) - z₀) ≥ s' + 1/m ≥ s' + 1/n`.  *Amplify*: raising
to the `p^k`-th power multiplies the congruence excess up to the absolute
carry depth (`lem:pow-congruence-amplify`, `min(1, p^k/m) = 1`), while the
iterated power carry (`lem:shadow-pow-carry`) keeps `S(ŷ)^{p^k}` within
`s + 1` of `S(â)`; the ultrametric combines the three congruences.

## Main statements

- `TrustworthyKedlaya.pAdicHahnSeries.exists_mem_closure_integralClosure_near_of_isTruncUP`:
  the full unit gain (`lem:approx-by-integral`).

## References

- K. S. Kedlaya, *Power series and `p`-adic algebraic closures*, J. Number
  Theory 89 (2001) [Ked01b], pp. 335–336 (published version), proof of
  Theorem 7, part 2.
-/

@[expose] public section

namespace TrustworthyKedlaya.pAdicHahnSeries

open Polynomial
open scoped TrustworthyKedlaya.UP
open LaurentSeries

variable {p : ℕ} [hp : Fact (Nat.Prime p)]

/-! ### The descaling automorphism -/

/-- The iterated inverse Frobenius of the coefficient field kills no nonzero
element. -/
theorem iterate_frobeniusEquiv_symm_eq_zero_iff {k : ℕ} {c : 𝔽ᵃ_[p]} :
    ((frobeniusEquiv (𝔽ᵃ_[p]) p).symm)^[k] c = 0 ↔ c = 0 := by
  induction k generalizing c with
  | zero => rw [Function.iterate_zero, id]
  | succ k ih =>
    rw [Function.iterate_succ_apply, ih]
    exact ⟨fun h => (frobeniusEquiv (𝔽ᵃ_[p]) p).symm.injective (by rw [h, map_zero]),
      fun h => by rw [h, map_zero]⟩

/-- The inverse of the `k`-fold Frobenius ring automorphism of the Hahn field is
the `k`-fold iterate of `invFrobeniusHahn`. -/
theorem iterateFrobeniusEquiv_symm_apply (k : ℕ) (x : HahnSeries ℚ (𝔽ᵃ_[p])) :
    (iterateFrobeniusEquiv (HahnSeries ℚ (𝔽ᵃ_[p])) p k).symm x
      = (invFrobeniusHahn p)^[k] x := by
  apply (iterateFrobeniusEquiv (HahnSeries ℚ (𝔽ᵃ_[p])) p k).injective
  rw [RingEquiv.apply_symm_apply, iterateFrobeniusEquiv_def, UP.invFrobeniusHahn_iterate_pow]

/-- The `k`-fold inverse Frobenius divides the exact `t`-adic order by `p^k`. -/
theorem orderTop_invFrobeniusHahn_iterate {x : HahnSeries ℚ (𝔽ᵃ_[p])} {s : ℚ} (k : ℕ)
    (hx : x.orderTop = (s : WithTop ℚ)) :
    ((invFrobeniusHahn p)^[k] x).orderTop = ((s / (p : ℚ) ^ k : ℚ) : WithTop ℚ) := by
  have hpk : (0 : ℚ) < (p : ℚ) ^ k := pow_pos (by exact_mod_cast hp.out.pos) k
  set y : HahnSeries ℚ (𝔽ᵃ_[p]) := (invFrobeniusHahn p)^[k] x with hy
  -- the coefficient at `s / p^k` survives
  have h1 : y.coeff (s / (p : ℚ) ^ k) ≠ 0 := by
    rw [hy, UP.coeff_invFrobeniusHahn_iterate, mul_div_cancel₀ s hpk.ne']
    rw [ne_eq, iterate_frobeniusEquiv_symm_eq_zero_iff]
    exact HahnSeries.coeff_orderTop_ne hx
  -- all lower coefficients vanish
  have h2 : ∀ q : ℚ, q < s / (p : ℚ) ^ k → y.coeff q = 0 := by
    intro q hq
    rw [hy, UP.coeff_invFrobeniusHahn_iterate]
    have hzero : x.coeff ((p : ℚ) ^ k * q) = 0 := by
      by_contra hne
      have hle := HahnSeries.orderTop_le_of_coeff_ne_zero hne
      rw [hx, WithTop.coe_le_coe] at hle
      have : (p : ℚ) ^ k * q < s := by
        rw [← mul_div_cancel₀ s hpk.ne']
        exact mul_lt_mul_of_pos_left hq hpk
      linarith
    rw [hzero, iterate_frobeniusEquiv_symm_eq_zero_iff.mpr rfl]
  -- the order is pinched
  have hyne : y ≠ 0 := fun h0 => h1 (by rw [h0, HahnSeries.coeff_zero])
  have hne_top : y.orderTop ≠ ⊤ := HahnSeries.orderTop_ne_top.2 hyne
  obtain ⟨g₀, hg₀⟩ := WithTop.ne_top_iff_exists.mp hne_top
  have hcoeff₀ : y.coeff g₀ ≠ 0 := HahnSeries.coeff_orderTop_ne hg₀.symm
  have hup : y.orderTop ≤ (s / (p : ℚ) ^ k : ℚ) := HahnSeries.orderTop_le_of_coeff_ne_zero h1
  have hlo : s / (p : ℚ) ^ k ≤ g₀ := le_of_not_gt fun hlt => hcoeff₀ (h2 g₀ hlt)
  rw [← hg₀] at hup ⊢
  rw [WithTop.coe_le_coe] at hup
  exact congrArg _ (le_antisymm hup hlo)

/-! ### Ultrametric exactness -/

/-- An approximation strictly deeper than the valuation of the target pins the
valuation of the approximant exactly. -/
theorem val_eq_of_le_val_sub {x y : 𝕃_[p]} {s : ℚ} (hx : val p x = (s : WithTop ℚ))
    (hxy : ((s + 1 : ℚ) : WithTop ℚ) ≤ val p (x - y)) :
    val p y = (s : WithTop ℚ) := by
  have hs1 : (s : WithTop ℚ) < ((s + 1 : ℚ) : WithTop ℚ) := by
    rw [WithTop.coe_lt_coe]; linarith
  have hy1 : (s : WithTop ℚ) ≤ val p y := by
    have hid : y = x + -(x - y) := by ring
    rw [hid]
    exact (val p).map_le_add (le_of_eq hx.symm)
      (by rw [(val p).map_neg]; exact le_trans hs1.le hxy)
  refine le_antisymm ?_ hy1
  by_contra hgt
  rw [not_le] at hgt
  have hminlt : (s : WithTop ℚ) < min (val p y) (val p (x - y)) :=
    lt_min hgt (lt_of_lt_of_le hs1 hxy)
  have hminle : min (val p y) (val p (x - y)) ≤ val p x := by
    have hid : x = y + (x - y) := by ring
    conv_rhs => rw [hid]
    exact (val p).map_le_add (min_le_left _ _) (min_le_right _ _)
  rw [hx] at hminle
  exact absurd (lt_of_lt_of_le hminlt hminle) (lt_irrefl _)

/-! ### The full unit gain -/

/-- **Approximation by completed-integral elements, full unit gain**
(`lem:approx-by-integral`; Kedlaya 2001b, Theorem 7, part 2, published proof):
every truncationwise-UP element `r ∈ B'` of exact valuation `s` admits an
element `z` of the closure `C` of the integral closure of `ℚᵘⁿ_[p]` in `𝕃_[p]`
with `val (r - z) ≥ s + 1`. -/
theorem exists_mem_closure_integralClosure_near_of_isTruncUP {r : 𝕃_[p]}
    (hr : IsTruncUP r) {s : ℚ} (hs : val p r = (s : WithTop ℚ)) :
    ∃ z ∈ closure (integralClosure ℚᵘⁿ_[p] 𝕃_[p]).carrier,
      ((s + 1 : ℚ) : WithTop ℚ) ≤ val p (r - z) := by
  classical
  -- ① an algebraic-coefficient approximant at depth `≥ s + 1`
  obtain ⟨Ncut, hNcut⟩ := exists_nat_ge (s + 1)
  have hrA : r ∈ closure {f : 𝕃_[p] | ∃ f' : HahnSeries ℚ (𝔽ᵃ_[p]),
      IsAlgebraic ((𝔽ᵃ_[p])⸨X⸩) f' ∧ coeff f = f'.coeff} := by
    rw [closure_algebraic_coeff_eq_setOf_isTruncUP]
    exact hr
  obtain ⟨a, ⟨ahat, hahat_alg, hahat_coeff⟩, hvala⟩ := exists_near_of_mem_closure hrA Ncut
  have ha_eq : a = shadow ahat := by
    rw [← shadow_coeffSeries a]
    congr 1
    exact HahnSeries.ext hahat_coeff
  rw [ha_eq] at hvala
  have hval1 : ((s + 1 : ℚ) : WithTop ℚ) ≤ val p (r - shadow ahat) :=
    le_trans (by exact_mod_cast hNcut) hvala
  -- ② the ultrametric pins the approximant's valuation, hence `v_t(â) = s`
  have hSa : val p (shadow ahat) = (s : WithTop ℚ) := val_eq_of_le_val_sub hs hval1
  have hahat_orderTop : ahat.orderTop = (s : WithTop ℚ) := by
    rw [← val_shadow]
    exact hSa
  -- ③ a monic integrality witness over the Laurent field, mapped into the Hahn field
  obtain ⟨Q₀, hQ₀monic, hQ₀eval⟩ := hahat_alg.isIntegral
  set QH : Polynomial (HahnSeries ℚ (𝔽ᵃ_[p])) := Q₀.map (UP.intHahnEmbedding p) with hQH
  have hQHmonic : QH.Monic := hQ₀monic.map _
  have hQHsplits : QH.Splits := UP.splits_map_intHahnEmbedding p Q₀
  have hQHroot : QH.eval ahat = 0 := by
    rw [hQH, Polynomial.eval_map]
    exact hQ₀eval
  set n : ℕ := QH.natDegree with hn
  have hn1 : 1 ≤ n := by
    by_contra h0
    rw [not_le, Nat.lt_one_iff] at h0
    have hone : QH = 1 := (Polynomial.Monic.natDegree_eq_zero hQHmonic).mp h0
    rw [hone, Polynomial.eval_one] at hQHroot
    exact one_ne_zero hQHroot
  set Y : Multiset (HahnSeries ℚ (𝔽ᵃ_[p])) := QH.roots with hY
  have hQHprod : QH = (Y.map fun y => X - Polynomial.C y).prod :=
    hQHsplits.eq_prod_roots_of_monic hQHmonic
  have hYcard : Y.card = n := by
    have h := congrArg Polynomial.natDegree hQHprod
    rw [natDegree_multiset_prod_X_sub_C_eq_card] at h
    exact h.symm
  have hahatY : ahat ∈ Y := by
    rw [hY, Polynomial.mem_roots']
    exact ⟨hQHmonic.ne_zero, hQHroot⟩
  -- ④ the descaling exponent is `n` itself: `p^n ≥ n`
  have hnpk : n ≤ p ^ n := (Nat.lt_pow_self hp.out.one_lt).le
  have hpk0 : (0 : ℚ) < (p : ℚ) ^ n := pow_pos (by exact_mod_cast hp.out.pos) n
  -- ⑤ the descaling automorphism `φ^{-n}` and the descaled root
  set σ : HahnSeries ℚ (𝔽ᵃ_[p]) ≃+* HahnSeries ℚ (𝔽ᵃ_[p]) :=
    (iterateFrobeniusEquiv (HahnSeries ℚ (𝔽ᵃ_[p])) p n).symm with hσ
  have hσ_eq : ∀ x : HahnSeries ℚ (𝔽ᵃ_[p]), σ x = (invFrobeniusHahn p)^[n] x :=
    fun x => iterateFrobeniusEquiv_symm_apply n x
  set yhat : HahnSeries ℚ (𝔽ᵃ_[p]) := σ ahat with hyhat
  set s' : ℚ := s / (p : ℚ) ^ n with hs'
  have hyhat_orderTop : yhat.orderTop = (s' : WithTop ℚ) := by
    rw [hyhat, hσ_eq]
    exact orderTop_invFrobeniusHahn_iterate n hahat_orderTop
  have hyhat_pow : yhat ^ p ^ n = ahat := by
    rw [hyhat, hσ_eq]
    exact UP.invFrobeniusHahn_iterate_pow ahat n
  -- ⑥ the descaled split polynomial and its root multiset
  set Yhat : Multiset (HahnSeries ℚ (𝔽ᵃ_[p])) := Y.map (fun y => σ y) with hYhat
  have hYhatcard : Yhat.card = n := by
    rw [hYhat, Multiset.card_map, hYcard]
  have hyhatYhat : yhat ∈ Yhat := by
    rw [hYhat, hyhat]
    exact Multiset.mem_map_of_mem _ hahatY
  set Phat : Polynomial (HahnSeries ℚ (𝔽ᵃ_[p])) :=
    QH.map (σ : HahnSeries ℚ (𝔽ᵃ_[p]) →+* HahnSeries ℚ (𝔽ᵃ_[p])) with hPhat
  have hPhatprod : Phat = (Yhat.map fun y => X - Polynomial.C y).prod := by
    rw [hPhat]
    conv_lhs => rw [hQHprod]
    rw [Polynomial.map_multiset_prod, hYhat, Multiset.map_map, Multiset.map_map]
    refine congrArg Multiset.prod (Multiset.map_congr rfl fun y _ => ?_)
    simp only [Function.comp_apply, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
    rfl
  -- coefficient supports lie in `p^{-n}ℤ`
  have hPhat_supp : ∀ i : ℕ, ∀ q ∈ (Phat.coeff i).support,
      ∃ m₀ : ℤ, q = (m₀ : ℚ) / ((p ^ n : ℕ) : ℚ) := by
    intro i q hq
    have hcast : (σ : HahnSeries ℚ (𝔽ᵃ_[p]) →+* HahnSeries ℚ (𝔽ᵃ_[p])) (QH.coeff i)
        = (invFrobeniusHahn p)^[n] (QH.coeff i) := hσ_eq _
    rw [HahnSeries.mem_support, hPhat, Polynomial.coeff_map, hcast,
      UP.coeff_invFrobeniusHahn_iterate] at hq
    have hne : (QH.coeff i).coeff ((p : ℚ) ^ n * q) ≠ 0 := by
      intro h0
      rw [h0] at hq
      exact hq (iterate_frobeniusEquiv_symm_eq_zero_iff.mpr rfl)
    have hrange : (p : ℚ) ^ n * q ∈ Set.range ((Int.castAddHom ℚ : ℤ →+ ℚ)) := by
      by_contra hnr
      refine hne ?_
      rw [hQH, Polynomial.coeff_map]
      exact HahnSeries.embDomain_of_notMem_range hnr
    obtain ⟨m₀, hm₀⟩ := hrange
    refine ⟨m₀, ?_⟩
    have hm₀' : (m₀ : ℚ) = (p : ℚ) ^ n * q := hm₀
    rw [hm₀', Nat.cast_pow, mul_div_cancel_left₀ _ hpk0.ne']
  -- ⑦ the coefficientwise-shadow companion
  set L : Polynomial 𝕃_[p] := X ^ n + ∑ i ∈ Finset.range n,
    Polynomial.C (shadow (Phat.coeff i)) * X ^ i with hL
  have hsumdeg : (∑ i ∈ Finset.range n,
      Polynomial.C (shadow (Phat.coeff i)) * X ^ i).degree < ((n : ℕ) : WithBot ℕ) := by
    refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _) ?_
    rw [Finset.sup_lt_iff (by exact_mod_cast WithBot.bot_lt_coe n)]
    intro i hi
    refine lt_of_le_of_lt (Polynomial.degree_C_mul_X_pow_le _ _) ?_
    exact_mod_cast Finset.mem_range.mp hi
  have hLmonic : L.Monic := Polynomial.monic_X_pow_add hsumdeg
  have hLcoeff : ∀ i < n, L.coeff i = shadow (Phat.coeff i) := by
    intro i hi
    rw [hL, Polynomial.coeff_add, Polynomial.coeff_X_pow, if_neg (Nat.ne_of_lt hi),
      zero_add, Polynomial.finsetSum_coeff]
    rw [Finset.sum_congr rfl fun j _ => Polynomial.coeff_C_mul_X_pow _ _ _]
    rw [Finset.sum_ite_eq (Finset.range n) i]
    rw [if_pos (Finset.mem_range.mpr hi)]
  have hLdeg : L.natDegree = n := by
    have hdegL : L.degree = ((n : ℕ) : WithBot ℕ) := by
      rw [hL, Polynomial.degree_add_eq_left_of_degree_lt
        (by rw [Polynomial.degree_X_pow]; exact hsumdeg), Polynomial.degree_X_pow]
    exact Polynomial.natDegree_eq_of_degree_eq_some hdegL
  -- ⑧ the exact chain state: deviation zero, residual target the shadow itself
  let St : ChainState (shadow yhat) s' Yhat yhat :=
    { recenter := 0
      extracted := 0
      lift := L
      extracted_mem := subset_closure (Subalgebra.zero_mem _)
      lift_monic := hLmonic
      lift_natDegree := by rw [hLdeg, hYhatcard]
      lift_coeff_mem := by
        intro i
        rcases lt_trichotomy i n with hi | hi | hi
        · rw [hLcoeff i hi]
          refine shadow_mem_closure_integralClosure_of_support_int_div
            ⟨p ^ n, pow_pos hp.out.pos n⟩ ?_
          exact hPhat_supp i
        · rw [hi, show L.coeff n = 1 from by rw [← hLdeg]; exact hLmonic.coeff_natDegree]
          exact subset_closure (Subalgebra.one_mem _)
        · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hLdeg]; exact hi)]
          exact subset_closure (Subalgebra.zero_mem _)
      le_orderTop := by
        rw [sub_zero, hyhat_orderTop]
      residual_approx := by
        rw [sub_zero, sub_zero, sub_self]
        rw [val_zero_eq_top]
        exact le_top
      adapted := by
        intro i hi
        have hmap : (Yhat.map fun y => y - 0) = Yhat := by
          rw [Multiset.map_congr rfl fun y _ => sub_zero y, Multiset.map_id']
        obtain ⟨T, hTle, hTcard, -⟩ := TrustworthyKedlaya.exists_min_sum_powersetCard
          ((Yhat.map fun y => y - 0).map HahnSeries.orderTop)
          (j := Yhat.card - i)
          (by simp only [hYhat, Multiset.card_map]; exact Nat.sub_le _ _)
        refine ⟨T, hTle, hTcard, ?_⟩
        have hin : i < n := by rw [← hYhatcard]; exact hi
        have hzero : shadow ((((Yhat.map fun y => y - 0).map
            fun y => X - Polynomial.C y).prod).coeff i) - L.coeff i = 0 := by
          rw [hmap, ← hPhatprod, hLcoeff i hin, sub_self]
        rw [hzero, val_zero_eq_top]
        exact le_top }
  -- ⑨ extraction of the companion root
  have hsc : (yhat - St.recenter).orderTop = (s' : WithTop ℚ) := by
    have h0 : (yhat - 0).orderTop = (s' : WithTop ℚ) := by
      rw [sub_zero, hyhat_orderTop]
    exact h0
  obtain ⟨z₀, hz₀roots, m, hmeq, hm0, hmn, hz₀C, hz₀val, hz₀near, -, -, -⟩ :=
    St.exists_step hyhatYhat hsc
  have hz₀near' : ((s' + 1 / (m : ℚ) : ℚ) : WithTop ℚ) ≤ val p (shadow yhat - z₀) := by
    have h0 : ((s' + 1 / (m : ℚ) : ℚ) : WithTop ℚ) ≤ val p (shadow (yhat - 0) - z₀) :=
      hz₀near
    rwa [sub_zero] at h0
  have hz₀val' : val p z₀ = (s' : WithTop ℚ) := hz₀val
  -- ⑩ Frobenius amplification and the three-term combination
  have hm0' : (0 : ℚ) < (m : ℚ) := by exact_mod_cast hm0
  have hmpk : (m : ℚ) ≤ (p : ℚ) ^ n := by
    have h1 : m ≤ p ^ n := le_trans (le_trans hmn (le_of_eq hYhatcard)) hnpk
    exact_mod_cast h1
  have hamp : ((s + 1 : ℚ) : WithTop ℚ) ≤ val p (shadow yhat ^ p ^ n - z₀ ^ p ^ n) := by
    have h := le_val_pow_pow_sub (x := shadow yhat) (y := z₀)
      (w := s') (e := 1 / (m : ℚ)) (by positivity)
      (by rw [val_shadow, hyhat_orderTop])
      (le_of_eq hz₀val'.symm) hz₀near' n
    have harith : (p : ℚ) ^ n * s' + min 1 ((p : ℚ) ^ n * (1 / (m : ℚ))) = s + 1 := by
      have hmin : min (1 : ℚ) ((p : ℚ) ^ n * (1 / (m : ℚ))) = 1 := by
        refine min_eq_left ?_
        rw [mul_one_div, le_div_iff₀ hm0', one_mul]
        exact hmpk
      rw [hmin, hs', mul_div_cancel₀ _ hpk0.ne']
    rwa [harith] at h
  have hamp2 : ((s + 1 : ℚ) : WithTop ℚ) ≤ val p (shadow ahat - shadow yhat ^ p ^ n) := by
    have hu : ∀ q, yhat.coeff q ≠ 0 → s' ≤ q := by
      intro q hq
      have h := HahnSeries.orderTop_le_of_coeff_ne_zero hq
      rw [hyhat_orderTop, WithTop.coe_le_coe] at h
      exact h
    have hj : 1 ≤ p ^ n := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero n hp.out.pos.ne')
    have h := le_val_shadow_pow_sub yhat s' hu hj
    rw [hyhat_pow] at h
    have harith : ((p ^ n : ℕ) : ℚ) * s' + 1 = s + 1 := by
      rw [hs']
      push_cast
      rw [mul_div_cancel₀ _ hpk0.ne']
    rw [harith] at h
    rwa [(val p).map_sub_swap] at h
  refine ⟨z₀ ^ p ^ n, pow_mem_closure_integralClosure hz₀C _, ?_⟩
  have hcomb : r - z₀ ^ p ^ n
      = ((r - shadow ahat) + (shadow ahat - shadow yhat ^ p ^ n))
        + (shadow yhat ^ p ^ n - z₀ ^ p ^ n) := by
    ring
  rw [hcomb]
  exact (val p).map_le_add ((val p).map_le_add hval1 hamp2) hamp

end TrustworthyKedlaya.pAdicHahnSeries
