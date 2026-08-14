/-
Copyright (c) 2026 Shanwen Wang, Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import TrustworthyKedlaya.CRootClosed
public import TrustworthyKedlaya.ShadowCongruence

/-!
# Root extraction against an adapted lift of a recentered hat polynomial

Reusable extraction engine for the descaling route of blueprint
`lem:approx-by-integral` (the published proof of Kedlaya 2001b, Theorem 7,
part 2): a `ChainState` for the anchor `(r, s, Yhat, ahat)` packages a monic
polynomial `P` over `𝕃_[p]` with coefficients in the closed integral closure
`C` of `ℚᵘⁿ_[p]`, coefficientwise within `σ_{n-i}(W) + 1` of the shadows of
the coefficients of the recentered split hat polynomial
`∏_{y ∈ Yhat}(X - (y - ĝ))`, together with a residual approximation
`val ((r - g) - S(ahat - ĝ)) ≥ s + 1`.  In the one-shot descaling argument
the congruence is exact (`ĝ = 0`, `P` the coefficientwise shadow companion),
which is a special case of this state.

`ChainState.map_orderTop_eq_roots_map_val` is the polygon match: the adapted
congruence pins the valuation multiset of the roots of `P` over the
algebraically closed `𝕃_[p]` to the `t`-adic root valuations.
`ChainState.exists_step` extracts a root `z` of `P` with `z ∈ C`,
`val z = s_c` and `val (S(ŷ) - z) ≥ s_c + 1/m` (via
`roots_continuity_forward`), bounds the residual advance by
`min (s + 1) (s_c + 1/m)`, and records the depth-one-slice recentering
estimates (`ŵ = trunc (s_c + 1) z` raises the hat-root depth by `≥ 1/m` and
regenerates the residual congruence at depth `s + 1`) — the per-step clauses
retained from the retired chain formulation of the arXiv version, kept for
reuse.

## Main statements

- `TrustworthyKedlaya.pAdicHahnSeries.ChainState`: the adapted-lift state.
- `TrustworthyKedlaya.pAdicHahnSeries.ChainState.map_orderTop_eq_roots_map_val`:
  the polygon match.
- `TrustworthyKedlaya.pAdicHahnSeries.ChainState.exists_step`: root
  extraction, `C`-membership, distance bounds, and slice-recentering
  estimates.

## References

- K. S. Kedlaya, *Power series and `p`-adic algebraic closures*, J. Number
  Theory 89 (2001) [Ked01b], pp. 333–336 (published version), proof of
  Theorem 7.
-/

@[expose] public section

namespace TrustworthyKedlaya.pAdicHahnSeries

open Polynomial
open scoped TrustworthyKedlaya.UP

variable {p : ℕ} [hp : Fact (Nat.Prime p)]

/-- A **chain state** for the block anchor `(r, s, Yhat, ahat)` (an adapted
lift in the sense of the descaling route of `lem:approx-by-integral`): `Yhat`
is the root multiset of the hat polynomial and
`ahat ∈ Yhat` the distinguished root whose shadow approximates the residual
target `r` at depth `s + 1`.  The data are the accumulated char-`p` recentering
`ĝ`, the accumulated `p`-adic extracted sum `g`, and the adapted lift `P`; the
propositional fields are the blueprint invariants (1)–(3) in `j`-free form. -/
structure ChainState (r : 𝕃_[p]) (s : ℚ) (Yhat : Multiset (HahnSeries ℚ (𝔽ᵃ_[p])))
    (ahat : HahnSeries ℚ (𝔽ᵃ_[p])) where
  /-- the accumulated char-`p` recentering `ĝ` -/
  recenter : HahnSeries ℚ (𝔽ᵃ_[p])
  /-- the accumulated `p`-adic extracted sum `g` -/
  extracted : 𝕃_[p]
  /-- the adapted monic lift `P` of the recentered hat polynomial -/
  lift : Polynomial 𝕃_[p]
  /-- the extracted sum lies in the closed integral closure `C` -/
  extracted_mem : extracted ∈ closure (integralClosure ℚᵘⁿ_[p] 𝕃_[p]).carrier
  lift_monic : lift.Monic
  lift_natDegree : lift.natDegree = Yhat.card
  /-- the lift's coefficients lie in the closed integral closure `C` -/
  lift_coeff_mem : ∀ i, lift.coeff i ∈ closure (integralClosure ℚᵘⁿ_[p] 𝕃_[p]).carrier
  /-- invariant (1), `j`-free residue: the current hat-root depth never falls
  below `s` -/
  le_orderTop : (s : WithTop ℚ) ≤ (ahat - recenter).orderTop
  /-- invariant (2): the residual `r - g` approximates the shadow of the current
  hat root `ŷ = ahat - ĝ` at the fixed regeneration depth `s + 1` -/
  residual_approx :
    ((s + 1 : ℚ) : WithTop ℚ) ≤ val p ((r - extracted) - shadow (ahat - recenter))
  /-- invariant (3): the lift is *adapted* — each coefficient is within
  `σ_{n-i}(W) + 1` of the shadow of the matching coefficient of the recentered
  hat polynomial, the floor `σ_{n-i}(W)` being delivered by a size-`(n-i)`
  sub-multiset witness `T` of the recentered `t`-adic root valuations `W` -/
  adapted : ∀ i < Yhat.card,
    ∃ T ≤ (Yhat.map fun y => y - recenter).map HahnSeries.orderTop,
      T.card = Yhat.card - i ∧
      T.sum + ((1 : ℚ) : WithTop ℚ) ≤ val p
        (shadow ((((Yhat.map fun y => y - recenter).map
            fun y => X - Polynomial.C y).prod).coeff i)
          - lift.coeff i)

namespace ChainState

variable {r : 𝕃_[p]} {s : ℚ} {Yhat : Multiset (HahnSeries ℚ (𝔽ᵃ_[p]))}
  {ahat : HahnSeries ℚ (𝔽ᵃ_[p])}

/-- Invariant (3) transported to the root factorization of the adapted lift over
the algebraically closed `𝕃_[p]`: the congruence hypothesis in the exact shape
consumed by `roots_continuity_forward` and the polygon-match transfer. -/
theorem shadow_congruence (St : ChainState r s Yhat ahat) :
    ∀ i < (Yhat.map fun y => y - St.recenter).card,
      ∃ T ≤ (Yhat.map fun y => y - St.recenter).map HahnSeries.orderTop,
        T.card = (Yhat.map fun y => y - St.recenter).card - i ∧
        T.sum + ((1 : ℚ) : WithTop ℚ) ≤ val p
          (shadow ((((Yhat.map fun y => y - St.recenter).map
              fun y => X - Polynomial.C y).prod).coeff i)
            - ((St.lift.roots.map fun z => X - Polynomial.C z).prod).coeff i) := by
  intro i hi
  rw [Multiset.card_map] at hi
  obtain ⟨T, hTle, hTcard, hTsum⟩ := St.adapted i hi
  refine ⟨T, hTle, by rw [Multiset.card_map, hTcard], ?_⟩
  rw [← (IsAlgClosed.splits St.lift).eq_prod_roots_of_monic St.lift_monic]
  exact hTsum

/-- **Polygon match**: the adapted congruence (invariant (3)) pins the
valuation multiset of the roots of the adapted lift over
the algebraically closed `𝕃_[p]` to the `t`-adic root-valuation multiset `W` of
the recentered hat polynomial. -/
theorem map_orderTop_eq_roots_map_val (St : ChainState r s Yhat ahat) :
    (Yhat.map fun y => y - St.recenter).map HahnSeries.orderTop
      = St.lift.roots.map (val p) := by
  classical
  have hprod : St.lift = (St.lift.roots.map fun z => X - Polynomial.C z).prod :=
    (IsAlgClosed.splits St.lift).eq_prod_roots_of_monic St.lift_monic
  have hZcard : St.lift.roots.card = Yhat.card := by
    have h := congrArg Polynomial.natDegree hprod
    rw [St.lift_natDegree, natDegree_multiset_prod_X_sub_C_eq_card] at h
    exact h.symm
  have hmapshadow : ((Yhat.map fun y => y - St.recenter).map shadow).map (val p)
      = (Yhat.map fun y => y - St.recenter).map HahnSeries.orderTop := by
    rw [Multiset.map_map]
    exact Multiset.map_congr rfl fun y _ => val_shadow _
  have hRmap : (((Yhat.map fun y => y - St.recenter).map shadow).map
        fun u => X - Polynomial.C u)
      = (Yhat.map fun y => y - St.recenter).map fun y => X - Polynomial.C (shadow y) := by
    rw [Multiset.map_map]
    rfl
  have hcong' : ∀ i < ((Yhat.map fun y => y - St.recenter).map shadow).card,
      ∃ T ≤ ((Yhat.map fun y => y - St.recenter).map shadow).map (val p),
        T.card = ((Yhat.map fun y => y - St.recenter).map shadow).card - i ∧
        T.sum + ((1 : ℚ) : WithTop ℚ) ≤ val p
          (((((Yhat.map fun y => y - St.recenter).map shadow).map
                fun u => X - Polynomial.C u).prod
              - (St.lift.roots.map fun z => X - Polynomial.C z).prod).coeff i) := by
    intro i hi
    rw [Multiset.card_map] at hi
    obtain ⟨T, hTle, hTcard, hTsum⟩ :=
      exists_sum_le_val_coeff_sub_of_shadow_congruence
        (Yhat.map fun y => y - St.recenter) St.lift.roots le_rfl
        St.shadow_congruence hi
    refine ⟨T, ?_, ?_, ?_⟩
    · rw [hmapshadow]
      exact hTle
    · rw [Multiset.card_map]
      exact hTcard
    · rw [hRmap]
      exact hTsum
  have h := map_v_eq_of_v_coeff_sub (v := val p)
    (fun x hx => val_eq_top_iff.mp hx)
    ((Yhat.map fun y => y - St.recenter).map shadow) St.lift.roots
    (by rw [Multiset.card_map, Multiset.card_map, hZcard]) (k := 1) one_pos hcong'
  rw [← hmapshadow]
  exact h.symm

/-- **Root extraction and slice recentering against an adapted lift**: from a
chain state whose current hat root `ŷ = ahat - ĝ` has exact depth `s_c`,
extract a root `z` of the adapted lift with `z ∈ C`, `val z = s_c` and
`val (S(ŷ) - z) ≥ s_c + 1/m` (`m` ≥ 1 the multiplicity of `s_c` among the
recentered `t`-adic root depths, `m ≤ n`), so that the residual advances at
depth `min (s + 1) (s_c + 1/m)`; recentering by the depth-one slice
`ŵ = trunc (s_c + 1) z` raises the hat-root depth to at least `s_c + 1/m` and
regenerates invariant (2) at the fixed depth `s + 1`.

The step does **not** re-establish invariant (3) at the recentered state; in
the one-shot descaling route of `lem:approx-by-integral` no re-established
lift is needed. -/
theorem exists_step (St : ChainState r s Yhat ahat) (hahat : ahat ∈ Yhat) {sc : ℚ}
    (hsc : (ahat - St.recenter).orderTop = (sc : WithTop ℚ)) :
    ∃ z ∈ St.lift.roots, ∃ m : ℕ,
      m = ((Yhat.map fun y => y - St.recenter).map HahnSeries.orderTop).count
        ((sc : WithTop ℚ)) ∧
      0 < m ∧ m ≤ Yhat.card ∧
      z ∈ closure (integralClosure ℚᵘⁿ_[p] 𝕃_[p]).carrier ∧
      val p z = (sc : WithTop ℚ) ∧
      ((sc + 1 / (m : ℚ) : ℚ) : WithTop ℚ) ≤ val p (shadow (ahat - St.recenter) - z) ∧
      min ((s + 1 : ℚ) : WithTop ℚ) ((sc + 1 / (m : ℚ) : ℚ) : WithTop ℚ)
        ≤ val p ((r - St.extracted) - z) ∧
      ((sc + 1 / (m : ℚ) : ℚ) : WithTop ℚ)
        ≤ (ahat - (St.recenter + trunc (sc + 1) z)).orderTop ∧
      ((s + 1 : ℚ) : WithTop ℚ) ≤ val p
        ((r - (St.extracted + z)) - shadow (ahat - (St.recenter + trunc (sc + 1) z))) := by
  classical
  -- extraction: evaluation at the exact shadow root plus `lem:approx-root`,
  -- packaged as the forward continuity of roots
  obtain ⟨z, hzZ, hzval, hznear⟩ := roots_continuity_forward
    (Yhat.map fun y => y - St.recenter) St.lift.roots
    St.map_orderTop_eq_roots_map_val (k := 1) le_rfl
    St.shadow_congruence (Multiset.mem_map_of_mem _ hahat) hsc
  -- the multiplicity is positive and bounded by the degree
  have hmem : ((sc : WithTop ℚ))
      ∈ (Yhat.map fun y => y - St.recenter).map HahnSeries.orderTop := by
    rw [← hsc]
    exact Multiset.mem_map_of_mem _ (Multiset.mem_map_of_mem _ hahat)
  have hm1 : 0 < ((Yhat.map fun y => y - St.recenter).map HahnSeries.orderTop).count
      ((sc : WithTop ℚ)) := Multiset.count_pos.mpr hmem
  have hmn : ((Yhat.map fun y => y - St.recenter).map HahnSeries.orderTop).count
      ((sc : WithTop ℚ)) ≤ Yhat.card := by
    refine le_trans (Multiset.count_le_card _ _) ?_
    rw [Multiset.card_map, Multiset.card_map]
  -- the extracted root lies in `C`
  have hzC : z ∈ closure (integralClosure ℚᵘⁿ_[p] 𝕃_[p]).carrier :=
    mem_closure_integralClosure_of_monic_root St.lift_monic St.lift_coeff_mem
      (Polynomial.mem_roots'.mp hzZ).2
  -- `s ≤ s_c` from invariant (1)
  have hssc : s ≤ sc := by
    have h := St.le_orderTop
    rw [hsc] at h
    exact_mod_cast h
  -- the depth-one slice approximates the root at depth `s_c + 1`
  have hslice : ((sc + 1 : ℚ) : WithTop ℚ) ≤ val p (z - shadow (trunc (sc + 1) z)) :=
    le_val_sub_shadow_trunc _ z
  have hm1' : (1 : ℚ) ≤
      (((Yhat.map fun y => y - St.recenter).map HahnSeries.orderTop).count
        ((sc : WithTop ℚ)) : ℚ) := by
    exact_mod_cast hm1
  refine ⟨z, hzZ, _, rfl, hm1, hmn, hzC, hzval, hznear, ?_, ?_, ?_⟩
  · -- the residual advances at depth `min (s + 1) (s_c + 1/m)`
    have hd : (r - St.extracted) - z
        = ((r - St.extracted) - shadow (ahat - St.recenter))
          + (shadow (ahat - St.recenter) - z) := by
      ring
    rw [hd]
    exact (val p).map_le_add (le_trans (min_le_left _ _) St.residual_approx)
      (le_trans (min_le_right _ _) hznear)
  · -- invariant (1) advances: the recentered hat root has depth `≥ s_c + 1/m`
    have harg : ahat - (St.recenter + trunc (sc + 1) z)
        = (ahat - St.recenter) - trunc (sc + 1) z := by
      ring
    rw [harg, ← val_shadow_sub]
    have hsplit : shadow (ahat - St.recenter) - shadow (trunc (sc + 1) z)
        = (shadow (ahat - St.recenter) - z) + (z - shadow (trunc (sc + 1) z)) := by
      ring
    rw [hsplit]
    refine (val p).map_le_add hznear (le_trans ?_ hslice)
    rw [WithTop.coe_le_coe]
    have hdiv : 1 / (((Yhat.map fun y => y - St.recenter).map HahnSeries.orderTop).count
        ((sc : WithTop ℚ)) : ℚ) ≤ 1 :=
      (div_le_one (by linarith)).mpr hm1'
    linarith
  · -- invariant (2) regenerates at the fixed depth `s + 1`
    have harg : ahat - (St.recenter + trunc (sc + 1) z)
        = (ahat - St.recenter) - trunc (sc + 1) z := by
      ring
    rw [harg]
    have hident : (r - (St.extracted + z))
          - shadow ((ahat - St.recenter) - trunc (sc + 1) z)
        = ((r - St.extracted) - shadow (ahat - St.recenter))
          + (shadow (ahat - St.recenter)
              - shadow ((ahat - St.recenter) - trunc (sc + 1) z)
              - shadow (trunc (sc + 1) z))
          + (shadow (trunc (sc + 1) z) - z) := by
      ring
    rw [hident]
    -- the middle term is one additive Teichmüller carry over the slice support
    have h2 : ((s + 1 : ℚ) : WithTop ℚ) ≤ val p
        (shadow (ahat - St.recenter)
          - shadow ((ahat - St.recenter) - trunc (sc + 1) z)
          - shadow (trunc (sc + 1) z)) := by
      have hov : ∀ q, ((ahat - St.recenter) - trunc (sc + 1) z).coeff q ≠ 0 →
          (trunc (sc + 1) z).coeff q ≠ 0 → sc ≤ q := by
        intro q _ hq
        refine le_of_not_gt fun hlt => hq ?_
        rw [coeff_trunc_of_lt (by linarith) z]
        refine coeff_eq_zero_of_lt_val ?_
        rw [hzval]
        exact_mod_cast hlt
      have hcarry := le_val_shadow_add_sub ((ahat - St.recenter) - trunc (sc + 1) z)
        (trunc (sc + 1) z) sc hov
      rw [sub_add_cancel] at hcarry
      refine le_trans ?_ hcarry
      rw [WithTop.coe_le_coe]
      linarith
    have h3 : ((s + 1 : ℚ) : WithTop ℚ) ≤ val p (shadow (trunc (sc + 1) z) - z) := by
      rw [(val p).map_sub_swap]
      refine le_trans ?_ hslice
      rw [WithTop.coe_le_coe]
      linarith
    exact (val p).map_le_add ((val p).map_le_add St.residual_approx h2) h3

end ChainState

end TrustworthyKedlaya.pAdicHahnSeries
