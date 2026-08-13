/-
Copyright (c) 2026 Shanwen Wang, Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import TrustworthyKedlaya.TruncUPClosure
public import TrustworthyKedlaya.LpAlgClosed
public import TrustworthyKedlaya.NewtonPolygonRoots

/-!
# The closed integral closure of `ℚᵘⁿ_[p]` is closed under roots of monic polynomials

Blueprint `lem:c-root-closed`: write `C` for the closure (valued topology) of the
integral closure of `ℚᵘⁿ_[p]` in `𝕃_[p]`.  Every root in `𝕃_[p]` of a monic
polynomial with coefficients in `C` lies in `C`.

Perturb each coefficient to an integral element at valuation depth `Θ`: the
perturbed polynomial `P'` is monic with integral coefficients, so all of its roots
are integral over `ℚᵘⁿ_[p]` (integrality is transitive through the integral
closure), and `v(P'(u)) ≥ Θ - B` with `B` fixed by the degree and `v(u)`.  Since
`P'` splits over the algebraically closed `𝕃_[p]` and `v(P'(u))` is the sum of the
`n` root distances `v(u - z)`, some root is within `(Θ - B)/n` of `u`; letting
`Θ → ∞` exhibits `u` as a limit of integral elements.

## Main statements

- `TrustworthyKedlaya.pAdicHahnSeries.mem_closure_integralClosure_of_monic_root`:
  `lem:c-root-closed`.

## References

- K. S. Kedlaya, *Power series and p-adic algebraic closures*, J. Number Theory 89
  (2001) [Ked01b], Section 3 (the (b)-freedom of the coefficient lifts).
-/

@[expose] public section

namespace TrustworthyKedlaya.pAdicHahnSeries

open Polynomial
open scoped TrustworthyKedlaya.UP

variable {p : ℕ} [hp : Fact (Nat.Prime p)]

/-- A root of a monic polynomial whose coefficients are integral over `ℚᵘⁿ_[p]` is
itself integral over `ℚᵘⁿ_[p]`: integrality is transitive through the integral
closure. -/
theorem isIntegral_QpUn_of_monic_root {P : Polynomial 𝕃_[p]} (hP : P.Monic)
    (hcoeff : ∀ i, IsIntegral ℚᵘⁿ_[p] (P.coeff i)) {z : 𝕃_[p]} (hz : P.IsRoot z) :
    IsIntegral ℚᵘⁿ_[p] z := by
  have : Nontrivial (integralClosure ℚᵘⁿ_[p] 𝕃_[p]) :=
    ⟨⟨0, 1, fun h => zero_ne_one (α := 𝕃_[p]) (congrArg Subtype.val h)⟩⟩
  -- lift `P` to a polynomial over the integral closure
  have hmem : P ∈ Polynomial.lifts (algebraMap (integralClosure ℚᵘⁿ_[p] 𝕃_[p]) 𝕃_[p]) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    exact fun i => ⟨⟨P.coeff i, hcoeff i⟩, rfl⟩
  obtain ⟨P₀, hP₀⟩ := hmem
  rw [Polynomial.coe_mapRingHom] at hP₀
  have hP₀monic : P₀.Monic := by
    have hinj : Function.Injective (algebraMap (integralClosure ℚᵘⁿ_[p] 𝕃_[p]) 𝕃_[p]) :=
      Subtype.val_injective
    exact Polynomial.monic_of_injective hinj (by rwa [hP₀])
  refine isIntegral_trans (A := integralClosure ℚᵘⁿ_[p] 𝕃_[p]) z ⟨P₀, hP₀monic, ?_⟩
  have := hz
  rw [Polynomial.IsRoot, ← hP₀, Polynomial.eval_map] at this
  exact this

/-- **The closed integral closure is closed under roots of monic polynomials**
(`lem:c-root-closed`): let `C` be the closure of the integral closure of `ℚᵘⁿ_[p]`
in `𝕃_[p]`.  Every root in `𝕃_[p]` of a monic polynomial with coefficients in `C`
lies in `C`. -/
theorem mem_closure_integralClosure_of_monic_root {P : Polynomial 𝕃_[p]} (hP : P.Monic)
    (hcoeff : ∀ i, P.coeff i ∈ closure (integralClosure ℚᵘⁿ_[p] 𝕃_[p]).carrier)
    {u : 𝕃_[p]} (hu : P.IsRoot u) :
    u ∈ closure (integralClosure ℚᵘⁿ_[p] 𝕃_[p]).carrier := by
  classical
  set n : ℕ := P.natDegree with hn
  -- degree zero is impossible: a monic constant does not vanish
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · exfalso
    have hP1 : P = 1 := hP.natDegree_eq_zero.mp hn0
    have := hu
    rw [Polynomial.IsRoot, hP1, Polynomial.eval_one] at this
    exact one_ne_zero this
  -- the zero root is integral outright
  rcases eq_or_ne u 0 with rfl | hune
  · exact subset_closure (Subalgebra.zero_mem _)
  -- the valuation of `u`, and a natural bound absorbing its negative powers
  obtain ⟨vu, hvu⟩ := WithTop.ne_top_iff_exists.mp
    (fun h => hune (val_eq_top_iff.mp h))
  obtain ⟨b, hb⟩ := exists_nat_ge ((n : ℚ) * max 0 (-vu))
  refine mem_closure_of_forall_exists_near fun n₀ => ?_
  -- integral approximants of the coefficients at depth `Θ = n·n₀ + b`
  set Θ : ℕ := n * n₀ + b with hΘ
  have happrox : ∀ i : ℕ, ∃ a ∈ (integralClosure ℚᵘⁿ_[p] 𝕃_[p]).carrier,
      ((Θ : ℚ) : WithTop ℚ) ≤ val p (P.coeff i - a) := fun i =>
    exists_near_of_mem_closure (hcoeff i) Θ
  choose a haS hanear using happrox
  -- the perturbed polynomial
  set P' : Polynomial 𝕃_[p] := X ^ n + ∑ i ∈ Finset.range n, C (a i) * X ^ i with hP'
  have hsumdeg : (∑ i ∈ Finset.range n, C (a i) * X ^ i).degree < ((n : ℕ) : WithBot ℕ) := by
    refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _) ?_
    rw [Finset.sup_lt_iff (by exact_mod_cast WithBot.bot_lt_coe n)]
    intro i hi
    refine lt_of_le_of_lt (Polynomial.degree_C_mul_X_pow_le _ _) ?_
    exact_mod_cast Finset.mem_range.mp hi
  have hP'monic : P'.Monic := Polynomial.monic_X_pow_add hsumdeg
  have hP'deg : P'.natDegree = n := by
    have hdeg : P'.degree = ((n : ℕ) : WithBot ℕ) := by
      rw [hP', Polynomial.degree_add_eq_left_of_degree_lt
        (by rw [Polynomial.degree_X_pow]; exact hsumdeg), Polynomial.degree_X_pow]
    exact Polynomial.natDegree_eq_of_degree_eq_some hdeg
  -- the perturbed coefficients are integral
  have hP'coeffint : ∀ i, IsIntegral ℚᵘⁿ_[p] (P'.coeff i) := by
    intro i
    rcases lt_trichotomy i n with hi | rfl | hi
    · have hcoeffi : P'.coeff i = a i := by
        rw [hP', Polynomial.coeff_add, Polynomial.coeff_X_pow, if_neg (Nat.ne_of_lt hi),
          zero_add, Polynomial.finsetSum_coeff]
        rw [Finset.sum_congr rfl fun j _ => Polynomial.coeff_C_mul_X_pow _ _ _]
        rw [Finset.sum_ite_eq (Finset.range n) i]
        rw [if_pos (Finset.mem_range.mpr hi)]
      rw [hcoeffi]
      exact haS i
    · have hcoeffn : P'.coeff n = 1 := hP'deg ▸ hP'monic.coeff_natDegree
      rw [hcoeffn]
      exact isIntegral_one
    · have hcoeffhi : P'.coeff i = 0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt (hP'deg ▸ hi)
      rw [hcoeffhi]
      exact isIntegral_zero
  -- the evaluation of `P'` at `u` is deep: it differs from `P(u) = 0` by the
  -- coefficient perturbations
  have hevaldiff : P'.eval u = ∑ i ∈ Finset.range n, (a i - P.coeff i) * u ^ i := by
    have hPsum : P.eval u = u ^ n + ∑ i ∈ Finset.range n, P.coeff i * u ^ i := by
      conv_lhs => rw [hP.as_sum]
      rw [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
        Polynomial.eval_finsetSum]
      simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
        Polynomial.eval_X]
      rw [hn]
    have hP'sum : P'.eval u = u ^ n + ∑ i ∈ Finset.range n, a i * u ^ i := by
      rw [hP', Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
        Polynomial.eval_finsetSum]
      simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
        Polynomial.eval_X]
    have hzero := hu
    rw [Polynomial.IsRoot, hPsum] at hzero
    have hsplit : ∑ i ∈ Finset.range n, (a i - P.coeff i) * u ^ i
        = (∑ i ∈ Finset.range n, a i * u ^ i)
          - ∑ i ∈ Finset.range n, P.coeff i * u ^ i := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hP'sum, hsplit]
    linear_combination hzero
  have hevaldeep : (((n * n₀ : ℕ) : ℚ) : WithTop ℚ) ≤ val p (P'.eval u) := by
    have hms : ((Finset.range n).val.map fun i => (a i - P.coeff i) * u ^ i).sum
        = ∑ i ∈ Finset.range n, (a i - P.coeff i) * u ^ i := rfl
    rw [hevaldiff, ← hms]
    refine AddValuation.le_map_multiset_sum (val p) fun x hx => ?_
    obtain ⟨i, hi, rfl⟩ := Multiset.mem_map.mp hx
    have hiran : i < n := Finset.mem_range.mp hi
    have hterm : val p ((a i - P.coeff i) * u ^ i)
        = val p (a i - P.coeff i) + i • val p u := by
      rw [(val p).map_mul, (val p).map_pow]
    rw [hterm, ← hvu]
    have hsmul : ∀ m : ℕ,
        (m • ((vu : ℚ) : WithTop ℚ) : WithTop ℚ) = ((m • vu : ℚ) : WithTop ℚ) := by
      intro m
      induction m with
      | zero => simp
      | succ k ih =>
        rw [succ_nsmul, succ_nsmul, ih, ← WithTop.coe_add]
    rw [hsmul i]
    have hswap : val p (a i - P.coeff i) = val p (P.coeff i - a i) := by
      rw [← neg_sub, (val p).map_neg]
    have hbound : (((n * n₀ : ℕ) : ℚ) : WithTop ℚ)
        ≤ ((Θ : ℚ) : WithTop ℚ) + ((i • vu : ℚ) : WithTop ℚ) := by
      rw [← WithTop.coe_add, WithTop.coe_le_coe]
      have hivu : -(b : ℚ) ≤ (i • vu : ℚ) := by
        rcases lt_or_ge vu 0 with hvu0 | hvu0
        · have h1 : (i • vu : ℚ) = (i : ℚ) * vu := by rw [nsmul_eq_mul]
          have h2 : (n : ℚ) * vu ≤ (i : ℚ) * vu := by
            refine mul_le_mul_of_nonpos_right ?_ hvu0.le
            exact_mod_cast hiran.le
          have h3 : (n : ℚ) * max 0 (-vu) = (n : ℚ) * (-vu) := by
            rw [max_eq_right (by linarith)]
          have h4 : (n : ℚ) * (-vu) ≤ (b : ℚ) := by rw [← h3]; exact hb
          have h5 : -(b : ℚ) ≤ (n : ℚ) * vu := by nlinarith
          linarith [h1, h2, h5]
        · have h1 : (0 : ℚ) ≤ (i • vu : ℚ) := by
            rw [nsmul_eq_mul]
            positivity
          have h2 : -(b : ℚ) ≤ 0 := by
            simp
          linarith
      have hΘq : ((Θ : ℚ)) = ((n * n₀ : ℕ) : ℚ) + (b : ℚ) := by
        rw [hΘ]
        push_cast
        ring
      rw [hΘq]
      linarith
    refine le_trans hbound ?_
    exact add_le_add (hswap ▸ hanear i) le_rfl
  -- split `P'` over the algebraically closed `𝕃_[p]`
  have hsplits : P'.Splits := IsAlgClosed.splits P'
  have hprod : P' = (P'.roots.map fun z => X - C z).prod :=
    hsplits.eq_prod_roots_of_monic hP'monic
  have hrootscard : P'.roots.card = n := by
    have h := congrArg Polynomial.natDegree hprod
    rw [hP'deg, natDegree_multiset_prod_X_sub_C_eq_card] at h
    exact h.symm
  -- `v(P'(u))` is the sum of the root distances
  have hevalsum : val p (P'.eval u) = (P'.roots.map fun z => val p (u - z)).sum := by
    conv_lhs => rw [hprod]
    rw [eval_multiset_prod, Multiset.map_map, AddValuation.map_multiset_prod,
      Multiset.map_map]
    refine congrArg Multiset.sum (Multiset.map_congr rfl fun z _ => ?_)
    simp only [Function.comp_apply, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_C]
  -- some root is within `n₀` of `u`
  have hnear : ∃ z ∈ P'.roots, ((n₀ : ℚ) : WithTop ℚ) ≤ val p (u - z) := by
    by_contra hcon
    push Not at hcon
    have hlt : (P'.roots.map fun z => val p (u - z)).sum
        < (Multiset.replicate n (((n₀ : ℚ) : WithTop ℚ))).sum := by
      refine sum_lt_sum_of_forall_lt ?_ ?_ ?_
      · rw [Multiset.card_map, hrootscard, Multiset.card_replicate]
      · intro h0
        have := congrArg Multiset.card h0
        rw [Multiset.card_map, hrootscard, Multiset.card_zero] at this
        exact hnpos.ne' this
      · intro x hx y hy
        obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.mp hx
        rw [Multiset.eq_of_mem_replicate hy]
        exact hcon z hz
    rw [← hevalsum, Multiset.sum_replicate] at hlt
    have hrepl : (n • (((n₀ : ℚ) : WithTop ℚ)) : WithTop ℚ)
        = (((n * n₀ : ℕ) : ℚ) : WithTop ℚ) := by
      induction n with
      | zero => simp
      | succ k ih =>
        rw [succ_nsmul, ih, ← WithTop.coe_add]
        congr 1
        push_cast
        ring
    rw [hrepl] at hlt
    exact absurd hevaldeep (not_le.mpr hlt)
  obtain ⟨z, hzroots, hznear⟩ := hnear
  -- the near root is integral over `ℚᵘⁿ_[p]`
  have hzint : IsIntegral ℚᵘⁿ_[p] z :=
    isIntegral_QpUn_of_monic_root hP'monic hP'coeffint
      (Polynomial.isRoot_of_mem_roots hzroots)
  exact ⟨z, hzint, hznear⟩

end TrustworthyKedlaya.pAdicHahnSeries
