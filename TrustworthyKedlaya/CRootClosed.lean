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
# The closed integral closure of `ℚᶜᵘⁿ_[p]` is closed under roots of monic polynomials

Write `C` for the closure (valued topology) of the integral closure of `ℚᶜᵘⁿ_[p]`
in `𝕃_[p]`.  Every root in `𝕃_[p]` of a monic polynomial with coefficients in `C`
lies in `C`.

Perturb each coefficient to an integral element at valuation depth `Θ`: the
perturbed polynomial `P'` is monic with integral coefficients, so all of its roots
are integral over `ℚᶜᵘⁿ_[p]` (integrality is transitive through the integral
closure), and `v(P'(u)) ≥ Θ - B` with `B` fixed by the degree and `v(u)`.  Since
`P'` splits over the algebraically closed `𝕃_[p]` and `v(P'(u))` is the sum of the
`n` root distances `v(u - z)`, some root is within `(Θ - B)/n` of `u`; letting
`Θ → ∞` exhibits `u` as a limit of integral elements.

## Main statements

- `TrustworthyKedlaya.pAdicHahnSeries.mem_closure_integralClosure_of_monic_root`:
  every root in `𝕃_[p]` of a monic polynomial with coefficients in `C` lies in `C`.

## References

- K. S. Kedlaya, *Power series and p-adic algebraic closures*, J. Number Theory 89
  (2001) [Ked01b], Section 3 (the (b)-freedom of the coefficient lifts).
-/

@[expose] public section

namespace TrustworthyKedlaya.pAdicHahnSeries

open Polynomial
open scoped TrustworthyKedlaya.UP

variable {p : ℕ} [hp : Fact (Nat.Prime p)]

/-- A root of a monic polynomial whose coefficients are integral over `ℚᶜᵘⁿ_[p]` is
itself integral over `ℚᶜᵘⁿ_[p]`: integrality is transitive through the integral
closure. -/
theorem isIntegral_QpCUn_of_monic_root {P : Polynomial 𝕃_[p]} (hP : P.Monic)
    (hcoeff : ∀ i, IsIntegral ℚᶜᵘⁿ_[p] (P.coeff i)) {z : 𝕃_[p]} (hz : P.IsRoot z) :
    IsIntegral ℚᶜᵘⁿ_[p] z := by
  have : Nontrivial (integralClosure ℚᶜᵘⁿ_[p] 𝕃_[p]) :=
    ⟨⟨0, 1, fun h => zero_ne_one (α := 𝕃_[p]) (congrArg Subtype.val h)⟩⟩
  -- lift `P` to a polynomial over the integral closure
  have hmem : P ∈ Polynomial.lifts (algebraMap (integralClosure ℚᶜᵘⁿ_[p] 𝕃_[p]) 𝕃_[p]) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    exact fun i => ⟨⟨P.coeff i, hcoeff i⟩, rfl⟩
  obtain ⟨P₀, hP₀⟩ := hmem
  rw [Polynomial.coe_mapRingHom] at hP₀
  have hP₀monic : P₀.Monic := by
    have hinj : Function.Injective (algebraMap (integralClosure ℚᶜᵘⁿ_[p] 𝕃_[p]) 𝕃_[p]) :=
      Subtype.val_injective
    exact Polynomial.monic_of_injective hinj (by rwa [hP₀])
  refine isIntegral_trans (A := integralClosure ℚᶜᵘⁿ_[p] 𝕃_[p]) z ⟨P₀, hP₀monic, ?_⟩
  have := hz
  rw [Polynomial.IsRoot, ← hP₀, Polynomial.eval_map] at this
  exact this

/-- **The closed integral closure is closed under roots of monic polynomials**:
let `C` be the closure of the integral closure of `ℚᶜᵘⁿ_[p]` in `𝕃_[p]`.  Every root
in `𝕃_[p]` of a monic polynomial with coefficients in `C` lies in `C`. -/
theorem mem_closure_integralClosure_of_monic_root {P : Polynomial 𝕃_[p]} (hP : P.Monic)
    (hcoeff : ∀ i, P.coeff i ∈ closure (integralClosure ℚᶜᵘⁿ_[p] 𝕃_[p]).carrier)
    {u : 𝕃_[p]} (hu : P.IsRoot u) :
    u ∈ closure (integralClosure ℚᶜᵘⁿ_[p] 𝕃_[p]).carrier := by
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
  have happrox : ∀ i : ℕ, ∃ a ∈ (integralClosure ℚᶜᵘⁿ_[p] 𝕃_[p]).carrier,
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
  have hP'coeffint : ∀ i, IsIntegral ℚᶜᵘⁿ_[p] (P'.coeff i) := by
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
  -- the near root is integral over `ℚᶜᵘⁿ_[p]`
  have hzint : IsIntegral ℚᶜᵘⁿ_[p] z :=
    isIntegral_QpCUn_of_monic_root hP'monic hP'coeffint
      (Polynomial.isRoot_of_mem_roots hzroots)
  exact ⟨z, hzint, hznear⟩

/-! ### The Artin-Schreier depth transfer -/

private theorem coe_nsmul_withTop (m : ℕ) (r : ℚ) :
    (m • ((r : ℚ) : WithTop ℚ) : WithTop ℚ) = ((m • r : ℚ) : WithTop ℚ) := by
  induction m with
  | zero => simp
  | succ k ih =>
    rw [succ_nsmul, succ_nsmul, ih, ← WithTop.coe_add]

/-- **Artin-Schreier depth transfer**: let `u ∈ 𝕃_[p]`
have valuation `γ > 0` and let `q ≥ 2`, so that `u` is an exact root of
`X^q - X + c*` with `c* := u - u^q` of valuation `γ`.  If `c' ∈ C` (the closed
integral closure of `ℚᶜᵘⁿ_[p]`) approximates `c*` to valuation `γ + e` with
`e > 0`, then some root `z` of `X^q - X + c'` satisfies `v(u - z) ≥ γ + e`, and
`z ∈ C`.

The Newton polygon of `X^q - X + c'` has vertices `(0, γ), (1, 0), (q, 0)`: its
valuation-`γ` root is *simple* and isolated from the `q - 1` unit roots, so the
approximation depth transfers to the root distance in full — there is no division
by the degree.

The hypothesis `0 < γ` is essential: for `γ < 0` the point `(1, 0)` lies above
the polygon and all `q` roots share the valuation `γ`.  In particular the
fractional-window pieces of the UP decomposition have `γ ∈ (-1/a, 0)`, so this
lemma does *not* apply to them as-is; the variant needed there works with the
recentered root-difference polygon in the width-refined benign regime
`(q-1)|γ| < 1`, with this proof as the template. -/
theorem exists_mem_closure_near_of_artinSchreier {u c' : 𝕃_[p]} {γ e : ℚ}
    (hγ : 0 < γ) (he : 0 < e) {q : ℕ} (hq : 2 ≤ q)
    (hu : val p u = ((γ : ℚ) : WithTop ℚ))
    (hc' : c' ∈ closure (integralClosure ℚᶜᵘⁿ_[p] 𝕃_[p]).carrier)
    (hnear : ((γ + e : ℚ) : WithTop ℚ) ≤ val p ((u - u ^ q) - c')) :
    ∃ z ∈ closure (integralClosure ℚᶜᵘⁿ_[p] 𝕃_[p]).carrier,
      ((γ + e : ℚ) : WithTop ℚ) ≤ val p (u - z) := by
  classical
  -- `c* = u - u^q` has valuation exactly `γ`, hence so does `c'`
  have huq : val p (u ^ q) = ((q • γ : ℚ) : WithTop ℚ) := by
    rw [(val p).map_pow, hu, coe_nsmul_withTop]
  have hγlt : ((γ : ℚ) : WithTop ℚ) < val p (u ^ q) := by
    rw [huq, WithTop.coe_lt_coe]
    have hq2 : (2 : ℚ) ≤ (q : ℚ) := by exact_mod_cast hq
    rw [nsmul_eq_mul]
    nlinarith
  have hcstar : val p (u - u ^ q) = ((γ : ℚ) : WithTop ℚ) := by
    rw [(val p).map_sub_eq_of_lt_left (hu ▸ hγlt : val p u < val p (u ^ q)), hu]
  have hvc' : val p c' = ((γ : ℚ) : WithTop ℚ) := by
    have hlt : val p (u - u ^ q) < val p ((u - u ^ q) - c') := by
      rw [hcstar]
      refine lt_of_lt_of_le ?_ hnear
      rw [WithTop.coe_lt_coe]
      linarith
    have := (val p).map_sub_eq_of_lt_left hlt
    rw [show (u - u ^ q) - ((u - u ^ q) - c') = c' by ring, hcstar] at this
    exact this
  -- the perturbed Artin-Schreier polynomial
  set A : Polynomial 𝕃_[p] := X ^ q + (-X + C c') with hA
  have hlindeg : (-X + C c' : Polynomial 𝕃_[p]).degree < ((q : ℕ) : WithBot ℕ) := by
    refine lt_of_le_of_lt (Polynomial.degree_add_le _ _) (max_lt ?_ ?_)
    · rw [Polynomial.degree_neg, Polynomial.degree_X]
      exact_mod_cast lt_of_lt_of_le Nat.one_lt_two hq
    · refine lt_of_le_of_lt Polynomial.degree_C_le ?_
      exact_mod_cast lt_of_lt_of_le Nat.zero_lt_two hq
  have hAmonic : A.Monic := by
    refine (Polynomial.monic_X_pow q).add_of_left ?_
    rw [Polynomial.degree_X_pow]
    exact hlindeg
  have hAdeg : A.natDegree = q := by
    have hdeg : A.degree = ((q : ℕ) : WithBot ℕ) := by
      rw [hA, Polynomial.degree_add_eq_left_of_degree_lt
        (by rw [Polynomial.degree_X_pow]; exact hlindeg), Polynomial.degree_X_pow]
    exact Polynomial.natDegree_eq_of_degree_eq_some hdeg
  have hAeval : A.eval u = -((u - u ^ q) - c') := by
    rw [hA]
    simp only [Polynomial.eval_add, Polynomial.eval_neg, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_C]
    ring
  have hAvaleval : ((γ + e : ℚ) : WithTop ℚ) ≤ val p (A.eval u) := by
    rw [hAeval, (val p).map_neg]
    exact hnear
  -- split over the algebraically closed `𝕃_[p]`
  have hsplits : A.Splits := IsAlgClosed.splits A
  have hprod : A = (A.roots.map fun z => X - C z).prod :=
    hsplits.eq_prod_roots_of_monic hAmonic
  set Z : Multiset 𝕃_[p] := A.roots with hZ
  have hZcard : Z.card = q := by
    have h := congrArg Polynomial.natDegree hprod
    rw [hAdeg, natDegree_multiset_prod_X_sub_C_eq_card] at h
    exact h.symm
  -- every root has nonnegative valuation
  have hroot_eq : ∀ z ∈ Z, z ^ q = z - c' := by
    intro z hz
    have h0 : A.eval z = 0 := Polynomial.isRoot_of_mem_roots hz
    rw [hA] at h0
    simp only [Polynomial.eval_add, Polynomial.eval_neg, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_C] at h0
    linear_combination h0
  have hZnonneg : ∀ z ∈ Z, (0 : WithTop ℚ) ≤ val p z := by
    intro z hz
    by_contra hneg
    rw [not_le] at hneg
    obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp (ne_top_of_lt hneg)
    have hrneg : r < 0 := by
      rw [← WithTop.coe_lt_coe, hr]
      exact hneg.trans_eq (WithTop.coe_zero).symm
    have hrltγ : val p z < val p c' := by
      rw [hvc', ← hr, WithTop.coe_lt_coe]
      linarith
    have hzsub : val p (z - c') = val p z := (val p).map_sub_eq_of_lt_left hrltγ
    have hzpow : val p (z ^ q) = ((q • r : ℚ) : WithTop ℚ) := by
      rw [(val p).map_pow, ← hr, coe_nsmul_withTop]
    have heq : ((q • r : ℚ) : WithTop ℚ) = ((r : ℚ) : WithTop ℚ) := by
      rw [← hzpow, hroot_eq z hz, hzsub, hr]
    have heqq : (q • r : ℚ) = r := WithTop.coe_injective heq
    rw [nsmul_eq_mul] at heqq
    have hq2 : (2 : ℚ) ≤ (q : ℚ) := by exact_mod_cast hq
    nlinarith
  -- the root valuations sum to `γ` (the constant coefficient)
  have hcoeff0 : A.coeff 0 = c' := by
    rw [hA]
    simp only [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_neg,
      Polynomial.coeff_X_zero, Polynomial.coeff_C_zero]
    rw [if_neg (by omega : ¬ (0 : ℕ) = q)]
    ring
  have hWsum : ((Z.map (val p)).sum : WithTop ℚ) = ((γ : ℚ) : WithTop ℚ) := by
    have h0 : A.coeff 0 = (Z.map fun z => -z).prod := by
      conv_lhs => rw [hprod]
      rw [Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_multiset_prod,
        Multiset.map_map]
      refine congrArg Multiset.prod (Multiset.map_congr rfl fun z _ => ?_)
      simp only [Function.comp_apply, Polynomial.eval_sub, Polynomial.eval_X,
        Polynomial.eval_C]
      ring
    have hv : val p (A.coeff 0) = (Z.map (val p)).sum := by
      rw [h0, AddValuation.map_multiset_prod, Multiset.map_map]
      refine congrArg Multiset.sum (Multiset.map_congr rfl fun z _ => ?_)
      simp only [Function.comp_apply]
      exact (val p).map_neg z
    rw [← hv, hcoeff0, hvc']
  -- the `X`-coefficient is a unit, so `q - 1` of the roots have valuation zero
  have hcoeff1 : A.coeff 1 = -1 := by
    rw [hA]
    simp only [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_neg,
      Polynomial.coeff_X_one]
    rw [Polynomial.coeff_C, if_neg (by omega : ¬ (1 : ℕ) = 0),
      if_neg (by omega : ¬ (1 : ℕ) = q)]
    ring
  obtain ⟨T, hTle, hTcard, hTmin, hTsum⟩ :=
    exists_sum_le_v_coeff_prod_X_sub_C (val p) Z (i := 1) (by rw [hZcard]; omega)
  have hTsum0 : T.sum ≤ (0 : WithTop ℚ) := by
    refine le_trans hTsum ?_
    rw [← hprod, hcoeff1, (val p).map_neg, (val p).map_one]
  have hTnonneg : ∀ t ∈ T, (0 : WithTop ℚ) ≤ t := by
    intro t ht
    have htW := Multiset.mem_of_le hTle ht
    obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.mp htW
    exact hZnonneg z hz
  have hTzero : ∀ t ∈ T, t = (0 : WithTop ℚ) := by
    intro t ht
    have h1 : t ≤ T.sum := Multiset.single_le_sum hTnonneg t ht
    exact le_antisymm (h1.trans hTsum0) (hTnonneg t ht)
  have hTsumzero : T.sum = (0 : WithTop ℚ) := by
    rw [Multiset.sum_eq_zero hTzero]
  -- the remaining root valuation is `γ`
  set W : Multiset (WithTop ℚ) := Z.map (val p) with hW
  have hWcard : W.card = q := by rw [hW, Multiset.card_map, hZcard]
  have hrestcard : (W - T).card = 1 := by
    rw [Multiset.card_sub hTle, hWcard, hTcard, hZcard]
    omega
  obtain ⟨w, hw⟩ := Multiset.card_eq_one.mp hrestcard
  have hWsplit : W = w ::ₘ T := by
    have h1 : W - T + T = W := Multiset.sub_add_cancel hTle
    rw [hw] at h1
    rw [← h1, Multiset.singleton_add]
  have hwγ : w = ((γ : ℚ) : WithTop ℚ) := by
    have h1 : W.sum = w + T.sum := by
      rw [hWsplit, Multiset.sum_cons]
    rw [hWsum, hTsumzero, add_zero] at h1
    exact h1.symm
  -- a designated root `z₀` of valuation `γ`; all other roots have valuation zero
  have hwmem : w ∈ W := hWsplit ▸ Multiset.mem_cons_self w T
  obtain ⟨z₀, hz₀Z, hvz₀⟩ := Multiset.mem_map.mp hwmem
  have hvz₀γ : val p z₀ = ((γ : ℚ) : WithTop ℚ) := hvz₀.trans hwγ
  have hZcons : Z = z₀ ::ₘ Z.erase z₀ := (Multiset.cons_erase hz₀Z).symm
  have herasemap : (Z.erase z₀).map (val p) = T := by
    have h1 : W = val p z₀ ::ₘ (Z.erase z₀).map (val p) := by
      rw [hW]
      conv_lhs => rw [hZcons]
      rw [Multiset.map_cons]
    rw [hvz₀γ, ← hwγ] at h1
    have h2 : w ::ₘ (Z.erase z₀).map (val p) = w ::ₘ T := h1.symm.trans hWsplit
    exact Multiset.cons_inj_right w |>.mp h2
  have herasezero : ∀ z ∈ Z.erase z₀, val p z = (0 : WithTop ℚ) := by
    intro z hz
    refine hTzero _ ?_
    rw [← herasemap]
    exact Multiset.mem_map_of_mem _ hz
  -- the distance to every unit root is exactly zero
  have hdistzero : ∀ z ∈ Z.erase z₀, val p (u - z) = (0 : WithTop ℚ) := by
    intro z hz
    have hlt : val p z < val p u := by
      rw [herasezero z hz, hu, ← WithTop.coe_zero, WithTop.coe_lt_coe]
      exact hγ
    rw [(val p).map_sub_eq_of_lt_right hlt]
    exact herasezero z hz
  -- the whole evaluation valuation concentrates on `z₀`
  have hevalsum : val p (A.eval u) = (Z.map fun z => val p (u - z)).sum := by
    conv_lhs => rw [hprod]
    rw [Polynomial.eval_multiset_prod, Multiset.map_map, AddValuation.map_multiset_prod,
      Multiset.map_map]
    refine congrArg Multiset.sum (Multiset.map_congr rfl fun z _ => ?_)
    simp only [Function.comp_apply, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_C]
  have hz₀near : ((γ + e : ℚ) : WithTop ℚ) ≤ val p (u - z₀) := by
    have h1 : (Z.map fun z => val p (u - z)).sum = val p (u - z₀) := by
      conv_lhs => rw [hZcons]
      rw [Multiset.map_cons, Multiset.sum_cons, Multiset.sum_eq_zero
        (fun x hx => by
          obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.mp hx
          exact hdistzero z hz), add_zero]
    rw [hevalsum, h1] at hAvaleval
    exact hAvaleval
  -- the designated root lies in the closed integral closure
  have hAcoeffC : ∀ i, A.coeff i ∈ closure (integralClosure ℚᶜᵘⁿ_[p] 𝕃_[p]).carrier := by
    intro i
    rcases Nat.eq_zero_or_pos i with rfl | hipos
    · rw [hcoeff0]
      exact hc'
    rcases eq_or_ne i 1 with rfl | hi1
    · rw [hcoeff1]
      exact subset_closure (Subalgebra.neg_mem _ (Subalgebra.one_mem _))
    have hcoeffi : A.coeff i = if i = q then 1 else 0 := by
      rw [hA]
      simp only [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_neg,
        Polynomial.coeff_X, Polynomial.coeff_C]
      rw [if_neg (by omega : ¬ i = 0), if_neg (by omega : ¬ (1 : ℕ) = i)]
      ring
    rw [hcoeffi]
    split
    · exact subset_closure (Subalgebra.one_mem _)
    · exact subset_closure (Subalgebra.zero_mem _)
  have hz₀C : z₀ ∈ closure (integralClosure ℚᶜᵘⁿ_[p] 𝕃_[p]).carrier :=
    mem_closure_integralClosure_of_monic_root hAmonic hAcoeffC
      (Polynomial.isRoot_of_mem_roots hz₀Z)
  exact ⟨z₀, hz₀C, hz₀near⟩

/-! ### The closed integral closure is a subring -/

/-- `C` contains the image of `ℚᶜᵘⁿ_[p]`. -/
theorem algebraMap_mem_closure_integralClosure (c : ℚᶜᵘⁿ_[p]) :
    algebraMap ℚᶜᵘⁿ_[p] 𝕃_[p] c ∈ closure (integralClosure ℚᶜᵘⁿ_[p] 𝕃_[p]).carrier :=
  subset_closure (Subalgebra.algebraMap_mem _ c)

/-- `C` is closed under addition: approximants add. -/
theorem add_mem_closure_integralClosure {x y : 𝕃_[p]}
    (hx : x ∈ closure (integralClosure ℚᶜᵘⁿ_[p] 𝕃_[p]).carrier)
    (hy : y ∈ closure (integralClosure ℚᶜᵘⁿ_[p] 𝕃_[p]).carrier) :
    x + y ∈ closure (integralClosure ℚᶜᵘⁿ_[p] 𝕃_[p]).carrier := by
  refine mem_closure_of_forall_exists_near fun n => ?_
  obtain ⟨a, haS, hax⟩ := exists_near_of_mem_closure hx n
  obtain ⟨b, hbS, hby⟩ := exists_near_of_mem_closure hy n
  refine ⟨a + b, Subalgebra.add_mem _ haS hbS, ?_⟩
  have hsplit : (x + y) - (a + b) = (x - a) + (y - b) := by ring
  rw [hsplit]
  exact (val p).map_le_add hax hby

/-- `C` is closed under negation. -/
theorem neg_mem_closure_integralClosure {x : 𝕃_[p]}
    (hx : x ∈ closure (integralClosure ℚᶜᵘⁿ_[p] 𝕃_[p]).carrier) :
    -x ∈ closure (integralClosure ℚᶜᵘⁿ_[p] 𝕃_[p]).carrier := by
  refine mem_closure_of_forall_exists_near fun n => ?_
  obtain ⟨a, haS, hax⟩ := exists_near_of_mem_closure hx n
  refine ⟨-a, Subalgebra.neg_mem _ haS, ?_⟩
  have hsplit : -x - -a = a - x := by ring
  rw [hsplit, (val p).map_sub_swap]
  exact hax

/-- `C` is closed under multiplication: `xy - ab = x(y - b) + b(x - a)`, and the
valuations of `x` and `b` are bounded below independently of the approximation
depth. -/
theorem mul_mem_closure_integralClosure {x y : 𝕃_[p]}
    (hx : x ∈ closure (integralClosure ℚᶜᵘⁿ_[p] 𝕃_[p]).carrier)
    (hy : y ∈ closure (integralClosure ℚᶜᵘⁿ_[p] 𝕃_[p]).carrier) :
    x * y ∈ closure (integralClosure ℚᶜᵘⁿ_[p] 𝕃_[p]).carrier := by
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [zero_mul]
    exact subset_closure (Subalgebra.zero_mem _)
  rcases eq_or_ne y 0 with rfl | hy0
  · rw [mul_zero]
    exact subset_closure (Subalgebra.zero_mem _)
  obtain ⟨vx, hvx⟩ := WithTop.ne_top_iff_exists.mp
    (fun h => hx0 (val_eq_top_iff.mp h))
  obtain ⟨vy, hvy⟩ := WithTop.ne_top_iff_exists.mp
    (fun h => hy0 (val_eq_top_iff.mp h))
  obtain ⟨M, hM⟩ := exists_nat_ge (max 0 (max (-vx) (-vy)))
  have hMx : -vx ≤ (M : ℚ) := le_trans (le_max_of_le_right (le_max_left _ _)) hM
  have hMy : -vy ≤ (M : ℚ) := le_trans (le_max_of_le_right (le_max_right _ _)) hM
  refine mem_closure_of_forall_exists_near fun n => ?_
  obtain ⟨a, haS, hax⟩ := exists_near_of_mem_closure hx (n + M)
  obtain ⟨b, hbS, hby⟩ := exists_near_of_mem_closure hy (n + M)
  refine ⟨a * b, Subalgebra.mul_mem _ haS hbS, ?_⟩
  have hsplit : x * y - a * b = x * (y - b) + b * (x - a) := by ring
  rw [hsplit]
  refine (val p).map_le_add ?_ ?_
  · rw [(val p).map_mul, ← hvx]
    calc ((n : ℚ) : WithTop ℚ) ≤ ((vx + (n + M : ℕ) : ℚ) : WithTop ℚ) := by
          rw [WithTop.coe_le_coe]
          push_cast
          linarith
      _ = ((vx : ℚ) : WithTop ℚ) + (((n + M : ℕ) : ℚ) : WithTop ℚ) := by
          rw [← WithTop.coe_add]
      _ ≤ ((vx : ℚ) : WithTop ℚ) + val p (y - b) := add_le_add le_rfl hby
  · rw [(val p).map_mul]
    have hvb : min ((vy : WithTop ℚ)) ((((n + M : ℕ) : ℚ)) : WithTop ℚ) ≤ val p b := by
      have hb : b = y - (y - b) := by ring
      rw [hb]
      exact (val p).map_le_sub (le_trans (min_le_left _ _) (le_of_eq hvy))
        (le_trans (min_le_right _ _) hby)
    rcases le_total (vy : WithTop ℚ) ((((n + M : ℕ) : ℚ)) : WithTop ℚ) with hmin | hmin
    · rw [min_eq_left hmin] at hvb
      calc ((n : ℚ) : WithTop ℚ) ≤ ((vy + (n + M : ℕ) : ℚ) : WithTop ℚ) := by
            rw [WithTop.coe_le_coe]
            push_cast
            linarith
        _ = ((vy : ℚ) : WithTop ℚ) + (((n + M : ℕ) : ℚ) : WithTop ℚ) := by
            rw [← WithTop.coe_add]
        _ ≤ val p b + val p (x - a) := add_le_add hvb hax
    · rw [min_eq_right hmin] at hvb
      calc ((n : ℚ) : WithTop ℚ)
          ≤ (((n + M : ℕ) + (n + M : ℕ) : ℚ) : WithTop ℚ) := by
            rw [WithTop.coe_le_coe]
            push_cast
            linarith
        _ = (((n + M : ℕ) : ℚ) : WithTop ℚ) + (((n + M : ℕ) : ℚ) : WithTop ℚ) := by
            rw [← WithTop.coe_add]
        _ ≤ val p b + val p (x - a) := add_le_add hvb hax

/-- `C` is closed under powers. -/
theorem pow_mem_closure_integralClosure {x : 𝕃_[p]}
    (hx : x ∈ closure (integralClosure ℚᶜᵘⁿ_[p] 𝕃_[p]).carrier) (n : ℕ) :
    x ^ n ∈ closure (integralClosure ℚᶜᵘⁿ_[p] 𝕃_[p]).carrier := by
  induction n with
  | zero =>
    rw [pow_zero]
    exact subset_closure (Subalgebra.one_mem _)
  | succ n ih =>
    rw [pow_succ]
    exact mul_mem_closure_integralClosure ih hx

end TrustworthyKedlaya.pAdicHahnSeries
