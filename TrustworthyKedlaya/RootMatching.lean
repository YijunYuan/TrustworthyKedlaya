/-
Copyright (c) 2026 Shanwen Wang, Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.RingTheory.Polynomial.Vieta
public import Mathlib.RingTheory.Valuation.Basic

/-!
# Valuation floors and root matching for split polynomials

Generic valued-ring toolkit for the cross-characteristic Newton comparison
(Kedlaya 2001b, the lemma on continuity of roots).  Throughout,
`v : AddValuation F (WithTop ℚ)` on a commutative ring `F`.

The "sum of the `j` smallest elements" `σ_j(W)` of a multiset `W` of valuations is
encoded by its attaining witnesses: a sub-multiset `T ≤ W` of size `j` whose sum is
minimal among all such (`exists_min_sum_powersetCard`).  Statements quantify over
such witnesses instead of a `σ` function.

- `exists_sum_le_v_coeff_prod_X_sub_C`: the coefficient of
  `X^i` in `∏_{y ∈ Y} (X - y)` has valuation at least `σ_{n-i}(v(Y))`, delivered as a
  minimal witness `T` with `T.sum ≤ v(coeff)`;
- `exists_root_sub_valuation_le`: if two split monic
  polynomials of the same degree `n` have equal valuation multisets `W` and their
  coefficients at `X^i` differ by valuation at least `σ_{n-i}(W) + k`, then for every
  root `u` of the first of valuation `s` there is a root `z` of the second with
  `v z = s` and `v (u - z) ≥ s + k/m`, where `m` is the multiplicity of `s` in `W`.

## References

- K. S. Kedlaya, *Power series and p-adic algebraic closures*, J. Number Theory 89
  (2001) [Ked01b], Lemma preceding the Theorem in Section 3.
-/

@[expose] public section

namespace TrustworthyKedlaya

open Polynomial Multiset

/-! ### Minimal-sum witnesses among fixed-size sub-multisets -/

/-- Among the sub-multisets of `W` of size `j ≤ card W` there is one of minimal sum:
the attaining witness for "the sum of the `j` smallest elements of `W`". -/
theorem exists_min_sum_powersetCard (W : Multiset (WithTop ℚ)) {j : ℕ} (hj : j ≤ W.card) :
    ∃ T ≤ W, T.card = j ∧ ∀ T' ≤ W, T'.card = j → T.sum ≤ T'.sum := by
  classical
  have hne : (W.powersetCard j).toFinset.Nonempty := by
    rw [Multiset.toFinset_nonempty]
    intro h0
    have hcard := Multiset.card_powersetCard j W
    rw [h0] at hcard
    exact absurd hcard.symm (Nat.choose_pos hj).ne'
  obtain ⟨T, hTmem, hTmin⟩ :=
    Finset.exists_min_image (W.powersetCard j).toFinset Multiset.sum hne
  rw [Multiset.mem_toFinset, Multiset.mem_powersetCard] at hTmem
  refine ⟨T, hTmem.1, hTmem.2, fun T' hT' hT'card => ?_⟩
  exact hTmin T' (by rw [Multiset.mem_toFinset, Multiset.mem_powersetCard]; exact ⟨hT', hT'card⟩)

/-- Any sub-multiset `T ≤ W` bounds the truncated sum from above:
`∑_{w ∈ W} min(s, w) ≤ T.sum + (card W - card T) • s`. -/
theorem sum_map_min_le_add {W T : Multiset (WithTop ℚ)} (hT : T ≤ W) (s : ℚ) :
    (W.map fun w => min (s : WithTop ℚ) w).sum
      ≤ T.sum + (W.card - T.card) • ((s : WithTop ℚ)) := by
  obtain ⟨D, rfl⟩ := Multiset.le_iff_exists_add.mp hT
  rw [Multiset.map_add, Multiset.sum_add, Multiset.card_add, add_tsub_cancel_left]
  refine add_le_add ?_ ?_
  · exact Multiset.sum_map_le_sum _ fun x _ => min_le_right _ _
  · have h := Multiset.sum_le_card_nsmul (D.map fun w => min (s : WithTop ℚ) w)
      ((s : WithTop ℚ)) ?_
    · rwa [Multiset.card_map] at h
    · intro x hx
      obtain ⟨w, _, rfl⟩ := Multiset.mem_map.mp hx
      exact min_le_left _ _

/-! ### Valuations of multiset products and sums -/

variable {F : Type*} [CommRing F] (v : AddValuation F (WithTop ℚ))

/-- An additive valuation turns multiset products into sums of valuations. -/
theorem AddValuation.map_multiset_prod (M : Multiset F) : v M.prod = (M.map v).sum := by
  induction M using Multiset.induction_on with
  | empty => simp
  | cons a t ih => rw [Multiset.prod_cons, v.map_mul, ih, Multiset.map_cons, Multiset.sum_cons]

/-- A uniform lower bound on the valuations of the elements of a multiset bounds the
valuation of its sum. -/
theorem AddValuation.le_map_multiset_sum {M : Multiset F} {g : WithTop ℚ}
    (h : ∀ x ∈ M, g ≤ v x) : g ≤ v M.sum := by
  induction M using Multiset.induction_on with
  | empty => rw [Multiset.sum_zero, v.map_zero]; exact le_top
  | cons a t ih =>
    rw [Multiset.sum_cons]
    exact v.map_le_add (h a (Multiset.mem_cons_self a t))
      (ih fun x hx => h x (Multiset.mem_cons_of_mem hx))

/-! ### Coefficient floors of a split polynomial -/

/-- A minimal-sum witness bounds the valuation of an elementary symmetric function:
if `T ≤ Y.map v` has minimal sum among sub-multisets of its size, then
`T.sum ≤ v (esymm Y (T.card))`. -/
theorem sum_le_v_esymm (Y : Multiset F) {T : Multiset (WithTop ℚ)}
    (hmin : ∀ T' ≤ Y.map v, T'.card = T.card → T.sum ≤ T'.sum) :
    T.sum ≤ v (Y.esymm T.card) := by
  rw [Multiset.esymm]
  refine AddValuation.le_map_multiset_sum v fun x hx => ?_
  obtain ⟨T', hT'mem, rfl⟩ := Multiset.mem_map.mp hx
  rw [Multiset.mem_powersetCard] at hT'mem
  rw [AddValuation.map_multiset_prod]
  refine hmin (T'.map v) (Multiset.map_le_map hT'mem.1) ?_
  rw [Multiset.card_map, hT'mem.2]

/-- **Coefficient floor of a split polynomial**: the
coefficient of `X^i` in `∏_{y ∈ Y}(X - y)` has valuation at least the sum of the
`card Y - i` smallest valuations of `Y`, delivered by a minimal witness `T`. -/
theorem exists_sum_le_v_coeff_prod_X_sub_C (Y : Multiset F) {i : ℕ} (hi : i ≤ Y.card) :
    ∃ T ≤ Y.map v, T.card = Y.card - i ∧
      (∀ T' ≤ Y.map v, T'.card = Y.card - i → T.sum ≤ T'.sum) ∧
      T.sum ≤ v (((Y.map fun y => X - C y).prod).coeff i) := by
  obtain ⟨T, hT, hTcard, hTmin⟩ := exists_min_sum_powersetCard (Y.map v)
    (j := Y.card - i) (by rw [Multiset.card_map]; exact Nat.sub_le _ _)
  refine ⟨T, hT, hTcard, hTmin, ?_⟩
  rw [Multiset.prod_X_sub_C_coeff Y hi, v.map_mul]
  have hunit : v ((-1 : F) ^ (Y.card - i)) = 0 := by
    rw [v.map_pow, v.map_neg, v.map_one, smul_zero]
  rw [hunit, zero_add]
  have := sum_le_v_esymm v Y (by rw [hTcard]; exact hTmin)
  rwa [hTcard] at this

/-! ### An approximate root is close to a root -/

/-- **An approximate root is close to a root**: let `Z` be a
finite root multiset with `Q = ∏_{z ∈ Z}(X - z)`, and let `u` have valuation `s`,
with `s` occurring in the valuation multiset `v(Z)` with multiplicity `m ≥ 1`.
If `v(Q(u)) ≥ ∑_{z ∈ Z} min(s, v z) + k`, then some root `z ∈ Z` has `v z = s`
and `v (u - z) ≥ s + k/m`.

Each factor of `Q(u) = ∏_z (u - z)` obeys `v(u - z) ≥ min(s, v z)`, with equality
whenever `v z ≠ s`; subtracting `∑_z min(s, v z)` from the hypothesis concentrates
the excess `k` on the `m` factors of valuation `s`, and a maximal one exceeds
`s + k/m`. -/
theorem exists_root_sub_valuation_le_of_le_v_eval [Nontrivial F]
    (Z : Multiset F) {u : F} {s : ℚ} (hs : v u = (s : WithTop ℚ))
    (hsZ : ((s : WithTop ℚ)) ∈ Z.map v) {k : ℚ}
    (hVs : (Z.map fun z => min ((s : WithTop ℚ)) (v z)).sum + (k : WithTop ℚ)
      ≤ v (((Z.map fun y => X - C y).prod).eval u)) :
    ∃ z ∈ Z, v z = (s : WithTop ℚ) ∧
      ((s + k / ((Z.map v).count ((s : WithTop ℚ)) : ℚ) : ℚ) : WithTop ℚ) ≤ v (u - z) := by
  classical
  set Q : F[X] := (Z.map fun y => X - C y).prod with hQ
  set m : ℕ := (Z.map v).count ((s : WithTop ℚ)) with hm
  have hmpos : 0 < m := Multiset.count_pos.mpr hsZ
  -- the roots of `Q` of valuation `s`, and the rest
  set Zs : Multiset F := Z.filter (fun z => (s : WithTop ℚ) = v z) with hZs
  set Zr : Multiset F := Z.filter (fun z => ¬ ((s : WithTop ℚ) = v z)) with hZr
  have hZsplit : Zs + Zr = Z := Multiset.filter_add_not _ Z
  have hZscard : Zs.card = m := by
    rw [hZs, hm, Multiset.count_map]
  have hZs_ne : Zs ≠ 0 := by
    intro h0
    rw [h0, Multiset.card_zero] at hZscard
    exact absurd hZscard.symm hmpos.ne'
  -- trivial case: `u` itself occurs among the valuation-`s` roots of `Q`
  by_cases htriv : ∃ z ∈ Zs, v (u - z) = ⊤
  · obtain ⟨z, hzZs, hztop⟩ := htriv
    have hzmem := Multiset.mem_filter.mp hzZs
    exact ⟨z, hzmem.1, hzmem.2.symm, hztop ▸ le_top⟩
  · push Not at htriv
    -- pick a valuation-`s` root of `Q` maximizing `v (u - ·)`
    have hZsFin : Zs.toFinset.Nonempty := Multiset.toFinset_nonempty.mpr hZs_ne
    obtain ⟨z₀, hz₀mem, hz₀max⟩ :=
      Finset.exists_max_image Zs.toFinset (fun z => v (u - z)) hZsFin
    rw [Multiset.mem_toFinset] at hz₀mem
    have hz₀Z : z₀ ∈ Z := (Multiset.mem_filter.mp hz₀mem).1
    have hz₀val : v z₀ = (s : WithTop ℚ) := ((Multiset.mem_filter.mp hz₀mem).2).symm
    refine ⟨z₀, hz₀Z, hz₀val, ?_⟩
    -- the product expansion `v (Q(u)) = ∑_z v (u - z)`
    have hQprod : v (Q.eval u) = (Z.map fun z => v (u - z)).sum := by
      rw [hQ, eval_multiset_prod, Multiset.map_map, AddValuation.map_multiset_prod,
        Multiset.map_map]
      congr 1
      refine Multiset.map_congr rfl fun z _ => ?_
      simp
    -- split off the valuation-`s` part on both sides
    have hsum_split : (Z.map fun z => v (u - z)).sum
        = (Zs.map fun z => v (u - z)).sum + (Zr.map fun z => v (u - z)).sum := by
      rw [← hZsplit, Multiset.map_add, Multiset.sum_add]
    have hmin_split : (Z.map fun z => min ((s : WithTop ℚ)) (v z)).sum
        = m • ((s : WithTop ℚ)) + (Zr.map fun z => min ((s : WithTop ℚ)) (v z)).sum := by
      rw [← hZsplit, Multiset.map_add, Multiset.sum_add]
      congr 1
      have : Zs.map (fun z => min ((s : WithTop ℚ)) (v z))
          = Zs.map (fun _ => ((s : WithTop ℚ))) := by
        refine Multiset.map_congr rfl fun z hz => ?_
        rw [← (Multiset.mem_filter.mp hz).2, min_self]
      rw [this, Multiset.map_const', Multiset.sum_replicate, hZscard]
    -- off the valuation-`s` part the factors have valuation exactly `min(s, v z)`
    have hZr_exact : (Zr.map fun z => v (u - z)).sum
        = (Zr.map fun z => min ((s : WithTop ℚ)) (v z)).sum := by
      refine congrArg Multiset.sum (Multiset.map_congr rfl fun z hz => ?_)
      have hzne : ¬ ((s : WithTop ℚ) = v z) := (Multiset.mem_filter.mp hz).2
      have hne' : v u ≠ v z := by rw [hs]; exact hzne
      rcases lt_or_gt_of_ne hne' with hlt | hgt
      · -- `v u < v z`: `v (u - z) = v u = s = min`
        have h1 : ((s : ℚ) : WithTop ℚ) < v z := by rw [← hs]; exact hlt
        rw [v.map_sub_eq_of_lt_left hlt, hs, min_eq_left h1.le]
      · -- `v z < v u`: `v (u - z) = v z = min`
        have h2 : v z < ((s : ℚ) : WithTop ℚ) := by rw [← hs]; exact hgt
        rw [v.map_sub_eq_of_lt_right hgt, min_eq_right h2.le]
    -- the tail sum is finite
    have hC_ne_top : (Zr.map fun z => min ((s : WithTop ℚ)) (v z)).sum ≠ ⊤ := by
      have hle : (Zr.map fun z => min ((s : WithTop ℚ)) (v z)).sum
          ≤ Zr.card • ((s : WithTop ℚ)) := by
        have h := Multiset.sum_le_card_nsmul (Zr.map fun z => min ((s : WithTop ℚ)) (v z))
          ((s : WithTop ℚ)) ?_
        · rwa [Multiset.card_map] at h
        · intro x hx
          obtain ⟨z, _, rfl⟩ := Multiset.mem_map.mp hx
          exact min_le_left _ _
      refine ne_top_of_le_ne_top ?_ hle
      induction Zr.card with
      | zero => simp
      | succ c ih => rw [succ_nsmul]; exact WithTop.add_ne_top.mpr ⟨ih, WithTop.coe_ne_top⟩
    -- every valuation-`s` factor is bounded by the maximal one
    have hZs_le : (Zs.map fun z => v (u - z)).sum ≤ m • v (u - z₀) := by
      have h := Multiset.sum_le_card_nsmul (Zs.map fun z => v (u - z)) (v (u - z₀)) ?_
      · rwa [Multiset.card_map, hZscard] at h
      · intro x hx
        obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.mp hx
        exact hz₀max z (Multiset.mem_toFinset.mpr hz)
    -- assemble: `m • s + k ≤ m • v (u - z₀)`
    have hkey : m • ((s : WithTop ℚ)) + (k : WithTop ℚ) ≤ m • v (u - z₀) := by
      have hchain : (m • ((s : WithTop ℚ)) + (k : WithTop ℚ))
            + (Zr.map fun z => min ((s : WithTop ℚ)) (v z)).sum
          ≤ m • v (u - z₀) + (Zr.map fun z => min ((s : WithTop ℚ)) (v z)).sum := by
        calc (m • ((s : WithTop ℚ)) + (k : WithTop ℚ))
              + (Zr.map fun z => min ((s : WithTop ℚ)) (v z)).sum
            = (m • ((s : WithTop ℚ))
              + (Zr.map fun z => min ((s : WithTop ℚ)) (v z)).sum) + (k : WithTop ℚ) := by
              rw [add_right_comm]
          _ = (Z.map fun z => min ((s : WithTop ℚ)) (v z)).sum + (k : WithTop ℚ) := by
              rw [← hmin_split]
          _ ≤ v (Q.eval u) := hVs
          _ = (Zs.map fun z => v (u - z)).sum + (Zr.map fun z => v (u - z)).sum := by
              rw [hQprod, hsum_split]
          _ = (Zs.map fun z => v (u - z)).sum
              + (Zr.map fun z => min ((s : WithTop ℚ)) (v z)).sum := by rw [hZr_exact]
          _ ≤ m • v (u - z₀) + (Zr.map fun z => min ((s : WithTop ℚ)) (v z)).sum :=
              add_le_add hZs_le le_rfl
      exact (WithTop.add_le_add_iff_right hC_ne_top).mp hchain
    -- untop and divide by the multiplicity
    obtain ⟨c, hc⟩ := WithTop.ne_top_iff_exists.mp (htriv z₀ hz₀mem)
    rw [← hc] at hkey ⊢
    rw [← WithTop.coe_nsmul, ← WithTop.coe_nsmul, ← WithTop.coe_add,
      WithTop.coe_le_coe] at hkey
    rw [WithTop.coe_le_coe]
    have hmQ : (0 : ℚ) < (m : ℚ) := Nat.cast_pos.mpr hmpos
    rw [nsmul_eq_mul, nsmul_eq_mul] at hkey
    have h2 : k / (m : ℚ) ≤ c - s := by
      rw [div_le_iff₀ hmQ]
      nlinarith [hkey]
    linarith [h2]

/-! ### Root matching -/

/-- **Root matching for coefficientwise-close split polynomials**
(the single-field core of Kedlaya 2001b's continuity of
roots).  Let `U, Z` be root multisets with equal valuation multisets `W`, and suppose
the products `R = ∏_{u ∈ U}(X - u)` and `Q = ∏_{z ∈ Z}(X - z)` are coefficientwise
close: for each `i < n` some size-`(n-i)` sub-multiset `T ≤ W` has
`T.sum + k ≤ v((R - Q).coeff i)`.  Then every `u ∈ U` of valuation `s` is within
`s + k/m` of some `z ∈ Z` of valuation `s`, where `m` is the multiplicity of `s`
in `W`.

The proof evaluates `Q` at `u`: `v(Q(u)) = v((R-Q)(u)) ≥ ∑_w min(s, w) + k`, while
`Q(u) = ∏_z (u - z)` with each factor of valuation exactly `min(s, v z)` unless
`v z = s`; the excess `k` therefore concentrates on the `m` factors of valuation `s`,
and a maximal one exceeds `s + k/m`. -/
theorem exists_root_sub_valuation_le [Nontrivial F]
    (U Z : Multiset F) (hUZ : U.map v = Z.map v) {k : ℚ}
    (hcong : ∀ i < U.card, ∃ T ≤ U.map v, T.card = U.card - i ∧
      T.sum + (k : WithTop ℚ) ≤
        v ((((U.map fun y => X - C y).prod) - ((Z.map fun y => X - C y).prod)).coeff i))
    {u : F} (hu : u ∈ U) {s : ℚ} (hs : v u = (s : WithTop ℚ)) :
    ∃ z ∈ Z, v z = (s : WithTop ℚ) ∧
      ((s + k / ((U.map v).count ((s : WithTop ℚ)) : ℚ) : ℚ) : WithTop ℚ) ≤ v (u - z) := by
  classical
  set W : Multiset (WithTop ℚ) := U.map v with hW
  set n : ℕ := U.card with hn
  have hsW : ((s : WithTop ℚ)) ∈ W := hs ▸ Multiset.mem_map_of_mem v hu
  -- notation for the two polynomials
  set R : F[X] := (U.map fun y => X - C y).prod with hR
  set Q : F[X] := (Z.map fun y => X - C y).prod with hQ
  have hcardZ : Z.card = n := by
    have h := congrArg Multiset.card hUZ
    rw [Multiset.card_map, Multiset.card_map, ← hn] at h
    exact h.symm
  -- `R` and `Q` are monic of degree `n`
  have hRmonic : R.Monic :=
    monic_multiset_prod_of_monic U (fun y => X - C y) fun y _ => monic_X_sub_C y
  have hQmonic : Q.Monic :=
    monic_multiset_prod_of_monic Z (fun y => X - C y) fun y _ => monic_X_sub_C y
  have hRdeg : R.natDegree = n := by
    rw [hR, natDegree_multiset_prod_X_sub_C_eq_card, hn]
  have hQdeg : Q.natDegree = n := by
    rw [hQ, natDegree_multiset_prod_X_sub_C_eq_card, hcardZ]
  -- evaluate: `R(u) = 0`, so `v (Q(u)) = v ((R - Q)(u))`
  have hReval : R.eval u = 0 := by
    rw [hR, eval_multiset_prod, Multiset.map_map]
    refine Multiset.prod_eq_zero ?_
    refine Multiset.mem_map.mpr ⟨u, hu, ?_⟩
    simp
  have hQReval : v (Q.eval u) = v ((R - Q).eval u) := by
    rw [eval_sub, hReval, zero_sub, v.map_neg]
  -- the truncated-sum lower bound `V_s + k ≤ v (Q(u))`
  have hVs : (Z.map fun z => min ((s : WithTop ℚ)) (v z)).sum + (k : WithTop ℚ)
      ≤ v (Q.eval u) := by
    rw [hQReval]
    by_cases hD : R - Q = 0
    · rw [hD, eval_zero, v.map_zero]; exact le_top
    · -- degree control: `R - Q` has `natDegree < n`
      have hdeglt : (R - Q).natDegree < n := by
        have hdeg : R.degree = Q.degree := by
          rw [Polynomial.degree_eq_natDegree hRmonic.ne_zero,
            Polynomial.degree_eq_natDegree hQmonic.ne_zero, hRdeg, hQdeg]
        have hlt : (R - Q).degree < R.degree :=
          degree_sub_lt_left hdeg hRmonic.ne_zero
            (by rw [hRmonic.leadingCoeff, hQmonic.leadingCoeff])
        refine (Polynomial.natDegree_lt_iff_degree_lt hD).mpr ?_
        rwa [Polynomial.degree_eq_natDegree hRmonic.ne_zero, hRdeg] at hlt
      rw [Polynomial.eval_eq_sum_range' hdeglt u]
      refine v.map_le_sum fun i hi => ?_
      rw [Finset.mem_range] at hi
      obtain ⟨T, hT, hTcard, hTbound⟩ := hcong i hi
      have hWTcard : W.card = n := by rw [hW, Multiset.card_map, hn]
      have hVsle : (Z.map fun z => min ((s : WithTop ℚ)) (v z)).sum
          ≤ T.sum + i • ((s : WithTop ℚ)) := by
        have h := sum_map_min_le_add (W := W) (T := T) hT s
        rw [hWTcard, hTcard, Nat.sub_sub_self hi.le] at h
        rw [hUZ, Multiset.map_map] at h
        simpa [Function.comp] using h
      calc (Z.map fun z => min ((s : WithTop ℚ)) (v z)).sum + (k : WithTop ℚ)
          ≤ (T.sum + i • ((s : WithTop ℚ))) + (k : WithTop ℚ) := add_le_add hVsle le_rfl
        _ = (T.sum + (k : WithTop ℚ)) + i • ((s : WithTop ℚ)) := by
            rw [add_right_comm]
        _ ≤ v ((R - Q).coeff i) + i • ((s : WithTop ℚ)) := add_le_add hTbound le_rfl
        _ = v ((R - Q).coeff i) + v (u ^ i) := by rw [v.map_pow, hs]
        _ = v ((R - Q).coeff i * u ^ i) := (v.map_mul _ _).symm
  -- delegate to the approximate-root lemma
  have hsZ : ((s : WithTop ℚ)) ∈ Z.map v := by rw [← hUZ]; exact hsW
  have hcount : W.count ((s : WithTop ℚ)) = (Z.map v).count ((s : WithTop ℚ)) := by
    rw [hUZ]
  obtain ⟨z, hzZ, hzval, hzle⟩ :=
    exists_root_sub_valuation_le_of_le_v_eval v Z hs hsZ hVs
  refine ⟨z, hzZ, hzval, ?_⟩
  rw [hcount]
  exact hzle

/-! ### Rootwise perturbation of split polynomials -/

/-- The valuation of a perturbed root dominates the original's:
if `v δ ≥ v u + κ` with `κ ≥ 0`, then `v (u + δ) ≥ v u`. -/
private theorem le_v_add_of_le_shift {u δ : F} {κ : ℚ} (hκ : 0 ≤ κ)
    (hδ : v u + (κ : WithTop ℚ) ≤ v δ) : v u ≤ v (u + δ) := by
  refine v.map_le_add le_rfl (le_trans ?_ hδ)
  calc v u = v u + (0 : WithTop ℚ) := (add_zero _).symm
    _ ≤ v u + (κ : WithTop ℚ) := by
        exact add_le_add le_rfl (by exact_mod_cast hκ)

/-- **Rootwise perturbation**: move each root `u` of a
split polynomial by a perturbation `δ` with `v δ ≥ v u + κ` (`κ ≥ 0`).  Then every
coefficient of the difference of the two split polynomials carries the `σ`-floor of
the *unperturbed* valuation multiset plus the full margin `κ`, delivered by a
minimal-sum witness `T` of size `card − i`.

This is the single transport engine of the recentering iteration: it converts a
matched root family (per-pair shadow distance `≥ v + κ`) into the coefficientwise
congruence consumed by the polygon-congruence and root-matching lemmas, and
it bounds the shadow-recentering defect (perturbations `δ_r = S(y_r) - S(ŷ) -
S(y_r - ŷ)` with `κ = 1`). -/
theorem coeff_prod_sub_prod_eq_zero_of_card_le [Nontrivial F] (E : Multiset (F × F)) {i : ℕ}
    (hi : E.card ≤ i) :
    ((E.map fun e : F × F => X - C (e.1 + e.2)).prod
      - (E.map fun e : F × F => X - C e.1).prod).coeff i = 0 := by
  classical
  have hm₁ : ((E.map fun e : F × F => X - C (e.1 + e.2)).prod).Monic :=
    monic_multiset_prod_of_monic _ _ fun e _ => monic_X_sub_C _
  have hm₂ : ((E.map fun e : F × F => X - C e.1).prod).Monic :=
    monic_multiset_prod_of_monic _ _ fun e _ => monic_X_sub_C _
  have hcomp₁ : E.map (fun e : F × F => X - C (e.1 + e.2))
      = (E.map fun e : F × F => e.1 + e.2).map (fun a => X - C a) := by
    rw [Multiset.map_map]
    rfl
  have hcomp₂ : E.map (fun e : F × F => X - C e.1)
      = (E.map Prod.fst).map (fun a => X - C a) := by
    rw [Multiset.map_map]
    rfl
  have hd₁ : ((E.map fun e : F × F => X - C (e.1 + e.2)).prod).natDegree = E.card := by
    rw [hcomp₁, Polynomial.natDegree_multiset_prod_X_sub_C_eq_card, Multiset.card_map]
  have hd₂ : ((E.map fun e : F × F => X - C e.1).prod).natDegree = E.card := by
    rw [hcomp₂, Polynomial.natDegree_multiset_prod_X_sub_C_eq_card, Multiset.card_map]
  rw [coeff_sub]
  rcases eq_or_lt_of_le hi with rfl | hlt
  · rw [← hd₁, hm₁.coeff_natDegree, hd₁, ← hd₂, hm₂.coeff_natDegree, sub_self]
  · rw [coeff_eq_zero_of_natDegree_lt (by rw [hd₁]; exact hlt),
      coeff_eq_zero_of_natDegree_lt (by rw [hd₂]; exact hlt), sub_self]

theorem exists_sum_add_le_v_coeff_prod_sub_prod [Nontrivial F] (E : Multiset (F × F)) {κ : ℚ}
    (hκ : 0 ≤ κ) (hδ : ∀ e ∈ E, v e.1 + (κ : WithTop ℚ) ≤ v e.2) (i : ℕ) :
    ∃ T ≤ E.map (fun e : F × F => v e.1), T.card = E.card - i ∧
      (∀ T' ≤ E.map (fun e : F × F => v e.1), T'.card = E.card - i → T.sum ≤ T'.sum) ∧
      T.sum + (κ : WithTop ℚ)
        ≤ v (((E.map fun e : F × F => X - C (e.1 + e.2)).prod
              - (E.map fun e : F × F => X - C e.1).prod).coeff i) := by
  classical
  induction E using Multiset.induction_on generalizing i with
  | empty =>
    refine ⟨0, le_rfl, by simp, fun T' hT' hT'c => ?_, ?_⟩
    · simp only [Multiset.card_zero, Nat.zero_sub] at hT'c
      rw [Multiset.card_eq_zero.mp hT'c]
    · simp only [Multiset.map_zero, Multiset.prod_zero, sub_self, coeff_zero, v.map_zero]
      exact le_top
  | cons e E ih =>
    obtain ⟨u, δ⟩ := e
    have hδ₀ : v u + (κ : WithTop ℚ) ≤ v δ := hδ (u, δ) (Multiset.mem_cons_self _ _)
    have hδE : ∀ e ∈ E, v e.1 + (κ : WithTop ℚ) ≤ v e.2 :=
      fun e he => hδ e (Multiset.mem_cons_of_mem he)
    -- the minimal witness for the enlarged multiset
    obtain ⟨T, hTle, hTcard, hTmin⟩ := exists_min_sum_powersetCard
      ((((u, δ) ::ₘ E)).map fun e : F × F => v e.1)
      (j := ((u, δ) ::ₘ E).card - i)
      (by rw [Multiset.card_map]; exact Nat.sub_le _ _)
    refine ⟨T, hTle, hTcard, hTmin, ?_⟩
    -- degenerate range: the difference vanishes at and above the common degree
    by_cases htop : ((u, δ) ::ₘ E).card ≤ i
    · rw [coeff_prod_sub_prod_eq_zero_of_card_le _ htop, v.map_zero]
      exact le_top
    push Not at htop
    have hiE : i ≤ E.card := by
      rw [Multiset.card_cons] at htop
      omega
    -- product splitting: new difference = (X - C (u+δ)) · D - C δ · P
    set P : Polynomial F := (E.map fun e : F × F => X - C e.1).prod with hP
    set Pt : Polynomial F := (E.map fun e : F × F => X - C (e.1 + e.2)).prod with hPt
    set D : Polynomial F := Pt - P with hD
    have hsplit : (((u, δ) ::ₘ E).map fun e : F × F => X - C (e.1 + e.2)).prod
        - (((u, δ) ::ₘ E).map fun e : F × F => X - C e.1).prod
        = (X - C (u + δ)) * D - C δ * P := by
      rw [Multiset.map_cons, Multiset.map_cons, Multiset.prod_cons, Multiset.prod_cons,
        hD, C_add]
      ring
    rw [hsplit]
    -- coefficient decomposition
    have hcoeff : ((X - C (u + δ)) * D - C δ * P).coeff i
        = (X * D).coeff i - (u + δ) * D.coeff i - δ * P.coeff i := by
      rw [coeff_sub, sub_mul, coeff_sub, coeff_C_mul, coeff_C_mul]
    rw [hcoeff]
    -- the enlarged minimal witness is bounded by `v u` plus any size-correct witness
    have hσ_head : ∀ {S : Multiset (WithTop ℚ)}, S ≤ E.map (fun e : F × F => v e.1) →
        S.card = E.card - i → T.sum ≤ v u + S.sum := by
      intro S hS hScard
      have hle : (v u ::ₘ S) ≤ ((u, δ) ::ₘ E).map (fun e : F × F => v e.1) := by
        rw [Multiset.map_cons]
        exact Multiset.cons_le_cons _ hS
      have hcard : (v u ::ₘ S).card = ((u, δ) ::ₘ E).card - i := by
        rw [Multiset.card_cons, hScard, Multiset.card_cons]
        omega
      calc T.sum ≤ (v u ::ₘ S).sum := hTmin _ hle hcard
        _ = v u + S.sum := Multiset.sum_cons _ _
    -- (a) the X·D term
    have hbound_a : T.sum + (κ : WithTop ℚ) ≤ v ((X * D).coeff i) := by
      rcases Nat.eq_zero_or_pos i with rfl | hipos
      · rw [Polynomial.coeff_X_mul_zero, v.map_zero]
        exact le_top
      · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
        rw [Polynomial.coeff_X_mul]
        obtain ⟨T₁, hT₁le, hT₁card, hT₁min, hT₁⟩ := ih hδE i'
        have hT₁' : T.sum ≤ T₁.sum := by
          refine hTmin T₁ (le_trans hT₁le ?_) ?_
          · rw [Multiset.map_cons]
            exact Multiset.le_cons_self _ _
          · rw [hT₁card, Multiset.card_cons]
            omega
        exact le_trans (add_le_add hT₁' le_rfl) hT₁
    -- (b) the (u+δ)·D term
    have hbound_b : T.sum + (κ : WithTop ℚ) ≤ v ((u + δ) * D.coeff i) := by
      obtain ⟨T₂, hT₂le, hT₂card, hT₂min, hT₂⟩ := ih hδE i
      rw [v.map_mul]
      calc T.sum + (κ : WithTop ℚ) ≤ (v u + T₂.sum) + (κ : WithTop ℚ) :=
            add_le_add (hσ_head hT₂le hT₂card) le_rfl
        _ = v u + (T₂.sum + (κ : WithTop ℚ)) := by rw [add_assoc]
        _ ≤ v (u + δ) + v (D.coeff i) :=
            add_le_add (le_v_add_of_le_shift v hκ hδ₀) hT₂
    -- (c) the δ·P term
    have hbound_c : T.sum + (κ : WithTop ℚ) ≤ v (δ * P.coeff i) := by
      obtain ⟨T₃, hT₃le, hT₃card, hT₃min, hT₃⟩ :=
        exists_sum_le_v_coeff_prod_X_sub_C v (E.map Prod.fst) (i := i)
          (by rw [Multiset.card_map]; exact hiE)
      rw [v.map_mul]
      have hmapeq : (E.map Prod.fst).map v = E.map (fun e : F × F => v e.1) := by
        rw [Multiset.map_map]
        rfl
      have hPeq : ((E.map Prod.fst).map fun y => X - C y).prod = P := by
        rw [hP, Multiset.map_map]
        rfl
      rw [Multiset.card_map] at hT₃card
      rw [hmapeq] at hT₃le
      rw [hPeq] at hT₃
      calc T.sum + (κ : WithTop ℚ) ≤ (v u + T₃.sum) + (κ : WithTop ℚ) :=
            add_le_add (hσ_head hT₃le hT₃card) le_rfl
        _ = (v u + (κ : WithTop ℚ)) + T₃.sum := add_right_comm _ _ _
        _ ≤ v δ + v (P.coeff i) := add_le_add hδ₀ hT₃
    -- combine
    refine le_trans (le_min (le_min hbound_a hbound_b) hbound_c) ?_
    calc min (min (v ((X * D).coeff i)) (v ((u + δ) * D.coeff i))) (v (δ * P.coeff i))
        ≤ min (v ((X * D).coeff i - (u + δ) * D.coeff i)) (v (δ * P.coeff i)) :=
          min_le_min (v.map_sub _ _) le_rfl
      _ ≤ v ((X * D).coeff i - (u + δ) * D.coeff i - δ * P.coeff i) := v.map_sub _ _

end TrustworthyKedlaya
