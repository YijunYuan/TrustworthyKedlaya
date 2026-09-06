/-
Copyright (c) 2026 Shanwen Wang, Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import TrustworthyKedlaya.NewtonSlope
public import Mathlib.Topology.Algebra.Valued.NormedValued

/-!
# `𝕃_p` as a complete valued field

The valuation `val p : 𝕃_[p] → WithTop ℚ` (the minimum of the support of the canonical
Teichmüller expansion) makes `𝕃_[p]` a valued field, hence a normed field with the norm
`‖x‖ = p^(-val p x)`.  This file installs these structures and proves that `𝕃_[p]` is
**complete**: a Cauchy sequence stabilises coefficientwise, the stabilised coefficient
function has well-ordered support (a subset of `ℚ` all of whose initial segments are
well-ordered is well-ordered), and the series it defines is the limit.

## Main declarations

- `TrustworthyKedlaya.pAdicHahnSeries.coeff_add_eq_of_lt_val`: adding a series of valuation
  `> q` does not change the coefficients at positions `≤ q`;
- `TrustworthyKedlaya.pAdicHahnSeries.lt_val_sub_of_forall_coeff_eq`: two series with the
  same coefficients at all positions `≤ q` differ by a series of valuation `> q`;
- `TrustworthyKedlaya.pAdicHahnSeries.rankOne`: the valuation of `𝕃_[p]` has rank one;
- `TrustworthyKedlaya.pAdicHahnSeries.normedField`: the normed-field structure on `𝕃_[p]`,
  with `norm_eq_of_ne_zero : ‖x‖ = p^(-val p x)`;
- `TrustworthyKedlaya.pAdicHahnSeries.completeSpace`: `𝕃_[p]` is complete.
-/

@[expose] public section

namespace TrustworthyKedlaya.pAdicHahnSeries

open WittVector Filter Topology

open scoped NNReal

variable {p : ℕ} [hp : Fact (Nat.Prime p)]

/-! ### Coefficientwise additivity below a dominated position

`coeff_add_of_le_val` (Wang-Yuan, Lemma 2.2(4)) is additivity at a position at or below
both valuations.  The following variant only asks that the second summand vanish below the
position and that the coefficients of the sum agree with those of the first summand there:
the defect of the canonical representatives is then a null series vanishing strictly below
the position, whose coefficient at the position is a unit unless additivity holds. -/

/-- Additivity of the coefficient maps at a position `q`, given that `y` vanishes strictly
below `q` and that `x + y` and `x` have the same coefficients strictly below `q`. -/
theorem coeff_add_of_forall_lt {x y : 𝕃_[p]} {q : ℚ}
    (hy : ∀ r < q, y.coeff r = 0) (hxy : ∀ r < q, (x + y).coeff r = x.coeff r) :
    (x + y).coeff q = x.coeff q + y.coeff q := by
  by_contra hne
  set fx : LiftedPAdicHahnSeries p :=
    LiftedPAdicHahnSeries.fromCoeff x.coeff (support_IsPWO x) with hfx_def
  set fy : LiftedPAdicHahnSeries p :=
    LiftedPAdicHahnSeries.fromCoeff y.coeff (support_IsPWO y) with hfy_def
  set fz : LiftedPAdicHahnSeries p :=
    LiftedPAdicHahnSeries.fromCoeff (x + y).coeff (support_IsPWO (x + y)) with hfz_def
  -- `Δ = fx + fy - fz` is a null series: its class in `𝕃_[p]` is `x + y - (x + y) = 0`
  have hΔ : fx + fy - fz ∈ NullSeriesIdeal p := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_add]
    have h1 : Ideal.Quotient.mk (NullSeriesIdeal p) fx = x := fromCoeff_of_coeff_eq_self x
    have h2 : Ideal.Quotient.mk (NullSeriesIdeal p) fy = y := fromCoeff_of_coeff_eq_self y
    have h3 : Ideal.Quotient.mk (NullSeriesIdeal p) fz = x + y :=
      fromCoeff_of_coeff_eq_self (x + y)
    rw [h1, h2, h3, sub_self]
  -- `Δ` vanishes strictly below `q`
  have hbelow : ∀ q' < q, (fx + fy - fz).coeff q' = 0 := by
    intro q' hq'
    rw [HahnSeries.coeff_sub, HahnSeries.coeff_add]
    change teichmuller p (x.coeff q') + teichmuller p (y.coeff q')
        - teichmuller p ((x + y).coeff q') = 0
    rw [hy q' hq', hxy q' hq', WittVector.teichmuller_zero]
    simp
  -- if additivity failed at `q`, the coefficient of `Δ` there would be a unit
  have hq_unit : IsUnit ((fx + fy - fz).coeff q) := by
    apply WittVector.isUnit_of_coeff_zero_ne_zero
    intro h0
    apply hne
    have hcoeff : (fx + fy - fz).coeff q
        = teichmuller p (x.coeff q) + teichmuller p (y.coeff q)
          - teichmuller p ((x + y).coeff q) := by
      rw [HahnSeries.coeff_sub, HahnSeries.coeff_add]; rfl
    rw [hcoeff, ← WittVector.constantCoeff_apply, map_sub, map_add,
      WittVector.constantCoeff_apply, WittVector.constantCoeff_apply,
      WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero,
      WittVector.teichmuller_coeff_zero, WittVector.teichmuller_coeff_zero] at h0
    exact (sub_eq_zero.mp h0).symm
  exact null_series_no_unit_leading hΔ hq_unit hbelow

/-- **Dominated positions are stable**: adding a series of valuation `> q` does not change
the coefficient at position `q` (hence at any position `≤ q`). -/
theorem coeff_add_eq_of_lt_val {x z : 𝕃_[p]} {q : ℚ} (hz : (q : WithTop ℚ) < val p z) :
    (x + z).coeff q = x.coeff q := by
  by_contra hne
  -- the positions below `val z` where the coefficients of `x + z` and `x` differ
  set D : Set ℚ := {r | (r : WithTop ℚ) < val p z ∧ (x + z).coeff r ≠ x.coeff r} with hD
  have hD_sub : D ⊆ x.support ∪ (x + z).support := by
    intro r hr
    by_contra hmem
    simp only [Set.mem_union, mem_support_iff, not_or, not_not] at hmem
    exact hr.2 (hmem.2.trans hmem.1.symm)
  have hD_pwo : D.IsPWO := ((support_IsPWO x).union (support_IsPWO (x + z))).mono hD_sub
  have hD_ne : D.Nonempty := ⟨q, hz, hne⟩
  -- its least element `r₀`: below `r₀` the coefficients agree and `z` vanishes
  set r₀ : ℚ := hD_pwo.isWF.min hD_ne with hr₀
  have hr₀_mem : r₀ ∈ D := hD_pwo.isWF.min_mem hD_ne
  have hz_below : ∀ r < r₀, z.coeff r = 0 := fun r hr =>
    coeff_eq_zero_of_lt_val ((WithTop.coe_lt_coe.mpr hr).trans hr₀_mem.1)
  have hxz_below : ∀ r < r₀, (x + z).coeff r = x.coeff r := by
    intro r hr
    by_contra h
    exact hD_pwo.isWF.not_lt_min hD_ne
      (show r ∈ D from ⟨(WithTop.coe_lt_coe.mpr hr).trans hr₀_mem.1, h⟩) hr
  -- so additivity holds at `r₀`, where `z` has coefficient `0`: contradiction
  have hkey := coeff_add_of_forall_lt hz_below hxz_below
  rw [coeff_eq_zero_of_lt_val hr₀_mem.1, add_zero] at hkey
  exact hr₀_mem.2 hkey

/-- Adding a series of valuation `> q` does not change the coefficients at any position
`≤ q`. -/
theorem coeff_add_eq_of_le_of_lt_val {x z : 𝕃_[p]} {q r : ℚ} (hr : r ≤ q)
    (hz : (q : WithTop ℚ) < val p z) : (x + z).coeff r = x.coeff r :=
  coeff_add_eq_of_lt_val ((WithTop.coe_le_coe.mpr hr).trans_lt hz)

/-- **Coefficient agreement bounds the valuation of the difference**: if `x` and `y` have
the same coefficients at all positions `≤ q`, then `val p (x - y) > q`. -/
theorem lt_val_sub_of_forall_coeff_eq {x y : 𝕃_[p]} {q : ℚ}
    (h : ∀ r ≤ q, x.coeff r = y.coeff r) : (q : WithTop ℚ) < val p (x - y) := by
  by_contra hle
  push Not at hle
  have hne : x - y ≠ 0 := by
    intro h0
    rw [h0, val_zero_eq_top] at hle
    exact absurd hle (not_le.mpr (WithTop.coe_lt_top q))
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp fun h => hne (val_eq_top_iff.mp h)
  have hmq : m ≤ q := WithTop.coe_le_coe.mp (hm ▸ hle)
  have hd : (x - y).coeff m ≠ 0 := coeff_val_ne_zero hm.symm
  have hd_below : ∀ r < m, (x - y).coeff r = 0 := fun r hr =>
    coeff_eq_zero_of_lt_val (hm ▸ WithTop.coe_lt_coe.mpr hr)
  have hxy : y + (x - y) = x := by ring
  have hx_below : ∀ r < m, (y + (x - y)).coeff r = y.coeff r := fun r hr =>
    coeff_add_eq_of_lt_val (hm ▸ WithTop.coe_lt_coe.mpr hr)
  have hkey := coeff_add_of_forall_lt hd_below hx_below
  rw [hxy, h m hmq] at hkey
  exact hd (add_left_cancel (hkey.symm.trans (add_zero _).symm))

/-! ### The valued field structure -/

/-- The valued-field structure on `𝕃_[p]` (installed in `PAdicHahnSeries.lean` as
`Valued.mk' (val p)`) has `Valued.v x = val p x`, viewed multiplicatively. -/
theorem valued_v_apply (x : 𝕃_[p]) :
    (Valued.v x : Multiplicative (WithTop ℚ)ᵒᵈ)
      = Multiplicative.ofAdd (OrderDual.toDual (val p x)) := rfl

theorem valued_v_lt_iff {x y : 𝕃_[p]} :
    (Valued.v x : Multiplicative (WithTop ℚ)ᵒᵈ) < Valued.v y ↔ val p y < val p x := by
  rw [valued_v_apply, valued_v_apply, Multiplicative.ofAdd_lt]
  exact OrderDual.toDual_lt_toDual

theorem valued_v_le_iff {x y : 𝕃_[p]} :
    (Valued.v x : Multiplicative (WithTop ℚ)ᵒᵈ) ≤ Valued.v y ↔ val p y ≤ val p x := by
  rw [valued_v_apply, valued_v_apply, Multiplicative.ofAdd_le]
  exact OrderDual.toDual_le_toDual

theorem valued_v_eq_zero_iff {x : 𝕃_[p]} :
    (Valued.v x : Multiplicative (WithTop ℚ)ᵒᵈ) = 0 ↔ x = 0 :=
  (Valued.v).zero_iff

theorem valued_v_eq_one_iff {x : 𝕃_[p]} :
    (Valued.v x : Multiplicative (WithTop ℚ)ᵒᵈ) = 1 ↔ val p x = 0 := by
  rw [valued_v_apply]
  constructor
  · intro h
    have h' := congrArg (fun g : Multiplicative (WithTop ℚ)ᵒᵈ =>
      OrderDual.ofDual (Multiplicative.toAdd g)) h
    simpa using h'
  · intro h
    rw [h]
    rfl

/-! ### The norm `p^(-val)` -/

/-- The map `t ↦ p^(-t)` on `WithTop ℚ`, sending `⊤` to `0`. -/
noncomputable def expNNReal (p : ℕ) : WithTop ℚ → ℝ≥0
  | ⊤ => 0
  | (q : ℚ) => (p : ℝ≥0) ^ (-(q : ℝ))

omit hp in
@[simp]
theorem expNNReal_top : expNNReal p ⊤ = 0 := rfl

omit hp in
@[simp]
theorem expNNReal_coe (q : ℚ) : expNNReal p (q : WithTop ℚ) = (p : ℝ≥0) ^ (-(q : ℝ)) := rfl

theorem one_lt_p_nnreal : (1 : ℝ≥0) < (p : ℝ≥0) := by
  exact_mod_cast (Fact.out : Nat.Prime p).one_lt

omit hp in
theorem expNNReal_zero : expNNReal p 0 = 1 := by
  rw [show (0 : WithTop ℚ) = ((0 : ℚ) : WithTop ℚ) from rfl, expNNReal_coe]
  simp

theorem expNNReal_add (a b : WithTop ℚ) :
    expNNReal p (a + b) = expNNReal p a * expNNReal p b := by
  cases a with
  | top => simp
  | coe qa =>
    cases b with
    | top => simp
    | coe qb =>
      rw [← WithTop.coe_add, expNNReal_coe, expNNReal_coe, expNNReal_coe,
        ← NNReal.rpow_add (ne_zero_of_lt one_lt_p_nnreal)]
      congr 1
      push_cast
      ring

theorem expNNReal_strictAnti : StrictAnti (expNNReal p) := by
  intro a b hab
  cases b with
  | top =>
    cases a with
    | top => exact absurd hab (lt_irrefl _)
    | coe qa =>
      rw [expNNReal_top, expNNReal_coe]
      exact NNReal.rpow_pos (lt_trans zero_lt_one one_lt_p_nnreal)
  | coe qb =>
    cases a with
    | top => exact absurd hab (not_lt.mpr le_top)
    | coe qa =>
      rw [expNNReal_coe, expNNReal_coe]
      refine NNReal.rpow_lt_rpow_of_exponent_lt one_lt_p_nnreal ?_
      have : qa < qb := WithTop.coe_lt_coe.mp hab
      have : (qa : ℝ) < qb := by exact_mod_cast this
      linarith

theorem expNNReal_eq_zero_iff {a : WithTop ℚ} : expNNReal p a = 0 ↔ a = ⊤ := by
  cases a with
  | top => simp
  | coe q =>
    simp only [expNNReal_coe, WithTop.coe_ne_top, iff_false]
    exact (NNReal.rpow_pos (lt_trans zero_lt_one one_lt_p_nnreal)).ne'

/-- The norm homomorphism `Multiplicative (WithTop ℚ)ᵒᵈ →*₀ ℝ≥0`, `t ↦ p^(-t)`. -/
noncomputable def normHom (p : ℕ) [Fact (Nat.Prime p)] :
    Multiplicative (WithTop ℚ)ᵒᵈ →*₀ ℝ≥0 where
  toFun g := expNNReal p (OrderDual.ofDual (Multiplicative.toAdd g))
  map_zero' := expNNReal_top
  map_one' := expNNReal_zero
  map_mul' _ _ := expNNReal_add _ _

theorem normHom_apply (g : Multiplicative (WithTop ℚ)ᵒᵈ) :
    normHom p g = expNNReal p (OrderDual.ofDual (Multiplicative.toAdd g)) := rfl

theorem normHom_strictMono : StrictMono (normHom p) := by
  intro g h hgh
  rw [normHom_apply, normHom_apply]
  apply expNNReal_strictAnti
  rw [← Multiplicative.toAdd_lt] at hgh
  exact OrderDual.ofDual_lt_ofDual.mpr hgh

/-- The valuation of `𝕃_[p]` has rank one, with real embedding `t ↦ p^(-t)`. -/
noncomputable instance rankOne :
    (Valued.v : Valuation 𝕃_[p] (Multiplicative (WithTop ℚ)ᵒᵈ)).RankOne where
  hom' := (normHom p).comp MonoidWithZeroHom.ValueGroup₀.embedding
  strictMono' := normHom_strictMono.comp MonoidWithZeroHom.ValueGroup₀.embedding_strictMono
  exists_val_nontrivial := by
    refine ⟨single 1 1, ?_, ?_⟩
    · rw [ne_eq, valued_v_eq_zero_iff]
      intro h
      have := val_single (p := p) 1 one_ne_zero
      rw [h, val_zero_eq_top] at this
      exact WithTop.top_ne_coe this
    · rw [ne_eq, valued_v_eq_one_iff, val_single (p := p) 1 one_ne_zero]
      simp

/-- The normed-field structure on `𝕃_[p]` determined by its valuation: `‖x‖ = p^(-val p x)`. -/
noncomputable instance normedField : NormedField 𝕃_[p] :=
  Valued.toNormedField 𝕃_[p] (Multiplicative (WithTop ℚ)ᵒᵈ)

noncomputable instance nontriviallyNormedField : NontriviallyNormedField 𝕃_[p] :=
  Valued.toNontriviallyNormedField 𝕃_[p] (Multiplicative (WithTop ℚ)ᵒᵈ)

theorem norm_eq (x : 𝕃_[p]) : ‖x‖ = (expNNReal p (val p x) : ℝ) := by
  rw [Valued.toNormedField.norm_def]
  change ((normHom p) (MonoidWithZeroHom.ValueGroup₀.embedding (Valued.v.restrict x)) : ℝ) = _
  rw [Valuation.embedding_restrict]
  rfl

theorem norm_eq_of_ne_zero {x : 𝕃_[p]} (hx : x ≠ 0) :
    ‖x‖ = (p : ℝ) ^ (-(valQ x : ℝ)) := by
  rw [norm_eq, ← coe_valQ hx, expNNReal_coe, NNReal.coe_rpow, NNReal.coe_natCast]

theorem norm_lt_iff_lt_val {x : 𝕃_[p]} {q : ℚ} :
    ‖x‖ < (p : ℝ) ^ (-(q : ℝ)) ↔ (q : WithTop ℚ) < val p x := by
  rw [norm_eq, show (p : ℝ) ^ (-(q : ℝ)) = ((expNNReal p (q : WithTop ℚ) : ℝ≥0) : ℝ) by
    rw [expNNReal_coe, NNReal.coe_rpow, NNReal.coe_natCast], NNReal.coe_lt_coe]
  exact StrictAnti.lt_iff_gt expNNReal_strictAnti

theorem norm_le_iff_le_val {x : 𝕃_[p]} {q : ℚ} :
    ‖x‖ ≤ (p : ℝ) ^ (-(q : ℝ)) ↔ (q : WithTop ℚ) ≤ val p x := by
  rw [norm_eq, show (p : ℝ) ^ (-(q : ℝ)) = ((expNNReal p (q : WithTop ℚ) : ℝ≥0) : ℝ) by
    rw [expNNReal_coe, NNReal.coe_rpow, NNReal.coe_natCast], NNReal.coe_le_coe]
  exact StrictAnti.le_iff_ge expNNReal_strictAnti

theorem norm_le_one_iff_le_val {x : 𝕃_[p]} : ‖x‖ ≤ 1 ↔ (0 : WithTop ℚ) ≤ val p x := by
  have h := norm_le_iff_le_val (x := x) (q := 0)
  simpa using h

/-! ### Completeness -/

/-- A Cauchy sequence in `𝕃_[p]` has differences of arbitrarily large valuation. -/
theorem exists_forall_lt_val_sub_of_cauchySeq {u : ℕ → 𝕃_[p]} (hu : CauchySeq u) (q : ℚ) :
    ∃ N : ℕ, ∀ m, N ≤ m → ∀ n, N ≤ n → (q : WithTop ℚ) < val p (u m - u n) := by
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hu ((p : ℝ) ^ (-(q : ℝ)))
    (Real.rpow_pos_of_pos (by exact_mod_cast (Fact.out : Nat.Prime p).pos) _)
  refine ⟨N, fun m hm n hn => norm_lt_iff_lt_val.mp ?_⟩
  rw [← dist_eq_norm]
  exact hN m hm n hn

/-- Every Cauchy sequence in `𝕃_[p]` converges: its coefficients stabilise position by
position, the stabilised coefficient function has well-ordered support, and the series it
defines is the limit. -/
theorem exists_tendsto_of_cauchySeq (u : ℕ → 𝕃_[p]) (hu : CauchySeq u) :
    ∃ x : 𝕃_[p], Tendsto u atTop (𝓝 x) := by
  classical
  choose N hN using fun q : ℚ => exists_forall_lt_val_sub_of_cauchySeq hu q
  -- stabilisation: beyond stage `N q`, the coefficients at positions `≤ q` are frozen
  have hstab : ∀ q : ℚ, ∀ m, N q ≤ m → ∀ r, r ≤ q → (u m).coeff r = (u (N r)).coeff r := by
    intro q m hm r hr
    have h1 : (u m).coeff r = (u (max m (N r))).coeff r := by
      have hv : (q : WithTop ℚ) < val p (u (max m (N r)) - u m) :=
        hN q _ (hm.trans (le_max_left _ _)) m hm
      have := coeff_add_eq_of_le_of_lt_val (x := u m) hr hv
      rw [add_sub_cancel] at this
      exact this.symm
    have h2 : (u (max m (N r))).coeff r = (u (N r)).coeff r := by
      have hv : (r : WithTop ℚ) < val p (u (max m (N r)) - u (N r)) :=
        hN r _ (le_max_right _ _) _ le_rfl
      have := coeff_add_eq_of_lt_val (x := u (N r)) hv
      rwa [add_sub_cancel] at this
    exact h1.trans h2
  -- the stabilised coefficient function
  set s : ℚ → Fpbar p := fun r => (u (N r)).coeff r with hs_def
  -- its support is well-ordered: every initial segment is contained in the support of a
  -- single term of the sequence
  have hs : (Function.support s).IsPWO := by
    refine Set.IsWF.isPWO ?_
    rw [Set.isWF_iff_no_descending_seq]
    intro f hf hmem
    have hsub : ∀ n, f n ∈ (u (N (f 0))).support := by
      intro n
      rw [mem_support_iff, hstab (f 0) (N (f 0)) le_rfl (f n) (hf.antitone (Nat.zero_le n))]
      exact hmem n
    exact (Set.isWF_iff_no_descending_seq.mp (support_IsPWO (u (N (f 0)))).isWF) f hf hsub
  refine ⟨fromCoeff s hs, ?_⟩
  have hcoeff : (fromCoeff s hs).coeff = s := coeff_of_fromCoeff_eq_self s hs
  -- beyond stage `N q`, the limit and the sequence agree at all positions `≤ q`
  have hval : ∀ q : ℚ, ∀ m, N q ≤ m → (q : WithTop ℚ) < val p (fromCoeff s hs - u m) := by
    intro q m hm
    refine lt_val_sub_of_forall_coeff_eq fun r hr => ?_
    rw [hcoeff, hstab q m hm r hr]
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : Nat.Prime p).one_lt
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt ε⁻¹ hp1
  refine ⟨N k, fun n hn => ?_⟩
  rw [dist_eq_norm, ← norm_neg, neg_sub]
  calc ‖fromCoeff s hs - u n‖ < (p : ℝ) ^ (-((k : ℚ) : ℝ)) :=
        norm_lt_iff_lt_val.mpr (hval k n hn)
    _ = ((p : ℝ) ^ k)⁻¹ := by
        rw [Real.rpow_neg (by positivity), Rat.cast_natCast, Real.rpow_natCast]
    _ < ε := by
        rw [inv_lt_comm₀ (by positivity) hε]
        exact hk

/-- **`𝕃_[p]` is complete.** -/
instance completeSpace : CompleteSpace 𝕃_[p] :=
  Metric.complete_of_cauchySeq_tendsto exists_tendsto_of_cauchySeq

end TrustworthyKedlaya.pAdicHahnSeries
