/-
Copyright (c) 2026 Shanwen Wang, Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import TrustworthyKedlaya.LevelCalculus
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# The slice-span decomposition of a uniformly periodic series

The slice-span decomposition writes a UP series
`x` presented on `S_{a,b,c}` as a finite sum `∑ λ_i x_i` with `λ_i` supported in
`(1/a)·ℤ_{≥ -b}` and `x_i` supported in `(1/a)(T_c ∪ {0})` with slice witness
`(a, 0, c, M, N)`.

The engine is the *span step* `exists_finite_slice_span`: the width-`a` slice
functions `f_m` (`m ≥ -b`), all `(M, N)`-periodic at level `c`, span a
finite-dimensional space of functions on the level set — because a periodic
function's values on the level set are pinned by its values at the finitely many
expansions confined to the digit box `Finset.range ((c+1)(M+N))`
(`exists_confined_rep_forall`, whose confined representative is
function-independent).  Hence finitely many slices `f_{m_1}, …, f_{m_r}` suffice to
express every `f_m` on the level set as an `𝔽̄_p`-linear combination with
point-independent coefficients `K m i`.

The decomposition `SliceWitness.exists_slice_span` then takes `x_i` to be the
restriction of the shift `t^{-m_i/a}·x` to the fractional window
`(1/a)(T_c ∪ {0})` — whose index-`0` slice samples `f_{m_i}` at every twist
evaluation point (`sliceWitness_hahnRestrict_single_mul`) — and `λ_i` to be the
Hahn series with coefficient `K m i` at `m/a`.  The product identity is the unique
antidiagonal decomposition of an exponent `s = (m + z)/a` into the integer part
`m = ⌈a s⌉` and the fractional part `z ∈ (-1, 0]` (`Sabc_mem_ceil_decomp`).

The level set here always contains `0 = -fracVal 0`, so no separate treatment of
the exponent `0` is needed.

## References

- K. S. Kedlaya, *The algebraic closure of the power series field in positive
  characteristic*, Proc. Amer. Math. Soc. 129 (2001) [Ked01a], proof of Theorem 8.
-/

@[expose] public section

namespace TrustworthyKedlaya.UP

variable {p : ℕ} [hp : Fact (Nat.Prime p)]

/-- Pointwise finite sums of `(M, N)`-periodic functions at level `c` are
`(M, N)`-periodic at level `c` (twist sequences are computed by evaluation, so they
are termwise additive). -/
theorem isTwistPeriodic_finset_sum {ι : Type*} (s : Finset ι) {F : ι → ℚ → 𝔽ᵃ_[p]}
    {c : ℕ} {M N : ℕ+} (hF : ∀ i ∈ s, IsTwistPeriodic p (F i) c M N) :
    IsTwistPeriodic p (fun z => ∑ i ∈ s, F i z) c M N := by
  intro j dig hj hd hs n hn
  have hsum : ∀ n', twistSeq p (fun z => ∑ i ∈ s, F i z) j dig n'
      = ∑ i ∈ s, twistSeq p (F i) j dig n' := fun n' => rfl
  rw [hsum, hsum]
  exact Finset.sum_congr rfl fun i hi => hF i hi j dig hj hd hs n hn

/-- Two `(M, N)`-periodic functions at level `c` agreeing at all expansions confined
to the digit box `Finset.range ((c+1)(M+N))` agree at every canonical expansion of
digit sum `≤ c`: the confined representative of `exists_confined_rep_forall` is the
same for both functions. -/
theorem IsTwistPeriodic.eq_on_levelSet_of_eq_on_confined {f g : ℚ → 𝔽ᵃ_[p]} {c : ℕ}
    {M N : ℕ+} (hf : IsTwistPeriodic p f c M N) (hg : IsTwistPeriodic p g c M N)
    (hfg : ∀ e' : ℕ →₀ ℕ, (∀ i, e' i < p) →
      e'.support ⊆ Finset.range ((c + 1) * ((M : ℕ) + N)) →
      f (-fracVal p e') = g (-fracVal p e'))
    {e : ℕ →₀ ℕ} (he : ∀ i, e i < p) (hsum : (e.sum fun _ v => v) ≤ c) :
    f (-fracVal p e) = g (-fracVal p e) := by
  obtain ⟨e', he', hsum', hbox, hval⟩ := exists_confined_rep_forall c M N he hsum
  rw [← hval f hf, ← hval g hg]
  exact hfg e' he' hbox

/-- **Finite spanning family for the slices** (the span step): given a family of
`(M, N)`-periodic functions at level `c` indexed by the
integers `m ≥ -b`, finitely many members `F (ms 1), …, F (ms r)` with `ms i ≥ -b`
span the family on the level set: every `F m` (`m ≥ -b`) agrees at every canonical
expansion of digit sum `≤ c` (including `0`, the empty expansion) with an
`𝔽̄_p`-linear combination of them, with coefficients `K m` independent of the
expansion. -/
theorem exists_finite_slice_span {b c : ℕ} {M N : ℕ+} (F : ℤ → ℚ → 𝔽ᵃ_[p])
    (hF : ∀ m : ℤ, -(b : ℤ) ≤ m → IsTwistPeriodic p (F m) c M N) :
    ∃ (r : ℕ) (ms : Fin r → ℤ) (K : ℤ → Fin r → 𝔽ᵃ_[p]),
      (∀ i, -(b : ℤ) ≤ ms i) ∧
      ∀ m : ℤ, -(b : ℤ) ≤ m → ∀ e : ℕ →₀ ℕ, (∀ i, e i < p) →
        (e.sum fun _ v => v) ≤ c →
        F m (-fracVal p e) = ∑ i, K m i * F (ms i) (-fracVal p e) := by
  classical
  have hConfFin := finite_neg_fracVal_confined p ((c + 1) * ((M : ℕ) + N))
  set Conf : Finset ℚ := hConfFin.toFinset with hConf
  -- The evaluation of each slice at the confined points.
  set Φ : ℤ → (↥Conf → 𝔽ᵃ_[p]) := fun m z => F m (z : ℚ) with hΦ
  set D : Set ℤ := {m : ℤ | -(b : ℤ) ≤ m} with hD
  -- The span of the evaluations is finitely generated (the ambient space is a
  -- finite-dimensional function space), hence spanned by finitely many members
  -- of the family.
  have hVfg : (Submodule.span (𝔽ᵃ_[p]) (Φ '' D)).FG :=
    Module.Finite.iff_fg.mp inferInstance
  obtain ⟨S, hSspan⟩ := hVfg
  have hSsub : ∀ v ∈ S, ∃ Tv : Finset (↥Conf → 𝔽ᵃ_[p]), ↑Tv ⊆ Φ '' D ∧
      v ∈ Submodule.span (𝔽ᵃ_[p]) (Tv : Set (↥Conf → 𝔽ᵃ_[p])) := by
    intro v hv
    exact Submodule.mem_span_finite_of_mem_span (hSspan ▸ Submodule.subset_span hv)
  choose Tv hTvsub hTvmem using hSsub
  set T : Finset (↥Conf → 𝔽ᵃ_[p]) := S.attach.biUnion (fun v => Tv v.1 v.2) with hT
  have hTsub : ↑T ⊆ Φ '' D := by
    intro t ht
    obtain ⟨v, _, hvt⟩ := Finset.mem_biUnion.mp ht
    exact hTvsub v.1 v.2 hvt
  have hTspan : Submodule.span (𝔽ᵃ_[p]) (Φ '' D)
      ≤ Submodule.span (𝔽ᵃ_[p]) (T : Set (↥Conf → 𝔽ᵃ_[p])) := by
    rw [← hSspan, Submodule.span_le]
    intro v hv
    have hsub : (Tv v hv : Set (↥Conf → 𝔽ᵃ_[p])) ⊆ (T : Set (↥Conf → 𝔽ᵃ_[p])) := by
      intro t ht
      exact Finset.mem_coe.mpr
        (Finset.mem_biUnion.mpr ⟨⟨v, hv⟩, S.mem_attach _, Finset.mem_coe.mp ht⟩)
    exact Submodule.span_mono hsub (hTvmem v hv)
  -- Choose index preimages for the finitely many spanning evaluations.
  have hTpre : ∀ t ∈ T, ∃ m : ℤ, -(b : ℤ) ≤ m ∧ Φ m = t := by
    intro t ht
    obtain ⟨m, hm, hmt⟩ := hTsub ht
    exact ⟨m, hm, hmt⟩
  choose pre hpreD hpreEq using hTpre
  -- Every `Φ m` is a combination of the chosen evaluations.
  have hTsubrange : (T : Set (↥Conf → 𝔽ᵃ_[p]))
      ⊆ Set.range fun i : Fin T.card =>
        Φ (pre (T.equivFin.symm i).1 (T.equivFin.symm i).2) := by
    intro t ht
    refine ⟨T.equivFin ⟨t, ht⟩, ?_⟩
    have h1 : T.equivFin.symm (T.equivFin ⟨t, ht⟩) = ⟨t, ht⟩ := Equiv.symm_apply_apply _ _
    change Φ (pre (T.equivFin.symm (T.equivFin ⟨t, ht⟩)).1
      (T.equivFin.symm (T.equivFin ⟨t, ht⟩)).2) = t
    rw [h1]
    exact hpreEq t ht
  have hrep : ∀ m : ℤ, -(b : ℤ) ≤ m → ∃ K : Fin T.card → 𝔽ᵃ_[p],
      ∑ i, K i • Φ (pre (T.equivFin.symm i).1 (T.equivFin.symm i).2) = Φ m := by
    intro m hm
    refine (Submodule.mem_span_range_iff_exists_fun (𝔽ᵃ_[p])).mp ?_
    exact Submodule.span_mono hTsubrange (hTspan (Submodule.subset_span ⟨m, hm, rfl⟩))
  refine ⟨T.card, fun i => pre (T.equivFin.symm i).1 (T.equivFin.symm i).2,
    fun m => if hm : -(b : ℤ) ≤ m then (hrep m hm).choose else 0,
    fun i => hpreD _ _, ?_⟩
  intro m hm e he hsum
  simp only [dif_pos hm]
  have hKm := (hrep m hm).choose_spec
  -- Compare `F m` with the combination: they agree at the confined points, hence
  -- on the whole level set.
  refine (hF m hm).eq_on_levelSet_of_eq_on_confined
    (isTwistPeriodic_finset_sum Finset.univ fun i _ =>
      (hF _ (hpreD (T.equivFin.symm i).1 (T.equivFin.symm i).2)).comp
        fun v => (hrep m hm).choose i * v)
    (fun e' he' hbox => ?_) he hsum
  have hz : -fracVal p e' ∈ Conf := by
    rw [hConf]
    exact hConfFin.mem_toFinset.mpr ⟨e', he', hbox, rfl⟩
  have hev := congrFun hKm ⟨-fracVal p e', hz⟩
  simp only [hΦ, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hev
  exact hev.symm

/-! ### From the span step to the decomposition -/

/-- The set `(1/a)·ℤ_{≥ -b}` of shifted integer exponents is partially
well-ordered. -/
theorem isPWO_intCastGE_div (a : ℕ+) (b : ℕ) :
    {q : ℚ | ∃ m : ℤ, -(b : ℤ) ≤ m ∧ q = (m : ℚ) / (a : ℚ)}.IsPWO := by
  have ha : (0 : ℚ) < (a : ℚ) := by exact_mod_cast a.pos
  have hmono : Monotone fun q : ℚ => q / (a : ℚ) := fun x y hxy => by
    simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_right hxy (inv_nonneg.mpr ha.le)
  refine ((isPWO_intCastGE b).image_of_monotone hmono).mono ?_
  rintro q ⟨m, hm, rfl⟩
  exact ⟨(m : ℚ), ⟨m, hm, rfl⟩, rfl⟩

/-- The fractional window `(1/a)(T_c ∪ {0})` lies inside the support set
`S_{a,0,c}`. -/
theorem Tc_union_zero_div_subset_Sabc (a : ℕ+) (c : ℕ) :
    (· / (a : ℚ)) '' (Tc p c ∪ {0}) ⊆ Sabc p a 0 c := by
  rintro q ⟨z, hz, rfl⟩
  rcases hz with hz | hz
  · obtain ⟨e, he, hesum, rfl⟩ := Tc_subset_neg_fracVal p c hz
    refine ⟨0, e, by norm_num, he, hesum, ?_⟩
    rw [fracVal_def]
    ring
  · rw [Set.mem_singleton_iff.mp hz]
    exact ⟨0, 0, by norm_num, fun i => hp.out.pos, by simp, by simp⟩

/-- The `⌈·⌉`-decomposition of a point of `S_{a,b,c}`: `a·s` has integer part
`⌈a s⌉ ≥ -b` and fractional part `a·s - ⌈a s⌉` in the window `T_c ∪ {0}`. -/
theorem Sabc_mem_ceil_decomp {a : ℕ+} {b c : ℕ} {s : ℚ} (hs : s ∈ Sabc p a b c) :
    -(b : ℤ) ≤ ⌈(a : ℚ) * s⌉ ∧ (a : ℚ) * s - (⌈(a : ℚ) * s⌉ : ℚ) ∈ Tc p c ∪ {0} := by
  obtain ⟨n, d, hn, hd, hsum, rfl⟩ := hs
  have ha : ((a : ℕ) : ℚ) ≠ 0 := by exact_mod_cast a.pos.ne'
  rw [fracVal_def]
  have hval : (a : ℚ) * (1 / (a : ℚ) * ((n : ℚ) - fracVal p d))
      = (n : ℚ) - fracVal p d := by
    field_simp
  rw [hval]
  have hceil : ⌈(n : ℚ) - fracVal p d⌉ = n := by
    rw [Int.ceil_eq_iff]
    constructor
    · have := fracVal_lt_one p hp.out.one_lt hd
      linarith
    · have := fracVal_nonneg p d
      linarith
  rw [hceil]
  refine ⟨hn, ?_⟩
  have harg : (n : ℚ) - fracVal p d - (n : ℚ) = -fracVal p d := by ring
  rw [harg]
  rcases eq_or_ne (fracVal p d) 0 with h0 | h0
  · rw [h0, neg_zero]
    exact Set.mem_union_right _ rfl
  · refine Set.mem_union_left _ ⟨⟨0, d, by norm_num, hd, hsum, ?_⟩, ?_, ?_⟩
    · rw [fracVal_def]
      push_cast
      ring
    · have := fracVal_lt_one p hp.out.one_lt hd
      linarith
    · have h1 := fracVal_nonneg p d
      have h2 : 0 < fracVal p d := lt_of_le_of_ne h1 (Ne.symm h0)
      linarith

/-- The restriction to the fractional window `(1/a)(T_c ∪ {0})` of the shift
`t^{-m₀/a}·x` of a series with `(M, N)`-periodic slices carries the slice witness
`(a, 0, c, M, N)`: the index-`0` slice samples the `m₀`-slice of `x` at every twist
evaluation point of level `≤ c`, and the positive-index slices vanish at all of
them. -/
theorem sliceWitness_hahnRestrict_single_mul {x : HahnSeries ℚ (𝔽ᵃ_[p])} {a : ℕ+}
    {b c : ℕ} {M N : ℕ+}
    (hper : ∀ m : ℤ, -(b : ℤ) ≤ m →
      IsTwistPeriodic p (fun z => x.coeff (((m : ℚ) + z) / (a : ℚ))) c M N)
    {m₀ : ℤ} (hm₀ : -(b : ℤ) ≤ m₀) :
    SliceWitness p (hahnRestrict ((· / (a : ℚ)) '' (Tc p c ∪ {0}))
      (HahnSeries.single (-(m₀ : ℚ) / (a : ℚ)) 1 * x)) a 0 c M N := by
  constructor
  · exact (support_hahnRestrict_subset_set _ _).trans (Tc_union_zero_div_subset_Sabc a c)
  intro m hm
  have hm' : (0 : ℤ) ≤ m := by simpa using hm
  intro j dig hj hdig hsum n hn
  rcases eq_or_ne dig 0 with rfl | hdig0
  · simp [twistSeq]
  obtain ⟨i₁, hi₁⟩ : ∃ i₁, dig i₁ ≠ 0 := by
    by_contra h
    push Not at h
    exact hdig0 (Finsupp.ext h)
  have hsumpos : 0 < dig.sum fun _ v => v :=
    lt_of_lt_of_le (Nat.pos_of_ne_zero hi₁)
      (Finset.single_le_sum (f := fun i => dig i) (fun _ _ => Nat.zero_le _)
        (Finsupp.mem_support_iff.mpr hi₁))
  have hgd0 : ∀ n' : ℕ, gapDig j n' dig ≠ 0 := by
    intro n' h0
    have hs' := gapDig_sum j n' dig
    rw [h0, Finsupp.sum_zero_index] at hs'
    omega
  have hlt : ∀ n' : ℕ, fracVal p (gapDig j n' dig) < 1 := fun n' =>
    fracVal_lt_one p hp.out.one_lt (gapDig_lt p hdig hp.out.pos j n')
  simp only [twistSeq_eq_neg_fracVal_gapDig]
  rcases hm'.eq_or_lt with rfl | hmpos
  · -- Index `0`: the twist points land in the window, where the restriction samples
    -- the `m₀`-slice of `x`.
    have hmem : ∀ n' : ℕ, (((0 : ℤ) : ℚ) + -fracVal p (gapDig j n' dig)) / (a : ℚ)
        ∈ (· / (a : ℚ)) '' (Tc p c ∪ {0}) := by
      intro n'
      rw [div_mem_image_div_iff]
      have h0 : ((0 : ℤ) : ℚ) + -fracVal p (gapDig j n' dig)
          = -fracVal p (gapDig j n' dig) := by push_cast; ring
      rw [h0]
      exact Set.mem_union_left _ (neg_fracVal_mem_Tc (gapDig_lt p hdig hp.out.pos j n')
        (by rw [gapDig_sum]; exact hsum) (hgd0 n'))
    rw [coeff_hahnRestrict_of_mem _ (hmem _), coeff_hahnRestrict_of_mem _ (hmem _),
      HahnSeries.coeff_single_mul, HahnSeries.coeff_single_mul, one_mul, one_mul]
    have harg : ∀ w : ℚ, (((0 : ℤ) : ℚ) + w) / (a : ℚ) - -(m₀ : ℚ) / (a : ℚ)
        = ((m₀ : ℚ) + w) / (a : ℚ) := by
      intro w
      push_cast
      ring
    rw [harg, harg]
    have hx := hper m₀ hm₀ j dig hj hdig hsum n hn
    simpa only [twistSeq_eq_neg_fracVal_gapDig] using hx
  · -- Positive index: the twist points have positive numerator, outside the window.
    have hmem : ∀ n' : ℕ, ((m : ℚ) + -fracVal p (gapDig j n' dig)) / (a : ℚ)
        ∉ (· / (a : ℚ)) '' (Tc p c ∪ {0}) := by
      intro n' hmem'
      rw [div_mem_image_div_iff] at hmem'
      have hm1 : (1 : ℚ) ≤ (m : ℚ) := by exact_mod_cast (by omega : (1 : ℤ) ≤ m)
      have hpos : (0 : ℚ) < (m : ℚ) + -fracVal p (gapDig j n' dig) := by
        have := hlt n'
        linarith
      rcases hmem' with hT | h0
      · linarith [hT.2.2]
      · rw [Set.mem_singleton_iff] at h0
        rw [h0] at hpos
        exact lt_irrefl _ hpos
    rw [coeff_hahnRestrict_of_notMem _ (hmem _), coeff_hahnRestrict_of_notMem _ (hmem _)]

/-- **Slice-span decomposition**: a series with slice
witness `(a, b, c, M, N)` is a finite sum `x = ∑ i, λ i * xs i` where each `λ i` is
supported in `(1/a)·ℤ_{≥ -b}` and each `xs i` is supported in the fractional window
`(1/a)(T_c ∪ {0})` and carries the slice witness `(a, 0, c, M, N)`. -/
theorem SliceWitness.exists_slice_span {x : HahnSeries ℚ (𝔽ᵃ_[p])} {a : ℕ+}
    {b c : ℕ} {M N : ℕ+} (hx : SliceWitness p x a b c M N) :
    ∃ (r : ℕ) (lam xs : Fin r → HahnSeries ℚ (𝔽ᵃ_[p])),
      (∀ i, ∀ q ∈ (lam i).support, ∃ m : ℤ, -(b : ℤ) ≤ m ∧ q = (m : ℚ) / (a : ℚ)) ∧
      (∀ i, (xs i).support ⊆ (· / (a : ℚ)) '' (Tc p c ∪ {0})) ∧
      (∀ i, SliceWitness p (xs i) a 0 c M N) ∧
      x = ∑ i, lam i * xs i := by
  classical
  obtain ⟨hsupp, hper⟩ := hx
  have ha : ((a : ℕ) : ℚ) ≠ 0 := by exact_mod_cast a.pos.ne'
  obtain ⟨r, ms, K, hms, hspan⟩ := exists_finite_slice_span
    (fun m z => x.coeff (((m : ℚ) + z) / (a : ℚ))) hper
  -- The `λ` series: coefficient `K m i` at the exponent `m/a`, `m ≥ -b`.
  set lamCoeff : Fin r → ℚ → 𝔽ᵃ_[p] := fun i q =>
    if (⌈(a : ℚ) * q⌉ : ℚ) = (a : ℚ) * q ∧ -(b : ℤ) ≤ ⌈(a : ℚ) * q⌉
    then K ⌈(a : ℚ) * q⌉ i else 0 with hlamCoeff
  have hlamCoeff_supp : ∀ (i : Fin r) (q : ℚ), lamCoeff i q ≠ 0 →
      ∃ m : ℤ, -(b : ℤ) ≤ m ∧ q = (m : ℚ) / (a : ℚ) := by
    intro i q hq
    by_cases hcond : (⌈(a : ℚ) * q⌉ : ℚ) = (a : ℚ) * q ∧ -(b : ℤ) ≤ ⌈(a : ℚ) * q⌉
    · refine ⟨⌈(a : ℚ) * q⌉, hcond.2, ?_⟩
      rw [eq_div_iff ha, mul_comm]
      exact hcond.1.symm
    · exact absurd (by simp only [hlamCoeff]; exact if_neg hcond) hq
  have hlam_isPWO : ∀ i : Fin r, (Function.support (lamCoeff i)).IsPWO := fun i =>
    (isPWO_intCastGE_div a b).mono fun q hq => hlamCoeff_supp i q hq
  set lam : Fin r → HahnSeries ℚ (𝔽ᵃ_[p]) := fun i => ⟨lamCoeff i, hlam_isPWO i⟩
    with hlam
  have hlam_coeff : ∀ (i : Fin r) (m : ℤ),
      (lam i).coeff ((m : ℚ) / (a : ℚ)) = if -(b : ℤ) ≤ m then K m i else 0 := by
    intro i m
    have harg : (a : ℚ) * ((m : ℚ) / (a : ℚ)) = ((m : ℤ) : ℚ) := by field_simp
    change lamCoeff i ((m : ℚ) / (a : ℚ)) = _
    simp only [hlamCoeff, harg, Int.ceil_intCast]
    by_cases hm : -(b : ℤ) ≤ m
    · rw [if_pos ⟨trivial, hm⟩, if_pos hm]
    · rw [if_neg fun hc => hm hc.2, if_neg hm]
  -- The `xs` series: window restrictions of the shifts of `x` by the spanning
  -- slice indices.
  set xs : Fin r → HahnSeries ℚ (𝔽ᵃ_[p]) := fun i =>
    hahnRestrict ((· / (a : ℚ)) '' (Tc p c ∪ {0}))
      (HahnSeries.single (-(ms i : ℚ) / (a : ℚ)) 1 * x) with hxs
  have hxs_mem : ∀ (i : Fin r) {w : ℚ}, w ∈ Tc p c ∪ {0} →
      (xs i).coeff (w / (a : ℚ)) = x.coeff (((ms i : ℚ) + w) / (a : ℚ)) := by
    intro i w hw
    simp only [hxs]
    rw [coeff_hahnRestrict_of_mem _ (div_mem_image_div_iff.mpr hw),
      HahnSeries.coeff_single_mul, one_mul]
    congr 1
    ring
  have hxs_notMem : ∀ (i : Fin r) {w : ℚ}, w ∉ Tc p c ∪ {0} →
      (xs i).coeff (w / (a : ℚ)) = 0 := by
    intro i w hw
    simp only [hxs]
    exact coeff_hahnRestrict_of_notMem _ fun hmem => hw (div_mem_image_div_iff.mp hmem)
  refine ⟨r, lam, xs, fun i q hq => hlamCoeff_supp i q hq,
    fun i => support_hahnRestrict_subset_set _ _,
    fun i => sliceWitness_hahnRestrict_single_mul hper (hms i), ?_⟩
  -- The product identity, coefficient by coefficient.
  ext s
  rw [HahnSeries.coeff_sum]
  set m : ℤ := ⌈(a : ℚ) * s⌉ with hm
  set z : ℚ := (a : ℚ) * s - (m : ℚ) with hz
  have hz_le : z ≤ 0 := by
    rw [hz, hm]
    exact sub_nonpos.mpr (Int.le_ceil _)
  have hz_gt : -1 < z := by
    rw [hz, hm]
    have := Int.ceil_lt_add_one ((a : ℚ) * s)
    linarith
  have hs_eq : s = ((m : ℚ) + z) / (a : ℚ) := by
    rw [hz]
    field_simp
    ring
  -- In each product only the pair `(m/a, z/a)` can contribute.
  have hterm : ∀ i : Fin r,
      (lam i * xs i).coeff s
        = (lam i).coeff ((m : ℚ) / (a : ℚ)) * (xs i).coeff (z / (a : ℚ)) := by
    intro i
    rw [HahnSeries.coeff_mul]
    have hsub : Finset.antidiagonal (lam i).isPWO_support (xs i).isPWO_support s
        ⊆ {((m : ℚ) / (a : ℚ), z / (a : ℚ))} := by
      rintro ⟨q₁, q₂⟩ hq
      simp only [Finset.mem_antidiagonal] at hq
      obtain ⟨h₁, h₂, h₁₂⟩ := hq
      obtain ⟨m', hm', rfl⟩ := hlamCoeff_supp i q₁ h₁
      obtain ⟨w, hw, rfl⟩ := support_hahnRestrict_subset_set _ _ h₂
      have hw_le : w ≤ 0 := by
        rcases hw with hw | hw
        · exact hw.2.2.le
        · exact (Set.mem_singleton_iff.mp hw).le
      have hw_gt : -1 < w := by
        rcases hw with hw | hw
        · exact hw.2.1
        · rw [Set.mem_singleton_iff.mp hw]; norm_num
      have hsum' : (m' : ℚ) + w = (m : ℚ) + z := by
        have h1 : ((m' : ℚ) + w) / (a : ℚ) = ((m : ℚ) + z) / (a : ℚ) := by
          rw [add_div, h₁₂, hs_eq]
        have h2 := congrArg (· * (a : ℚ)) h1
        simpa [div_mul_cancel₀ _ ha] using h2
      have hmm' : m' = m := by
        have hcast : ((m' - m : ℤ) : ℚ) = z - w := by push_cast; linarith
        have h1 : (-1 : ℚ) < ((m' - m : ℤ) : ℚ) := by rw [hcast]; linarith
        have h2 : ((m' - m : ℤ) : ℚ) < 1 := by rw [hcast]; linarith
        have h1' : (-1 : ℤ) < m' - m := by exact_mod_cast h1
        have h2' : m' - m < 1 := by exact_mod_cast h2
        omega
      subst hmm'
      have hww : w = z := by linarith
      subst hww
      exact Finset.mem_singleton_self _
    rcases Finset.subset_singleton_iff.mp hsub with hemp | hsing
    · rw [hemp, Finset.sum_empty]
      by_contra hne
      have hprod : (lam i).coeff ((m : ℚ) / (a : ℚ)) * (xs i).coeff (z / (a : ℚ)) ≠ 0 :=
        fun h => hne h.symm
      obtain ⟨h1, h2⟩ := mul_ne_zero_iff.mp hprod
      have hpair : (((m : ℚ) / (a : ℚ), z / (a : ℚ)) : ℚ × ℚ)
          ∈ Finset.antidiagonal (lam i).isPWO_support (xs i).isPWO_support s := by
        simp only [Finset.mem_antidiagonal]
        exact ⟨h1, h2, by rw [← add_div, ← hs_eq]⟩
      rw [hemp] at hpair
      exact absurd hpair (Finset.notMem_empty _)
    · rw [hsing, Finset.sum_singleton]
  simp only [hterm]
  by_cases hmb : -(b : ℤ) ≤ m
  · by_cases hzT : z ∈ Tc p c ∪ {0}
    · -- Both parts in range: the span identity gives the coefficient.
      obtain ⟨e, he, hesum, hze⟩ :
          ∃ e : ℕ →₀ ℕ, (∀ k, e k < p) ∧ (e.sum fun _ v => v) ≤ c ∧
            z = -fracVal p e := by
        rcases hzT with hzT | hz0
        · exact Tc_subset_neg_fracVal p c hzT
        · exact ⟨0, fun k => hp.out.pos, by simp, by
            rw [Set.mem_singleton_iff.mp hz0, fracVal_zero, neg_zero]⟩
      have hlc : ∀ i : Fin r, (lam i).coeff ((m : ℚ) / (a : ℚ)) = K m i := fun i => by
        rw [hlam_coeff i m, if_pos hmb]
      have hxc : ∀ i : Fin r, (xs i).coeff (z / (a : ℚ))
          = x.coeff (((ms i : ℚ) + z) / (a : ℚ)) := fun i => hxs_mem i hzT
      simp only [hlc, hxc]
      rw [hs_eq]
      have hkey := hspan m hmb e he hesum
      rw [← hze] at hkey
      exact hkey
    · -- Fractional part outside the window: both sides vanish.
      have hxc0 : ∀ i : Fin r, (xs i).coeff (z / (a : ℚ)) = 0 := fun i =>
        hxs_notMem i hzT
      simp only [hxc0, mul_zero, Finset.sum_const_zero]
      by_contra hne
      obtain ⟨-, hfrac⟩ := Sabc_mem_ceil_decomp (hsupp hne)
      rw [← hm, ← hz] at hfrac
      exact hzT hfrac
  · -- Integer part below `-b`: both sides vanish.
    have hlc0 : ∀ i : Fin r, (lam i).coeff ((m : ℚ) / (a : ℚ)) = 0 := fun i => by
      rw [hlam_coeff i m, if_neg hmb]
    simp only [hlc0, zero_mul, Finset.sum_const_zero]
    by_contra hne
    obtain ⟨hint, -⟩ := Sabc_mem_ceil_decomp (hsupp hne)
    rw [← hm] at hint
    exact hmb hint

end TrustworthyKedlaya.UP
