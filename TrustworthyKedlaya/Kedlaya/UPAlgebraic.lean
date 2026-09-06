/-
Copyright (c) 2026 Shanwen Wang, Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import TrustworthyKedlaya.Kedlaya.SliceSpan
public import TrustworthyKedlaya.Kedlaya.FractionalLaurent

/-!
# Uniformly periodic series are algebraic

The converse half of Kedlaya's Theorem 15: every uniformly periodic Hahn series
in `𝔽̄_p((t^ℚ))` is integral — in particular algebraic — over the Laurent field
`𝔽̄_p((t))`.

The proof is a strong induction on the digit-sum level `c`
(`isIntegral_of_sliceWitness`).  A series with slice witness `(a, b, c, M, N)`
splits as `∑ λ_i x_i` by the slice-span decomposition
(`SliceWitness.exists_slice_span`), with the `λ_i` integral by the
fractional-Laurent lemma; each `x_i`, slice-supported on `T_c ∪ {0}`, splits off
its constant term, and the remaining `T_c`-part `x'` undergoes the Artin-Schreier
level drop `y = x'^{1/p^L} - x'`: the level-`≤ c-1` part of `y` is integral by
induction, the remainder `w` decomposes by first digits into monomial multiples of
series at levels `c - β ≤ c - 1`, integral by induction, and finally `x'` is a
root of `Z^{p^L} - Z + y^{p^L}` (`isIntegral_of_pow_eq_sub`), hence integral by
transitivity.

## References

- K. S. Kedlaya, *The algebraic closure of the power series field in positive
  characteristic*, Proc. Amer. Math. Soc. 129 (2001) [Ked01a], proof of Theorem 8.
- K. S. Kedlaya, *On the algebraicity of generalized power series*, Beiträge
  Algebra Geom. 58 (2017) [Ked17], Sections 1-2.
-/

@[expose] public section

namespace TrustworthyKedlaya.UP

open LaurentSeries

variable {p : ℕ} [hp : Fact (Nat.Prime p)]

/-- Every monomial of `𝔽̄_p((t^ℚ))` is integral over the Laurent field: its support
is the single rational point `q = q.num / q.den`. -/
theorem isIntegral_single (q : ℚ) (v : 𝔽ᵃ_[p]) :
    IsIntegral ((𝔽ᵃ_[p])⸨X⸩) (HahnSeries.single q v : HahnSeries ℚ (𝔽ᵃ_[p])) := by
  refine isIntegral_hahn_of_support_int_div ⟨q.den, q.den_pos⟩ fun s hs => ?_
  have hs' : s = q := HahnSeries.support_single_subset hs
  refine ⟨q.num, ?_⟩
  rw [hs']
  exact_mod_cast (Rat.num_div_den q).symm

/-- A root of the Artin-Schreier-type relation `x^n = x - t` with `t` integral and
`n ≥ 2` is integral: `x` satisfies the monic polynomial `X^n - X + t` over the
integral closure, and integrality is transitive. -/
theorem isIntegral_of_pow_eq_sub {R T : Type*} [CommRing R] [CommRing T] [Nontrivial T]
    [Algebra R T] {t x : T} (ht : IsIntegral R t) {n : ℕ} (hn : 1 < n)
    (hx : x ^ n = x - t) : IsIntegral R x := by
  have : Nontrivial (integralClosure R T) :=
    ⟨⟨0, 1, fun h => zero_ne_one (α := T) (congrArg Subtype.val h)⟩⟩
  refine isIntegral_trans (A := integralClosure R T) x
    ⟨Polynomial.X ^ n + (-Polynomial.X + Polynomial.C ⟨t, ht⟩), ?_, ?_⟩
  · refine (Polynomial.monic_X_pow n).add_of_left ?_
    rw [Polynomial.degree_X_pow]
    refine lt_of_le_of_lt (Polynomial.degree_add_le _ _) (max_lt ?_ ?_)
    · rw [Polynomial.degree_neg, Polynomial.degree_X]
      exact_mod_cast hn
    · refine lt_of_le_of_lt Polynomial.degree_C_le ?_
      exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn.le
  · simp only [Polynomial.eval₂_add, Polynomial.eval₂_neg, Polynomial.eval₂_X_pow,
      Polynomial.eval₂_X, Polynomial.eval₂_C, hx]
    have hcoe : algebraMap (integralClosure R T) T ⟨t, ht⟩ = t := rfl
    rw [hcoe]
    ring

/-- **Window form to `SliceWitness`**: a series slice-supported on `T_c ∪ {0}` whose
width-`a` slice is `(M, N)`-periodic at level `c` carries the slice witness
`(a, 0, c, M, N)` — the slices of positive index vanish at every twist evaluation
point. -/
theorem sliceWitness_of_window_form {x : HahnSeries ℚ (𝔽ᵃ_[p])} {a : ℕ+} {c : ℕ}
    {M N : ℕ+}
    (hsupp : ∀ q : ℚ, x.coeff (q / (a : ℚ)) ≠ 0 → q ∈ Tc p c ∪ {0})
    (hper : IsTwistPeriodic p (fun z => x.coeff (z / (a : ℚ))) c M N) :
    SliceWitness p x a 0 c M N := by
  have ha : ((a : ℕ) : ℚ) ≠ 0 := by exact_mod_cast a.pos.ne'
  constructor
  · intro s hs
    have hq : x.coeff (((a : ℚ) * s) / (a : ℚ)) ≠ 0 := by
      rw [mul_div_cancel_left₀ s ha]
      exact hs
    rcases hsupp _ hq with hTc | h0
    · obtain ⟨⟨n, e, hn, he, hsum, heq⟩, -⟩ := hTc
      refine ⟨n, e, hn, he, hsum, ?_⟩
      have h1 : ((1 : ℕ+) : ℚ) = 1 := by norm_num
      rw [h1] at heq
      field_simp at heq ⊢
      linarith [heq]
    · have hs0 : s = 0 := by
        rcases mul_eq_zero.mp (Set.mem_singleton_iff.mp h0) with h | h
        · exact absurd h ha
        · exact h
      exact ⟨0, 0, by norm_num, fun i => hp.out.pos, by simp, by simp [hs0]⟩
  · intro m hm
    rcases (by omega : m = 0 ∨ 1 ≤ m) with rfl | hm1
    · simpa using hper
    · intro j dig hj hdig hsum' n hn
      have hzero : ∀ n',
          twistSeq p (fun z => x.coeff (((m : ℚ) + z) / (a : ℚ))) j dig n' = 0 := by
        intro n'
        rw [twistSeq_eq_neg_fracVal_gapDig]
        by_contra h0
        have hm' : (1 : ℚ) ≤ (m : ℚ) := by exact_mod_cast hm1
        have hlt := fracVal_lt_one p hp.out.one_lt (d := gapDig j n' dig)
          fun i => gapDig_lt p hdig hp.out.pos j n' i
        rcases hsupp _ h0 with hTc | hz0
        · have hneg := hTc.2.2
          linarith
        · rw [Set.mem_singleton_iff] at hz0
          have hnn := fracVal_nonneg p (gapDig j n' dig)
          linarith [hz0]
      rw [hzero, hzero]

/-- Restricting to the `T_c` part of the fractional window preserves periodicity of
the width-`a` slice: nonzero twist strings sample points of `T_c`, where the
restriction agrees with `x`, and the zero string gives constant sequences. -/
theorem isTwistPeriodic_slice_hahnRestrict_TcImage {x : HahnSeries ℚ (𝔽ᵃ_[p])}
    {a : ℕ+} {c : ℕ} {M N : ℕ+}
    (hper : IsTwistPeriodic p (fun z => x.coeff (z / (a : ℚ))) c M N) :
    IsTwistPeriodic p
      (fun z => (hahnRestrict ((· / (a : ℚ)) '' Tc p c) x).coeff (z / (a : ℚ)))
      c M N := by
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
  have hmem : ∀ n' : ℕ,
      -fracVal p (gapDig j n' dig) / (a : ℚ) ∈ (· / (a : ℚ)) '' Tc p c := by
    intro n'
    rw [div_mem_image_div_iff]
    exact neg_fracVal_mem_Tc (gapDig_lt p hdig hp.out.pos j n')
      (by rw [gapDig_sum]; exact hsum) (hgd0 n')
  simp only [twistSeq_eq_neg_fracVal_gapDig]
  rw [coeff_hahnRestrict_of_mem _ (hmem _), coeff_hahnRestrict_of_mem _ (hmem _)]
  have hx := hper j dig hj hdig hsum n hn
  simpa only [twistSeq_eq_neg_fracVal_gapDig] using hx

/-- Restricting to the exponents of `S_{a,0,c'}` preserves periodicity of the
width-`a` slice at any level `c ≥ c'`: strings of digit sum `≤ c'` sample exponents
of `S_{a,0,c'}`, where the restriction agrees with `x`, while strings of larger
digit sum sample exponents outside it (canonical strings are unique), where the
restriction vanishes. -/
theorem isTwistPeriodic_slice_hahnRestrict_Sabc {x : HahnSeries ℚ (𝔽ᵃ_[p])}
    {a : ℕ+} {c c' : ℕ} {M N : ℕ+}
    (hper : IsTwistPeriodic p (fun z => x.coeff (z / (a : ℚ))) c M N) :
    IsTwistPeriodic p
      (fun z => (hahnRestrict (Sabc p a 0 c') x).coeff (z / (a : ℚ))) c M N := by
  intro j dig hj hdig hsum n hn
  by_cases hsum' : (dig.sum fun _ v => v) ≤ c'
  · have hmem : ∀ n' : ℕ, -fracVal p (gapDig j n' dig) / (a : ℚ) ∈ Sabc p a 0 c' := by
      intro n'
      refine ⟨0, gapDig j n' dig, by norm_num,
        fun i => gapDig_lt p hdig hp.out.pos _ _ i, by rw [gapDig_sum]; exact hsum', ?_⟩
      rw [fracVal_def]
      push_cast
      ring
    simp only [twistSeq_eq_neg_fracVal_gapDig]
    rw [coeff_hahnRestrict_of_mem _ (hmem _), coeff_hahnRestrict_of_mem _ (hmem _)]
    have hx := hper j dig hj hdig hsum n hn
    simpa only [twistSeq_eq_neg_fracVal_gapDig] using hx
  · have hmem : ∀ n' : ℕ, -fracVal p (gapDig j n' dig) / (a : ℚ) ∉ Sabc p a 0 c' := by
      intro n' hmem'
      have hshape : (1 / (a : ℚ)) * (((0 : ℤ) : ℚ) - fracVal p (gapDig j n' dig))
          ∈ Sabc p a 0 c' := by
        rw [show (1 / (a : ℚ)) * (((0 : ℤ) : ℚ) - fracVal p (gapDig j n' dig))
            = -fracVal p (gapDig j n' dig) / (a : ℚ) by push_cast; ring]
        exact hmem'
      obtain ⟨-, hsum₂⟩ := Sabc_mem_canonical p
        (fun i => gapDig_lt p hdig hp.out.pos j n' i) hshape
      rw [gapDig_sum] at hsum₂
      exact hsum' hsum₂
    simp only [twistSeq_eq_neg_fracVal_gapDig]
    rw [coeff_hahnRestrict_of_notMem _ (hmem _), coeff_hahnRestrict_of_notMem _ (hmem _)]

/-- A series slice-supported on the fractional window splits off its coefficient at
`0`: `x = x₀·t^0 + x'` with `x'` the restriction to the `T_c` part. -/
theorem eq_single_add_hahnRestrict_TcImage {x : HahnSeries ℚ (𝔽ᵃ_[p])} {a : ℕ+}
    {c : ℕ} (hsupp : ∀ q : ℚ, x.coeff (q / (a : ℚ)) ≠ 0 → q ∈ Tc p c ∪ {0}) :
    x = HahnSeries.single 0 (x.coeff 0)
      + hahnRestrict ((· / (a : ℚ)) '' Tc p c) x := by
  have ha : ((a : ℕ) : ℚ) ≠ 0 := by exact_mod_cast a.pos.ne'
  have h0img : (0 : ℚ) ∉ (· / (a : ℚ)) '' Tc p c := by
    rintro ⟨z, hz, hz0⟩
    have hz' : z = 0 := by
      rcases div_eq_zero_iff.mp hz0 with h | h
      · exact h
      · exact absurd h ha
    rw [hz'] at hz
    exact absurd hz.2.2 (lt_irrefl 0)
  refine HahnSeries.ext (funext fun s => ?_)
  rw [HahnSeries.coeff_add]
  rcases eq_or_ne s 0 with rfl | hs0
  · rw [HahnSeries.coeff_single_same, coeff_hahnRestrict_of_notMem _ h0img, add_zero]
  · rw [HahnSeries.coeff_single_of_ne hs0, zero_add]
    by_cases hsx : x.coeff s = 0
    · by_cases hmem : s ∈ (· / (a : ℚ)) '' Tc p c
      · rw [coeff_hahnRestrict_of_mem _ hmem]
      · rw [coeff_hahnRestrict_of_notMem _ hmem, hsx]
    · have hq : x.coeff (((a : ℚ) * s) / (a : ℚ)) ≠ 0 := by
        rw [mul_div_cancel_left₀ s ha]
        exact hsx
      rcases hsupp _ hq with hTc | h0'
      · have hmem : s ∈ (· / (a : ℚ)) '' Tc p c :=
          ⟨(a : ℚ) * s, hTc, mul_div_cancel_left₀ s ha⟩
        rw [coeff_hahnRestrict_of_mem _ hmem]
      · rw [Set.mem_singleton_iff] at h0'
        rcases mul_eq_zero.mp h0' with h | h
        · exact absurd h ha
        · exact absurd h hs0

/-- Finite sums of integral elements are integral. -/
theorem isIntegral_finset_sum {R T ι : Type*} [CommRing R] [CommRing T] [Algebra R T]
    (s : Finset ι) {f : ι → T} (h : ∀ i ∈ s, IsIntegral R (f i)) :
    IsIntegral R (∑ i ∈ s, f i) :=
  Finset.sum_induction f _ (fun _ _ => IsIntegral.add) isIntegral_zero h

/-- A series slice-supported on the level-`0` window `T_0 ∪ {0}` is supported on the
integers, hence integral over the Laurent field: `T_0` is empty. -/
theorem isIntegral_of_window_zero {x : HahnSeries ℚ (𝔽ᵃ_[p])} {a : ℕ+}
    (hsupp : ∀ q : ℚ, x.coeff (q / (a : ℚ)) ≠ 0 → q ∈ Tc p 0 ∪ {0}) :
    IsIntegral ((𝔽ᵃ_[p])⸨X⸩) x := by
  have ha : ((a : ℕ) : ℚ) ≠ 0 := by exact_mod_cast a.pos.ne'
  refine isIntegral_hahn_of_support_int_div 1 fun s hs => ?_
  refine ⟨0, ?_⟩
  have hq : x.coeff (((a : ℚ) * s) / (a : ℚ)) ≠ 0 := by
    rw [mul_div_cancel_left₀ s ha]
    exact hs
  have hs0 : s = 0 := by
    rcases hsupp _ hq with hTc | h0
    · exfalso
      obtain ⟨e, he, hesum, heq⟩ := Tc_subset_neg_fracVal p 0 hTc
      have he0 : e = 0 := by
        ext i
        simp only [Finsupp.coe_zero, Pi.zero_apply]
        by_contra hi
        have hle := Finset.single_le_sum (f := fun i => e i) (fun _ _ => Nat.zero_le _)
          (Finsupp.mem_support_iff.mpr hi)
        rw [Finsupp.sum] at hesum
        omega
      rw [he0, fracVal_zero, neg_zero] at heq
      have hlt := hTc.2.2
      rw [heq] at hlt
      exact lt_irrefl 0 hlt
    · rcases mul_eq_zero.mp (Set.mem_singleton_iff.mp h0) with h | h
      · exact absurd h ha
      · exact h
  rw [hs0]
  norm_num

/-- **The level induction** (window form): granted
integrality at all lower levels, a series slice-supported on `T_c ∪ {0}` with
`(M, N)`-periodic width-`a` slice at level `c` is integral over the Laurent field.
The constant term splits off; the `T_c` part undergoes the Artin-Schreier level
drop, whose low-level part is handled by the induction hypothesis and whose
remainder decomposes by first digits into monomial multiples of series at strictly
lower levels. -/
private theorem isIntegral_of_window_form {c : ℕ}
    (IH : ∀ c', c' < c → ∀ (x : HahnSeries ℚ (𝔽ᵃ_[p])) (a : ℕ+) (b : ℕ) (M N : ℕ+),
      SliceWitness p x a b c' M N → IsIntegral ((𝔽ᵃ_[p])⸨X⸩) x)
    {x : HahnSeries ℚ (𝔽ᵃ_[p])} {a : ℕ+} {M N : ℕ+}
    (hsupp : ∀ q : ℚ, x.coeff (q / (a : ℚ)) ≠ 0 → q ∈ Tc p c ∪ {0})
    (hper : IsTwistPeriodic p (fun z => x.coeff (z / (a : ℚ))) c M N) :
    IsIntegral ((𝔽ᵃ_[p])⸨X⸩) x := by
  rcases c with - | c'
  · exact isIntegral_of_window_zero hsupp
  -- Split off the constant term; `x'` is the `T_{c'+1}` part.
  set x' : HahnSeries ℚ (𝔽ᵃ_[p]) := hahnRestrict ((· / (a : ℚ)) '' Tc p (c' + 1)) x
    with hx'
  have hsplit := eq_single_add_hahnRestrict_TcImage hsupp
  have hsupp' : ∀ q : ℚ, x'.coeff (q / (a : ℚ)) ≠ 0 → q ∈ Tc p (c' + 1) := fun q hq =>
    div_mem_image_div_iff.mp (support_hahnRestrict_subset_set _ _ hq)
  have hper' : IsTwistPeriodic p (fun z => x'.coeff (z / (a : ℚ))) (c' + 1) M N :=
    isTwistPeriodic_slice_hahnRestrict_TcImage hper
  -- All slice values lie in a single finite subfield `𝔽_{p^d}`.
  obtain ⟨d, hd0, hdval⟩ := hper'.exists_uniform_subfield
  have hval : ∀ z ∈ Tc p (c' + 1),
      x'.coeff (z / (a : ℚ)) ^ p ^ d = x'.coeff (z / (a : ℚ)) := by
    intro z hz
    obtain ⟨e, he, hesum, rfl⟩ := Tc_subset_neg_fracVal p (c' + 1) hz
    exact hdval e he hesum
  -- The common multiple `L` of the period and the subfield degree.
  set L : ℕ := (N : ℕ) * d with hL
  have hL0 : 0 < L := Nat.mul_pos N.pos hd0
  have hdL : d ∣ L := dvd_mul_left d (N : ℕ)
  have hNL : (N : ℕ) ∣ L := dvd_mul_right (N : ℕ) d
  set Lp : ℕ+ := ⟨L, hL0⟩ with hLp
  -- The Artin-Schreier increment `y = x'^{1/p^L} - x'`.
  set y : HahnSeries ℚ (𝔽ᵃ_[p]) := (invFrobeniusHahn p)^[L] x' - x' with hy
  have hy_supp : ∀ q : ℚ, y.coeff (q / (a : ℚ)) ≠ 0 → q ∈ Tc p (c' + 1) := fun q hq =>
    levelDrop_support hsupp' L q hq
  have hy_per : IsTwistPeriodic p (fun z => y.coeff (z / (a : ℚ))) (c' + 1)
      (M + Lp) N := levelDrop_slice_periodic hsupp' hper' Lp
  -- The level-`≤ c'` part of `y` is integral by induction.
  set y0 : HahnSeries ℚ (𝔽ᵃ_[p]) := hahnRestrict (Sabc p a 0 c') y with hy0
  have hy0_coeff_of_mem : ∀ {g : ℚ}, g ∈ Sabc p a 0 c' → y0.coeff g = y.coeff g :=
    fun hg => coeff_hahnRestrict_of_mem _ hg
  have hy0_coeff_of_notMem : ∀ {g : ℚ}, g ∉ Sabc p a 0 c' → y0.coeff g = 0 :=
    fun hg => coeff_hahnRestrict_of_notMem _ hg
  have hy0_int : IsIntegral ((𝔽ᵃ_[p])⸨X⸩) y0 := by
    have hy_wit : SliceWitness p y a 0 (c' + 1) (M + Lp) N :=
      sliceWitness_of_slice_form hy_supp hy_per
    exact IH c' (by omega) y0 a 0 (M + Lp) N (hy_wit.levelRestrict (by omega))
  -- The remainder `w` is slice-supported on `T_{c'+1}` with vanishing deep
  -- coefficients.
  set w : HahnSeries ℚ (𝔽ᵃ_[p]) := y - y0 with hw
  have hw_coeff : ∀ g : ℚ, w.coeff g = y.coeff g - y0.coeff g := fun g =>
    HahnSeries.coeff_sub
  have hw_supp : ∀ q : ℚ, w.coeff (q / (a : ℚ)) ≠ 0 → q ∈ Tc p (c' + 1) := by
    intro q hq
    by_contra hqT
    apply hq
    have h0 : y.coeff (q / (a : ℚ)) = 0 := by
      by_contra hy0'
      exact hqT (hy_supp q hy0')
    have h00 : y0.coeff (q / (a : ℚ)) = 0 := by
      by_cases hmem : q / (a : ℚ) ∈ Sabc p a 0 c'
      · rw [hy0_coeff_of_mem hmem, h0]
      · exact hy0_coeff_of_notMem hmem
    rw [hw_coeff, h0, h00, sub_zero]
  have hw_per : IsTwistPeriodic p (fun z => w.coeff (z / (a : ℚ))) (c' + 1)
      (M + Lp) N := by
    have hy0_per : IsTwistPeriodic p (fun z => y0.coeff (z / (a : ℚ))) (c' + 1)
        (M + Lp) N := isTwistPeriodic_slice_hahnRestrict_Sabc hy_per
    have heq : (fun z : ℚ => w.coeff (z / (a : ℚ)))
        = fun z : ℚ => y.coeff (z / (a : ℚ)) - y0.coeff (z / (a : ℚ)) := by
      funext z
      exact hw_coeff _
    rw [heq]
    exact (hy_per.sub hy0_per).mono le_rfl (by simp)
      (PNat.dvd_iff.mp (PNat.lcm_dvd dvd_rfl dvd_rfl))
  have hw_deep : ∀ e : ℕ →₀ ℕ, (∀ i, e i < p) → (∀ i < (M : ℕ) + L, e i = 0) →
      w.coeff (-fracVal p e / (a : ℚ)) = 0 := by
    intro e he hdeep
    by_cases hesum : (e.sum fun _ v => v) ≤ c' + 1
    · rw [hw_coeff]
      by_cases hesum' : (e.sum fun _ v => v) ≤ c'
      · -- Cancellation: the exponent lies in `S_{a,0,c'}`, where `y0 = y`.
        have hmem : -fracVal p e / (a : ℚ) ∈ Sabc p a 0 c' :=
          ⟨0, e, by norm_num, he, hesum', by rw [fracVal_def]; push_cast; ring⟩
        rw [hy0_coeff_of_mem hmem, sub_self]
      · -- Level exactly `c'+1`: the level drop kills the deep coefficient of `y`.
        have hy_zero : y.coeff (-fracVal p e / (a : ℚ)) = 0 :=
          levelDrop_deep_coeff hsupp' hper' hval hdL hNL he hesum hdeep
        have hy0_zero : y0.coeff (-fracVal p e / (a : ℚ)) = 0 := by
          by_cases hmem : -fracVal p e / (a : ℚ) ∈ Sabc p a 0 c'
          · rw [hy0_coeff_of_mem hmem, hy_zero]
          · exact hy0_coeff_of_notMem hmem
        rw [hy_zero, hy0_zero, sub_zero]
    · -- Digit sum beyond `c'+1`: outside the slice support (canonical strings are
      -- unique).
      by_contra h0
      obtain ⟨e₂, he₂, hsum₂, heq₂⟩ := Tc_subset_neg_fracVal p (c' + 1) (hw_supp _ h0)
      rw [eq_of_fracVal_eq p hp.out.one_lt he₂ he (neg_inj.mp heq₂.symm)] at hsum₂
      exact hesum hsum₂
  -- First-digit decomposition of `w` into monomial multiples of lower-level series.
  have hw_int : IsIntegral ((𝔽ᵃ_[p])⸨X⸩) w := by
    rw [firstDigit_decomp hw_supp ((M : ℕ) + L) hw_deep]
    refine isIntegral_finset_sum _ fun k _ => isIntegral_finset_sum _ fun β hβ => ?_
    rw [← single_neg_mul_firstDigitShift]
    obtain ⟨hβ0, hβp⟩ := Finset.mem_Ioo.mp hβ
    refine (isIntegral_single _ _).mul ?_
    -- The shifted first-digit class lives at level `c' + 1 - β < c' + 1`.
    have hu_supp : ∀ q : ℚ, (firstDigitShift a k β w).coeff (q / (a : ℚ)) ≠ 0 →
        q ∈ Tc p (c' + 1 - β) ∪ {0} := fun q hq =>
      firstDigitShift_support hw_supp k β q hq
    have hu_per : IsTwistPeriodic p
        (fun z => (firstDigitShift a k β w).coeff (z / (a : ℚ))) (c' + 1 - β)
        (M + Lp + k.succPNat) N := by
      by_cases hβc : β ≤ c' + 1
      · refine firstDigitShift_slice_periodic hw_per hβp hβc ?_
        simp only [PNat.add_coe, Nat.succPNat_coe]
        omega
      · have hc₂0 : c' + 1 - β = 0 := by omega
        rw [hc₂0]
        exact isTwistPeriodic_zero_level _ _ _
    exact IH (c' + 1 - β) (by omega) _ a 0 _ N
      (sliceWitness_of_window_form hu_supp hu_per)
  -- Reassemble: `y` is integral, so `x'` solves a monic Artin-Schreier equation.
  have hy_int : IsIntegral ((𝔽ᵃ_[p])⸨X⸩) y := by
    have hy_eq : y = y0 + w := by
      rw [hw]
      ring
    rw [hy_eq]
    exact hy0_int.add hw_int
  have hyp_pow : y ^ p ^ L = x' - x' ^ p ^ L := levelDrop_pow_eq x' L
  have hx'_int : IsIntegral ((𝔽ᵃ_[p])⸨X⸩) x' := by
    refine isIntegral_of_pow_eq_sub (t := y ^ p ^ L) (hy_int.pow (p ^ L))
      (Nat.one_lt_pow hL0.ne' hp.out.one_lt) ?_
    rw [hyp_pow]
    ring
  rw [hsplit]
  exact (isIntegral_single _ _).add hx'_int

/-- **Uniformly periodic series are integral over the Laurent field** (induction
core): a series with a slice witness at digit-sum level `c` is integral over
`𝔽̄_p((t))`. -/
theorem isIntegral_of_sliceWitness {x : HahnSeries ℚ (𝔽ᵃ_[p])} {a : ℕ+} {b c : ℕ}
    {M N : ℕ+} (hx : SliceWitness p x a b c M N) :
    IsIntegral ((𝔽ᵃ_[p])⸨X⸩) x := by
  induction c using Nat.strongRecOn generalizing x a b M N with
  | ind c IH =>
  obtain ⟨r, lam, xs, hlam_supp, hxs_supp, hxs_wit, rfl⟩ := hx.exists_slice_span
  refine isIntegral_finset_sum _ fun i _ => IsIntegral.mul ?_ ?_
  · exact isIntegral_hahn_of_support_int_div a fun s hs =>
      (hlam_supp i s hs).imp fun m hm => hm.2
  · have hsupp_i : ∀ q : ℚ, (xs i).coeff (q / (a : ℚ)) ≠ 0 → q ∈ Tc p c ∪ {0} :=
      fun q hq => div_mem_image_div_iff.mp (hxs_supp i hq)
    have hper_i : IsTwistPeriodic p (fun z => (xs i).coeff (z / (a : ℚ))) c M N := by
      have h0 := (hxs_wit i).2 0 (by norm_num)
      simpa using h0
    exact isIntegral_of_window_form (fun c' hc' x' a' b' M' N' hx' => IH c' hc' hx')
      hsupp_i hper_i

/-- **Uniformly periodic series are integral over the Laurent field** (integral form). -/
theorem IsUP.isIntegral {x : HahnSeries ℚ (𝔽ᵃ_[p])} (hx : IsUP p x) :
    IsIntegral ((𝔽ᵃ_[p])⸨X⸩) x := by
  obtain ⟨a, b, c, M, N, hw⟩ := isUP_iff_exists_sliceWitness.mp hx
  exact isIntegral_of_sliceWitness hw

/-- **Uniformly periodic series are algebraic over the Laurent field**. -/
theorem IsUP.isAlgebraic {x : HahnSeries ℚ (𝔽ᵃ_[p])} (hx : IsUP p x) :
    IsAlgebraic ((𝔽ᵃ_[p])⸨X⸩) x :=
  hx.isIntegral.isAlgebraic

end TrustworthyKedlaya.UP
