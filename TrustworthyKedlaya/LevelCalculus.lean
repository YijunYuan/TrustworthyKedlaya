/-
Copyright (c) 2026 Shanwen Wang, Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import TrustworthyKedlaya.FrobeniusUP
public import TrustworthyKedlaya.FiniteImage
public import TrustworthyKedlaya.ArtinSchreierNeg

/-!
# Dismantling a UP series along digit-sum levels

The level-`c` induction that proves algebraicity of UP series dismantles a series along
the *levels* of its exponents: for an exponent `s` written as
`as = m - w` with `m ∈ ℤ` and `w ∈ [0,1)`, the level is the digit sum of the canonical
base-`p` expansion of `w`.  The exponents of level `≤ c'` inside `S_{a,b,c}` are exactly
the points of `S_{a,b,c'}` (canonical expansions are unique), so level restriction is
Hahn-series restriction (`hahnRestrict`) to a smaller support set.

## Main statements

- `TrustworthyKedlaya.UP.SliceWitness.levelRestrict`: restricting a UP series to the
  exponents of level at most `c' ≤ c` preserves the UP data, lowering the level to `c'`.

## References

- K. S. Kedlaya, *The algebraic closure of the power series field in positive
  characteristic*, Proc. Amer. Math. Soc. 129 (2001) [Ked01a], proof of Theorem 8.
-/

@[expose] public section

namespace TrustworthyKedlaya.UP

variable {p : ℕ} [hp : Fact (Nat.Prime p)]

/-- **Level restriction**: if `x` is UP, presented
on `S_{a,b,c}` with every width-`a` slice `(M, N)`-periodic at level `c`, and
`c' ≤ c`, then the restriction of `x` to the exponents of level at most `c'` — that is,
`hahnRestrict (Sabc p a b c') x` — is UP, presented on `S_{a,b,c'}` with the same
periodicity data at level `c'`.  Twist sequences at level `≤ c'` only evaluate the
slices at points of level `≤ c'`, where the restriction agrees with `x`. -/
theorem SliceWitness.levelRestrict {x : HahnSeries ℚ (𝔽ᵃ_[p])} {a : ℕ+} {b c : ℕ}
    {M N : ℕ+} (h : SliceWitness p x a b c M N) {c' : ℕ} (hc' : c' ≤ c) :
    SliceWitness p (hahnRestrict (Sabc p a b c') x) a b c' M N := by
  refine ⟨support_hahnRestrict_subset_set _ _, fun m hm j dig hj hdig hsum n hn => ?_⟩
  -- Every twist sequence of the restricted slice agrees termwise with that of `x`.
  have key : ∀ n' : ℕ,
      twistSeq p (fun z => (hahnRestrict (Sabc p a b c') x).coeff (((m : ℚ) + z) / (a : ℚ)))
        j dig n' = twistSeq p (fun z => x.coeff (((m : ℚ) + z) / (a : ℚ))) j dig n' := by
    intro n'
    have hmem : ((m : ℚ) + -fracVal p (gapDig j n' dig)) / (a : ℚ) ∈ Sabc p a b c' := by
      refine ⟨m, gapDig j n' dig, hm, fun i => gapDig_lt p hdig hp.out.pos _ _ i, ?_, ?_⟩
      · rw [gapDig_sum]
        exact hsum
      · rw [fracVal_def]
        ring
    rw [twistSeq_eq_neg_fracVal_gapDig, twistSeq_eq_neg_fracVal_gapDig]
    exact coeff_hahnRestrict_of_mem x hmem
  rw [key, key]
  exact h.2 m hm j dig hj hdig (hsum.trans hc') n hn

/-! ### Digit-string shifts

Multiplying a fractional value by `p^L` shifts all digits `L` positions shallower;
`dropGapDig 0 L` is that shift on digit strings.  These lemmas record the interaction
of the shift with `fracVal`, `gapDig` and the digit sum, and the vanishing threshold:
a digit at a position `≤ L` makes `p^L · fracVal` at least `1`. -/

/-- Shifting a digit string with no digits at positions `≤ L` up by `L` multiplies its
fractional value by `p^L`. -/
theorem fracVal_dropGapDig_zero {L : ℕ} {e : ℕ →₀ ℕ} (he0 : ∀ i < L, e i = 0) :
    fracVal p (dropGapDig 0 L e) = (p : ℚ) ^ L * fracVal p e := by
  have hpq : (0 : ℚ) < (p : ℚ) := by exact_mod_cast hp.out.pos
  have hgd : gapDig 1 L (dropGapDig 0 L e) = e :=
    gapDig_dropGapDig fun i _ hi => he0 i (by omega)
  have hfv := fracVal_gapDig_split (p := p) 1 L (dropGapDig 0 L e)
  rw [hgd] at hfv
  have h1 : (1 : ℕ) - 1 = 0 := rfl
  rw [h1] at hfv
  simp only [Nat.not_lt_zero, Nat.zero_le] at hfv
  rw [(Finsupp.filter_eq_zero_iff _ _).mpr fun x hx => hx.elim,
    (Finsupp.filter_eq_self_iff _ _).mpr fun x _ => trivial,
    fracVal_zero, zero_add] at hfv
  rw [hfv, ← mul_assoc, ← zpow_natCast (p : ℚ) L, ← zpow_add₀ hpq.ne']
  simp

/-- A digit at a position `≤ L` pushes the `p^L`-fold fractional value to at least
`1`. -/
theorem one_le_pow_mul_fracVal {L : ℕ} {e : ℕ →₀ ℕ} {i : ℕ} (hi : i < L)
    (hei : e i ≠ 0) : (1 : ℚ) ≤ (p : ℚ) ^ L * fracVal p e := by
  have hpq : (1 : ℚ) ≤ (p : ℚ) := by exact_mod_cast hp.out.one_le
  have hterm : (p : ℚ) ^ (-(i + 1 : ℤ)) ≤ (e i : ℚ) * (p : ℚ) ^ (-(i + 1 : ℤ)) := by
    have h1 : (1 : ℚ) ≤ (e i : ℚ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hei
    nlinarith [zpow_pos (by linarith : (0:ℚ) < (p:ℚ)) (-(i + 1 : ℤ))]
  have hsum : (e i : ℚ) * (p : ℚ) ^ (-(i + 1 : ℤ)) ≤ fracVal p e := by
    rw [← fracVal_def]
    exact Finset.single_le_sum
      (f := fun j => ((e j : ℚ) * (p : ℚ) ^ (-(j + 1 : ℤ))))
      (fun j _ => by positivity) (Finsupp.mem_support_iff.mpr hei)
  have hpow : (1 : ℚ) ≤ (p : ℚ) ^ L * (p : ℚ) ^ (-(i + 1 : ℤ)) := by
    rw [← zpow_natCast (p : ℚ) L, ← zpow_add₀ (by linarith : (p:ℚ) ≠ 0)]
    exact one_le_zpow₀ hpq (by omega)
  calc (1 : ℚ) ≤ (p : ℚ) ^ L * (p : ℚ) ^ (-(i + 1 : ℤ)) := hpow
    _ ≤ (p : ℚ) ^ L * fracVal p e := by
        have := hterm.trans hsum
        nlinarith [pow_pos (by linarith : (0:ℚ) < (p:ℚ)) L]

/-- The `L`-fold shallow shift commutes with opening a gap beyond position `L`. -/
theorem dropGapDig_zero_gapDig {j L : ℕ} (hj : L + 1 ≤ j) (n : ℕ) (dig : ℕ →₀ ℕ) :
    dropGapDig 0 L (gapDig j n dig) = gapDig (j - L) n (dropGapDig 0 L dig) := by
  ext i
  simp only [dropGapDig_apply, gapDig_apply]
  split_ifs <;> first
    | rfl
    | omega
    | (congr 1; omega)

/-- Shifting away `L` leading zero digits preserves the digit sum. -/
theorem sum_dropGapDig_zero {L : ℕ} {e : ℕ →₀ ℕ} (he0 : ∀ i < L, e i = 0) :
    ((dropGapDig 0 L e).sum fun _ v => v) = e.sum fun _ v => v := by
  have hgd : gapDig 1 L (dropGapDig 0 L e) = e :=
    gapDig_dropGapDig fun i _ hi => he0 i (by omega)
  conv_rhs => rw [← hgd]
  rw [gapDig_sum]

/-! ### Membership in `T_c` -/

/-- A nonzero canonical expansion of digit sum `≤ c` yields a point of `T_c`. -/
theorem neg_fracVal_mem_Tc {e : ℕ →₀ ℕ} {c : ℕ} (he : ∀ i, e i < p)
    (hsum : (e.sum fun _ v => v) ≤ c) (hne : e ≠ 0) : -fracVal p e ∈ Tc p c := by
  refine ⟨⟨0, e, by norm_num, he, hsum, ?_⟩,
    by linarith [fracVal_lt_one p hp.out.one_lt he],
    by linarith [fracVal_pos p hp.out.pos hne]⟩
  rw [fracVal_def]
  norm_num

/-- Dividing by `p^L` preserves membership in `T_c`: the digits move deeper, keeping
the digit sum and the interval `(-1, 0)`. -/
theorem Tc_mem_of_pow_mul_mem {c L : ℕ} {q : ℚ} (h : (p : ℚ) ^ L * q ∈ Tc p c) :
    q ∈ Tc p c := by
  have hpq : (0 : ℚ) < (p : ℚ) := by exact_mod_cast hp.out.pos
  obtain ⟨E, hEd, hEs, hEeq⟩ := Tc_subset_neg_fracVal p c h
  have hE0 : E ≠ 0 := by
    rintro rfl
    rw [fracVal_zero, neg_zero] at hEeq
    exact absurd (hEeq ▸ h.2.2) (lt_irrefl 0)
  have hq : q = -fracVal p (gapDig 1 L E) := by
    rw [fracVal_gapDig_one, zpow_neg, zpow_natCast]
    have hpL : (0 : ℚ) < (p : ℚ) ^ L := by positivity
    field_simp
    linarith [hEeq]
  rw [hq]
  refine neg_fracVal_mem_Tc (fun i => gapDig_lt p hEd hp.out.pos _ _ i)
    (by rw [gapDig_sum]; exact hEs) ?_
  obtain ⟨i₀, hi₀⟩ := Finsupp.ne_iff.mp hE0
  intro hzero
  have hcoord := congrArg (fun f : ℕ →₀ ℕ => f (i₀ + L)) hzero
  simp only [gapDig_apply, Finsupp.coe_zero, Pi.zero_apply] at hcoord
  rw [if_neg (by omega), if_pos (by omega), Nat.add_sub_cancel] at hcoord
  exact hi₀ (by simpa using hcoord)

/-! ### Iterated inverse Frobenius -/

/-- Coefficients of the `L`-fold inverse Frobenius: read off at the `p^L`-fold
exponent, taking the `p^L`-th root of the value. -/
theorem coeff_invFrobeniusHahn_iterate (x : HahnSeries ℚ (𝔽ᵃ_[p])) (L : ℕ) (g : ℚ) :
    ((invFrobeniusHahn p)^[L] x).coeff g
      = ((frobeniusEquiv (𝔽ᵃ_[p]) p).symm)^[L] (x.coeff ((p : ℚ) ^ L * g)) := by
  induction L generalizing g with
  | zero => simp
  | succ L ih =>
    have harg : (p : ℚ) ^ (L + 1) * g = (p : ℚ) ^ L * ((p : ℚ) * g) := by ring
    rw [Function.iterate_succ_apply' (f := invFrobeniusHahn p), coeff_invFrobeniusHahn,
      ih, harg, Function.iterate_succ_apply' (f := (frobeniusEquiv (𝔽ᵃ_[p]) p).symm)]

/-- The `L`-fold inverse Frobenius is a `p^L`-th root. -/
theorem invFrobeniusHahn_iterate_pow (x : HahnSeries ℚ (𝔽ᵃ_[p])) (L : ℕ) :
    ((invFrobeniusHahn p)^[L] x) ^ p ^ L = x := by
  induction L generalizing x with
  | zero => simp
  | succ L ih =>
    rw [Function.iterate_succ_apply, pow_succ, pow_mul, ih (invFrobeniusHahn p x),
      invFrobeniusHahn_pow]

/-- The `L`-fold inverse Frobenius on values undoes the `p^L`-th power. -/
theorem frobeniusEquiv_symm_iterate_pow_pow (v : 𝔽ᵃ_[p]) (L : ℕ) :
    ((frobeniusEquiv (𝔽ᵃ_[p]) p).symm)^[L] (v ^ p ^ L) = v := by
  induction L generalizing v with
  | zero => simp
  | succ L ih =>
    have h1 : (frobeniusEquiv (𝔽ᵃ_[p]) p).symm ((v ^ p ^ L) ^ p) = v ^ p ^ L := by
      rw [← frobenius_def, ← frobeniusEquiv_apply, RingEquiv.symm_apply_apply]
    rw [Function.iterate_succ_apply, pow_succ, pow_mul, h1, ih]

/-- Elements of `𝔽_{p^L}` are fixed by the `L`-fold inverse Frobenius. -/
theorem frobeniusEquiv_symm_iterate_fixed {v : 𝔽ᵃ_[p]} {L : ℕ}
    (hv : v ^ p ^ L = v) : ((frobeniusEquiv (𝔽ᵃ_[p]) p).symm)^[L] v = v := by
  conv_lhs => rw [← hv]
  rw [frobeniusEquiv_symm_iterate_pow_pow]

/-! ### Rescaling the argument by `p^L` -/

/-- **Exponent rescaling by `p^L` preserves twist-periodicity, shifting the preperiod
by `L`.**  If `f` vanishes on `(-∞, -1]` (as coefficient slice functions supported on
`T_c` do) and is `(M, N)`-periodic at level `c`, then `z ↦ f (p^L z)` is periodic at
level `c` with the same period and any preperiod `≥ M + L`.  Digit strings with a
head digit at position `≤ L` give identically vanishing sequences; a gap beyond `L`
turns the sequence into that of the `L`-fold shallower string; a shallow gap (empty
head) reproduces the original sequence at depth `n - L`. -/
theorem isTwistPeriodic_comp_pow_scale {f : ℚ → 𝔽ᵃ_[p]} {c : ℕ} {M N : ℕ+} {L : ℕ}
    {P : ℕ+} (hP : (M : ℕ) + L ≤ (P : ℕ))
    (hvanish : ∀ w : ℚ, w ≤ -1 → f w = 0)
    (hper : IsTwistPeriodic p f c M N) :
    IsTwistPeriodic p (fun z => f ((p : ℚ) ^ L * z)) c P N := by
  have hpq : (0 : ℚ) < (p : ℚ) := by exact_mod_cast hp.out.pos
  intro j dig hj hdig hsum n hn
  -- Every term is `f` at `-(p^L · fracVal (gapDig j n' dig))`.
  have hterm : ∀ n' : ℕ, twistSeq p (fun z => f ((p : ℚ) ^ L * z)) j dig n'
      = f (-((p : ℚ) ^ L * fracVal p (gapDig j n' dig))) := by
    intro n'
    rw [twistSeq_eq_neg_fracVal_gapDig, mul_neg]
  by_cases hA : ∃ i, i < j - 1 ∧ i < L ∧ dig i ≠ 0
  · -- A head digit at position `≤ L`: every term vanishes.
    obtain ⟨i, hij, hiL, hi0⟩ := hA
    have hzero : ∀ n' : ℕ, twistSeq p (fun z => f ((p : ℚ) ^ L * z)) j dig n' = 0 := by
      intro n'
      rw [hterm n']
      refine hvanish _ ?_
      have h1 : (1 : ℚ) ≤ (p : ℚ) ^ L * fracVal p (gapDig j n' dig) :=
        one_le_pow_mul_fracVal hiL (by rw [gapDig_apply, if_pos hij]; exact hi0)
      linarith
    rw [hzero, hzero]
  · push Not at hA
    by_cases hjL : L + 1 ≤ j
    · -- Gap beyond `L`: the sequence is that of the `L`-fold shallower string.
      have hkey : ∀ n', twistSeq p (fun z => f ((p : ℚ) ^ L * z)) j dig n'
          = twistSeq p f (j - L) (dropGapDig 0 L dig) n' := by
        intro n'
        have hgap0 : ∀ i < L, gapDig j n' dig i = 0 := by
          intro i hiL
          rw [gapDig_apply, if_pos (by omega)]
          exact hA i (by omega) hiL
        rw [hterm n', twistSeq_eq_neg_fracVal_gapDig, ← dropGapDig_zero_gapDig hjL,
          fracVal_dropGapDig_zero hgap0]
      rw [hkey, hkey]
      exact hper (j - L) (dropGapDig 0 L dig) (by omega)
        (fun i => dropGapDig_lt p hdig _ _ i)
        (by rw [sum_dropGapDig_zero fun i hiL => hA i (by omega) hiL]; exact hsum)
        n (by have := hP; omega)
    · -- Shallow gap: the head is empty, and terms shift by `L` in depth.
      have hhead : ∀ i, i < j - 1 → dig i = 0 := fun i hij => hA i hij (by omega)
      have hheadf : (Finsupp.filter (fun i => i < j - 1) dig) = 0 :=
        (Finsupp.filter_eq_zero_iff _ _).mpr fun i hi => hhead i hi
      have hkey : ∀ n', L ≤ n' → twistSeq p (fun z => f ((p : ℚ) ^ L * z)) j dig n'
          = twistSeq p f j dig (n' - L) := by
        intro n' hLn'
        rw [hterm n', twistSeq_eq_neg_fracVal_gapDig,
          fracVal_gapDig_split (p := p) j n' dig,
          fracVal_gapDig_split (p := p) j (n' - L) dig, hheadf, fracVal_zero,
          zero_add, zero_add, ← mul_assoc, ← zpow_natCast (p : ℚ) L,
          ← zpow_add₀ hpq.ne',
          show (L : ℤ) + -(n' : ℤ) = -((n' - L : ℕ) : ℤ) by omega]
      rw [hkey (n + ↑N) (by have := hP; omega), hkey n (by have := hP; omega)]
      have h1 : n + (N : ℕ) - L = (n - L) + (N : ℕ) := by have := hP; omega
      rw [h1]
      exact hper j dig hj hdig hsum (n - L) (by have := hP; omega)

/-- Pointwise differences of twist-periodic functions are twist-periodic. -/
theorem IsTwistPeriodic.sub {f g : ℚ → 𝔽ᵃ_[p]} {c : ℕ} {Mf Mg Nf Ng : ℕ+}
    (hf : IsTwistPeriodic p f c Mf Nf) (hg : IsTwistPeriodic p g c Mg Ng) :
    IsTwistPeriodic p (fun z => f z - g z) c (max Mf Mg) (Nf.lcm Ng) := by
  have h := hf.add (hg.comp fun v => -v)
  simpa only [sub_eq_add_neg] using h

/-! ### Level drop

For `x` supported on `(1/a)·T_c` with its width-`a` slice `(M, N)`-periodic at level
`c` and slice values in `𝔽_{p^d}`, and `L` a common multiple of `N` and `d` with
`L ≥ M`, the Artin-Schreier increment `y = x^{1/p^L} − x` stays supported on
`(1/a)·T_c`, its slice is `(M + L, N)`-periodic at level `c`, its coefficients vanish
at every exponent whose digits all sit at positions `> M + L`, and
`y^{p^L} = x − x^{p^L}`.  Support hypotheses and conclusions are phrased through the
width-`a` slice: `x.coeff (q / a) ≠ 0 → q ∈ T_c`. -/

section LevelDrop

variable {x : HahnSeries ℚ (𝔽ᵃ_[p])} {a : ℕ+} {c : ℕ} {M N : ℕ+}

/-- A series slice-supported on `T_c` vanishes at slice arguments outside `T_c`. -/
theorem coeff_slice_eq_zero_of_notMem
    (hsupp : ∀ q : ℚ, x.coeff (q / (a : ℚ)) ≠ 0 → q ∈ Tc p c) {w : ℚ}
    (hw : w ∉ Tc p c) : x.coeff (w / (a : ℚ)) = 0 := by
  by_contra h0
  exact hw (hsupp w h0)

/-- **Level drop, support**: the Artin-Schreier increment stays slice-supported on
`T_c`. -/
theorem levelDrop_support (hsupp : ∀ q : ℚ, x.coeff (q / (a : ℚ)) ≠ 0 → q ∈ Tc p c)
    (L : ℕ) (q : ℚ)
    (hq : ((invFrobeniusHahn p)^[L] x - x).coeff (q / (a : ℚ)) ≠ 0) : q ∈ Tc p c := by
  rw [HahnSeries.coeff_sub] at hq
  by_cases hx0 : x.coeff (q / (a : ℚ)) ≠ 0
  · exact hsupp q hx0
  · have hxL : ((invFrobeniusHahn p)^[L] x).coeff (q / (a : ℚ)) ≠ 0 := by
      intro h
      rw [h, not_not.mp hx0, sub_zero] at hq
      exact hq rfl
    rw [coeff_invFrobeniusHahn_iterate] at hxL
    have hcoeff : x.coeff ((p : ℚ) ^ L * q / (a : ℚ)) ≠ 0 := by
      intro h
      rw [show (p : ℚ) ^ L * (q / (a : ℚ)) = (p : ℚ) ^ L * q / (a : ℚ) by ring, h] at hxL
      exact hxL (Function.iterate_fixed (map_zero _) L)
    exact Tc_mem_of_pow_mul_mem (hsupp _ hcoeff)

/-- **Level drop, slice periodicity**: the slice of the Artin-Schreier increment is
`(M + L, N)`-periodic at level `c`. -/
theorem levelDrop_slice_periodic
    (hsupp : ∀ q : ℚ, x.coeff (q / (a : ℚ)) ≠ 0 → q ∈ Tc p c)
    (hper : IsTwistPeriodic p (fun z => x.coeff (z / (a : ℚ))) c M N) (L : ℕ+) :
    IsTwistPeriodic p
      (fun z => ((invFrobeniusHahn p)^[(L : ℕ)] x - x).coeff (z / (a : ℚ)))
      c (M + L) N := by
  have hvanish : ∀ w : ℚ, w ≤ -1 → x.coeff (w / (a : ℚ)) = 0 := fun w hw =>
    coeff_slice_eq_zero_of_notMem hsupp fun hmem => by
      have := hmem.2.1
      linarith
  have hML : (M : ℕ) + (L : ℕ) ≤ ((M + L : ℕ+) : ℕ) := by simp
  have hxL : IsTwistPeriodic p
      (fun z => ((invFrobeniusHahn p)^[(L : ℕ)] x).coeff (z / (a : ℚ))) c (M + L) N := by
    have hcomp := (isTwistPeriodic_comp_pow_scale (L := (L : ℕ)) hML hvanish hper).comp
      (((frobeniusEquiv (𝔽ᵃ_[p]) p).symm)^[(L : ℕ)])
    have heq : (fun z => ((invFrobeniusHahn p)^[(L : ℕ)] x).coeff (z / (a : ℚ)))
        = fun z => ((frobeniusEquiv (𝔽ᵃ_[p]) p).symm)^[(L : ℕ)]
            (x.coeff ((p : ℚ) ^ (L : ℕ) * z / (a : ℚ))) := by
      funext z
      rw [coeff_invFrobeniusHahn_iterate]
      congr 2
      ring
    rw [heq]
    exact hcomp
  have hx' : IsTwistPeriodic p (fun z => x.coeff (z / (a : ℚ))) c (M + L) N :=
    hper.mono le_rfl (by simp) dvd_rfl
  have hsub := hxL.sub hx'
  have hfin := hsub.mono le_rfl
    (by simp : ((max (M + L) (M + L) : ℕ+) : ℕ) ≤ ((M + L : ℕ+) : ℕ))
    (PNat.dvd_iff.mp (PNat.lcm_dvd dvd_rfl dvd_rfl))
  have heqf : (fun z => ((invFrobeniusHahn p)^[(L : ℕ)] x - x).coeff (z / (a : ℚ)))
      = fun z => ((invFrobeniusHahn p)^[(L : ℕ)] x).coeff (z / (a : ℚ))
          - x.coeff (z / (a : ℚ)) := by
    funext z
    rw [HahnSeries.coeff_sub]
  rw [heqf]
  exact hfin

/-- **Level drop, deep coefficients vanish**: at every exponent all of whose digits
sit at positions `> M + L` (with `L` a common multiple of `N` and `d`, `L ≥ M`, and
the slice values on `T_c` lying in `𝔽_{p^d}`), the Artin-Schreier increment has zero
coefficient.  Equivalently, every surviving exponent of maximal level has its first
digit at a position `≤ M + L`. -/
theorem levelDrop_deep_coeff
    (hsupp : ∀ q : ℚ, x.coeff (q / (a : ℚ)) ≠ 0 → q ∈ Tc p c)
    (hper : IsTwistPeriodic p (fun z => x.coeff (z / (a : ℚ))) c M N) {d L : ℕ}
    (hval : ∀ z ∈ Tc p c, x.coeff (z / (a : ℚ)) ^ p ^ d = x.coeff (z / (a : ℚ)))
    (hdL : d ∣ L) (hNL : (N : ℕ) ∣ L)
    {e : ℕ →₀ ℕ} (he : ∀ i, e i < p) (hsum : (e.sum fun _ v => v) ≤ c)
    (hdeep : ∀ i, i < (M : ℕ) + L → e i = 0) :
    ((invFrobeniusHahn p)^[L] x - x).coeff (-fracVal p e / (a : ℚ)) = 0 := by
  have hpq : (0 : ℚ) < (p : ℚ) := by exact_mod_cast hp.out.pos
  have he0L : ∀ i < L, e i = 0 := fun i hi => hdeep i (by omega)
  rw [HahnSeries.coeff_sub, coeff_invFrobeniusHahn_iterate]
  have harg : (p : ℚ) ^ L * (-fracVal p e / (a : ℚ))
      = -fracVal p (dropGapDig 0 L e) / (a : ℚ) := by
    rw [fracVal_dropGapDig_zero he0L]
    ring
  rw [harg]
  -- The two slice values agree, by iterating the period `L/N` times along the
  -- rebased digit string.
  have hfix : x.coeff (-fracVal p e / (a : ℚ))
      = x.coeff (-fracVal p (dropGapDig 0 L e) / (a : ℚ)) := by
    set D : ℕ →₀ ℕ := dropGapDig 0 ((M : ℕ) + L) e with hD
    have htw : ∀ n : ℕ, twistSeq p (fun z => x.coeff (z / (a : ℚ))) 1 D n
        = x.coeff (-((p : ℚ) ^ (-(n : ℤ)) * fracVal p D) / (a : ℚ)) := by
      intro n
      rw [twistSeq_eq_neg_fracVal_gapDig, fracVal_gapDig_one]
    have hDval : fracVal p D = (p : ℚ) ^ ((M : ℕ) + L) * fracVal p e :=
      fracVal_dropGapDig_zero hdeep
    have hDd : ∀ i, D i < p := fun i => dropGapDig_lt p he _ _ i
    have hDsum : (D.sum fun _ v => v) ≤ c := by
      rw [hD, sum_dropGapDig_zero hdeep]
      exact hsum
    have hiter := eventually_periodic_iterate
      (y := fun n => twistSeq p (fun z => x.coeff (z / (a : ℚ))) 1 D n)
      (M := (M : ℕ)) (N := (N : ℕ))
      (fun n hn => hper 1 D Nat.one_pos hDd hDsum n hn) (L / (N : ℕ)) (M : ℕ) le_rfl
    rw [Nat.mul_div_cancel' hNL] at hiter
    rw [htw, htw, hDval] at hiter
    have hexp1 : (p : ℚ) ^ (-(((M : ℕ) + L : ℕ) : ℤ))
        * ((p : ℚ) ^ ((M : ℕ) + L) * fracVal p e) = fracVal p e := by
      rw [← mul_assoc, ← zpow_natCast (p : ℚ) ((M : ℕ) + L), ← zpow_add₀ hpq.ne']
      simp
    have hexp2 : (p : ℚ) ^ (-((M : ℕ) : ℤ))
        * ((p : ℚ) ^ ((M : ℕ) + L) * fracVal p e) = fracVal p (dropGapDig 0 L e) := by
      rw [fracVal_dropGapDig_zero he0L, ← mul_assoc, ← zpow_natCast (p : ℚ) ((M : ℕ) + L),
        ← zpow_add₀ hpq.ne', ← zpow_natCast (p : ℚ) L,
        show -((M : ℕ) : ℤ) + (((M : ℕ) + L : ℕ) : ℤ) = (L : ℤ) by push_cast; ring]
    rw [show ((M : ℕ) + L : ℕ) = (M : ℕ) + L from rfl] at hiter
    rw [hexp1] at hiter
    rw [hexp2] at hiter
    exact hiter
  rw [← hfix]
  -- The common value lies in `𝔽_{p^L}`, so the `p^L`-th root fixes it.
  by_cases he0 : e = 0
  · subst he0
    have h0 : x.coeff (-fracVal p (0 : ℕ →₀ ℕ) / (a : ℚ)) = 0 := by
      rw [fracVal_zero]
      refine coeff_slice_eq_zero_of_notMem hsupp fun hmem => ?_
      rw [neg_zero] at hmem
      exact lt_irrefl 0 hmem.2.2
    rw [h0, Function.iterate_fixed (map_zero _) L, sub_zero]
  · have hTc : -fracVal p e ∈ Tc p c := neg_fracVal_mem_Tc he hsum he0
    have hv := hval _ hTc
    obtain ⟨k, hk⟩ := hdL
    have hvL : x.coeff (-fracVal p e / (a : ℚ)) ^ p ^ L
        = x.coeff (-fracVal p e / (a : ℚ)) := by
      rw [hk]
      exact pow_pow_mul_eq_self hv k
    rw [frobeniusEquiv_symm_iterate_fixed hvL, sub_self]

/-- **Level drop, Artin-Schreier identity**: `y^{p^L} = x − x^{p^L}` for the
increment `y = x^{1/p^L} − x`. -/
theorem levelDrop_pow_eq (x : HahnSeries ℚ (𝔽ᵃ_[p])) (L : ℕ) :
    ((invFrobeniusHahn p)^[L] x - x) ^ p ^ L = x - x ^ p ^ L := by
  rw [sub_pow_char_pow, invFrobeniusHahn_iterate_pow]

/-- **Slice form to `SliceWitness`**: a series slice-supported on `T_c` whose
width-`a` slice is `(M, N)`-periodic at level `c` is UP, presented on `S_{a,0,c}` —
the slices of index `m ≥ 1` vanish at every twist evaluation point. -/
theorem sliceWitness_of_slice_form {x : HahnSeries ℚ (𝔽ᵃ_[p])}
    (hsupp : ∀ q : ℚ, x.coeff (q / (a : ℚ)) ≠ 0 → q ∈ Tc p c)
    (hper : IsTwistPeriodic p (fun z => x.coeff (z / (a : ℚ))) c M N) :
    SliceWitness p x a 0 c M N := by
  have ha : ((a : ℕ) : ℚ) ≠ 0 := by exact_mod_cast a.pos.ne'
  constructor
  · intro s hs
    have hq : x.coeff (((a : ℚ) * s) / (a : ℚ)) ≠ 0 := by
      rw [mul_div_cancel_left₀ s ha]
      exact hs
    obtain ⟨⟨n, e, hn, he, hsum, heq⟩, hIoo⟩ := hsupp _ hq
    refine ⟨n, e, hn, he, hsum, ?_⟩
    have h1 : ((1 : ℕ+) : ℚ) = 1 := by norm_num
    rw [h1] at heq
    field_simp at heq ⊢
    linarith [heq]
  · intro m hm
    rcases (by omega : m = 0 ∨ 1 ≤ m) with rfl | hm1
    · simpa using hper
    · intro j dig hj hdig hsum' n hn
      have hzero : ∀ n',
          twistSeq p (fun z => x.coeff (((m : ℚ) + z) / (a : ℚ))) j dig n' = 0 := by
        intro n'
        rw [twistSeq_eq_neg_fracVal_gapDig]
        by_contra h0
        have hneg := (hsupp _ h0).2.2
        have hlt := fracVal_lt_one p hp.out.one_lt (d := gapDig j n' dig)
          fun i => gapDig_lt p hdig hp.out.pos j n' i
        have hm' : (1 : ℚ) ≤ (m : ℚ) := by exact_mod_cast hm1
        linarith
      rw [hzero, hzero]

end LevelDrop

/-! ### First-digit decomposition

A point of `T_c` has a unique canonical digit string, whose shallowest digit —
index `k`, value `β` — partitions the support.  A series slice-supported on `T_c`
all of whose coefficients vanish at strings with no digit before index `R` is the
sum of its first-digit restrictions over `k < R`, `0 < β < p`. -/

/-- The points whose canonical digit string has its first (shallowest) digit at
index `k` (position `k + 1` in the paper's 1-indexed convention) with value
`β`. -/
def firstDigitSet (p : ℕ) (k β : ℕ) : Set ℚ :=
  {q : ℚ | ∃ e : ℕ →₀ ℕ, (∀ i, e i < p) ∧ q = -fracVal p e ∧
    (∀ i < k, e i = 0) ∧ e k = β}

/-- **First-digit partition**: a series slice-supported on `T_c` whose coefficients
vanish at every string with all digits at indices `≥ R` decomposes as the sum of its
first-digit restrictions over indices `k < R` and digit values `0 < β < p`. -/
theorem firstDigit_decomp {x : HahnSeries ℚ (𝔽ᵃ_[p])} {a : ℕ+} {c : ℕ}
    (hsupp : ∀ q : ℚ, x.coeff (q / (a : ℚ)) ≠ 0 → q ∈ Tc p c) (R : ℕ)
    (hdeep : ∀ e : ℕ →₀ ℕ, (∀ i, e i < p) → (∀ i < R, e i = 0) →
      x.coeff (-fracVal p e / (a : ℚ)) = 0) :
    x = ∑ k ∈ Finset.range R, ∑ β ∈ Finset.Ioo 0 p,
      hahnRestrict ((· / (a : ℚ)) '' firstDigitSet p k β) x := by
  have ha : ((a : ℕ) : ℚ) ≠ 0 := by exact_mod_cast a.pos.ne'
  refine HahnSeries.ext (funext fun s => ?_)
  simp only [HahnSeries.coeff_sum]
  by_cases h0 : x.coeff s = 0
  · rw [h0]
    refine (Finset.sum_eq_zero fun k _ => Finset.sum_eq_zero fun β _ => ?_).symm
    by_cases hks : s ∈ (· / (a : ℚ)) '' firstDigitSet p k β
    · rw [coeff_hahnRestrict_of_mem x hks, h0]
    · rw [coeff_hahnRestrict_of_notMem x hks]
  · -- the canonical string of `a·s` and its least digit index
    have hq : x.coeff (((a : ℚ) * s) / (a : ℚ)) ≠ 0 := by
      rw [mul_div_cancel_left₀ s ha]
      exact h0
    have hTc := hsupp _ hq
    obtain ⟨e, he, hesum, heq⟩ := Tc_subset_neg_fracVal p c hTc
    have hs_eq : s = -fracVal p e / (a : ℚ) := by
      rw [← heq, mul_comm, mul_div_assoc, div_self ha, mul_one]
    have he0 : e ≠ 0 := by
      rintro rfl
      rw [fracVal_zero, neg_zero] at heq
      exact absurd (heq ▸ hTc.2.2) (lt_irrefl 0)
    have hne : e.support.Nonempty := Finsupp.support_nonempty_iff.mpr he0
    set k₀ : ℕ := e.support.min' hne with hk₀
    have hk₀mem : e k₀ ≠ 0 := Finsupp.mem_support_iff.mp (e.support.min'_mem hne)
    have hk₀min : ∀ i < k₀, e i = 0 := fun i hi => by
      by_contra hi0
      exact absurd (e.support.min'_le i (Finsupp.mem_support_iff.mpr hi0)) (by omega)
    have hk₀R : k₀ < R := by
      by_contra hout
      refine h0 ?_
      rw [hs_eq]
      exact hdeep e he fun i hi => hk₀min i (by omega)
    -- a witness in any first-digit class must be the canonical string of `a·s`
    have hcanon : ∀ {q' : ℚ},
        q' / (a : ℚ) = s → ∀ {e' : ℕ →₀ ℕ}, (∀ i, e' i < p) → q' = -fracVal p e' →
        e' = e := by
      intro q' hq's e' he' hq'eq
      refine eq_of_fracVal_eq p hp.out.one_lt he' he ?_
      have h1 : q' / (a : ℚ) = -fracVal p e / (a : ℚ) := by rw [hq's, hs_eq]
      rw [hq'eq] at h1
      field_simp at h1
      linarith [h1]
    -- collapse the double sum to the `(k₀, e k₀)` term
    have houter : ∀ k ∈ Finset.range R, k ≠ k₀ →
        (∑ β ∈ Finset.Ioo 0 p,
          (hahnRestrict ((· / (a : ℚ)) '' firstDigitSet p k β) x).coeff s) = 0 := by
      intro k _ hkne
      refine Finset.sum_eq_zero fun β hβ => ?_
      refine coeff_hahnRestrict_of_notMem x fun hmem => ?_
      obtain ⟨q', ⟨e', he', hq'eq, hfirst', hval'⟩, hq's⟩ := hmem
      obtain rfl := hcanon hq's he' hq'eq
      rcases lt_trichotomy k k₀ with hlt | heq' | hgt
      · rw [hk₀min k hlt] at hval'
        have := Finset.mem_Ioo.mp hβ
        omega
      · exact hkne heq'
      · rw [hfirst' k₀ hgt] at hk₀mem
        exact hk₀mem rfl
    have hinner : (∑ β ∈ Finset.Ioo 0 p,
        (hahnRestrict ((· / (a : ℚ)) '' firstDigitSet p k₀ β) x).coeff s)
        = x.coeff s := by
      have hβ₀mem : e k₀ ∈ Finset.Ioo 0 p :=
        Finset.mem_Ioo.mpr ⟨Nat.pos_of_ne_zero hk₀mem, he k₀⟩
      rw [Finset.sum_eq_single (e k₀)]
      · exact coeff_hahnRestrict_of_mem x
          ⟨-fracVal p e, ⟨e, he, rfl, hk₀min, rfl⟩, hs_eq.symm⟩
      · intro β _ hβne
        refine coeff_hahnRestrict_of_notMem x fun hmem => ?_
        obtain ⟨q', ⟨e', he', hq'eq, hfirst', hval'⟩, hq's⟩ := hmem
        obtain rfl := hcanon hq's he' hq'eq
        exact hβne hval'.symm
      · intro hout
        exact absurd hβ₀mem hout
    rw [Finset.sum_eq_single k₀ houter
      (fun hout => absurd (Finset.mem_range.mpr hk₀R) hout), hinner]

/-! ### First-digit shift

Multiplying the first-digit restriction `x^{(k,β)}` by the monomial
`t^{β p^{-(k+1)}/a}` erases the first digit from every exponent: the result is
slice-supported on `T_{c-β} ∪ {0}` and its width-`a` slice is `(M + k + 1, N)`-periodic
at level `c - β`.  This is the step that lowers the digit-sum level in the induction
proving algebraicity of UP series. -/

section FirstDigitShift

variable {x : HahnSeries ℚ (𝔽ᵃ_[p])} {a : ℕ+} {c : ℕ} {M N : ℕ+}

omit hp in
/-- Each digit term bounds the fractional value from below. -/
theorem term_le_fracVal (e : ℕ →₀ ℕ) (i : ℕ) :
    (e i : ℚ) * (p : ℚ) ^ (-(i + 1 : ℤ)) ≤ fracVal p e := by
  by_cases hei : e i = 0
  · rw [hei, Nat.cast_zero, zero_mul]
    exact fracVal_nonneg p e
  · rw [← fracVal_def]
    exact Finset.single_le_sum
      (f := fun j => ((e j : ℚ) * (p : ℚ) ^ (-(j + 1 : ℤ))))
      (fun j _ => by positivity) (Finsupp.mem_support_iff.mpr hei)

/-- A canonical expansion with all digits at positions `> R` has fractional value
less than `p^{-R}`. -/
theorem fracVal_lt_of_deep {e : ℕ →₀ ℕ} (he : ∀ i, e i < p) {R : ℕ}
    (hdeep : ∀ i < R, e i = 0) : fracVal p e < (p : ℚ) ^ (-(R : ℤ)) := by
  have hpq : (0 : ℚ) < (p : ℚ) := by exact_mod_cast hp.out.pos
  have hpow : (0 : ℚ) < (p : ℚ) ^ R := by positivity
  have h1 : (p : ℚ) ^ R * fracVal p e < 1 := by
    rw [← fracVal_dropGapDig_zero hdeep]
    exact fracVal_lt_one p hp.out.one_lt fun i => dropGapDig_lt p he _ _ i
  rw [zpow_neg, zpow_natCast, ← one_div, lt_div_iff₀ hpow, mul_comm]
  exact h1

/-- A canonical expansion whose digits vanish below index `k` has fractional value
less than `(e k + 1) · p^{-(k+1)}`: the first digit determines the value up to
`p^{-(k+1)}`. -/
theorem fracVal_lt_of_first_digit {e : ℕ →₀ ℕ} (he : ∀ i, e i < p) {k : ℕ}
    (hfirst : ∀ i < k, e i = 0) :
    fracVal p e < ((e k : ℚ) + 1) * (p : ℚ) ^ (-(k + 1 : ℤ)) := by
  have herase : fracVal p (e.erase k) < (p : ℚ) ^ (-(k + 1 : ℤ)) := by
    have hcast : (-(k + 1 : ℤ)) = -(((k + 1 : ℕ) : ℤ)) := by omega
    rw [hcast]
    refine fracVal_lt_of_deep (fun i => ?_) (fun i hi => ?_)
    · rcases eq_or_ne i k with rfl | hne
      · rw [Finsupp.erase_same]
        exact hp.out.pos
      · rw [Finsupp.erase_ne hne]
        exact he i
    · rcases eq_or_ne i k with rfl | hne
      · exact Finsupp.erase_same
      · rw [Finsupp.erase_ne hne]
        exact hfirst i (by omega)
  have hsplit : fracVal p e
      = fracVal p (e.erase k) + (e k : ℚ) * (p : ℚ) ^ (-(k + 1 : ℤ)) := by
    conv_lhs => rw [← Finsupp.erase_add_single k e]
    rw [fracVal_add, fracVal_single]
  have hring : ((e k : ℚ) + 1) * (p : ℚ) ^ (-(k + 1 : ℤ))
      = (e k : ℚ) * (p : ℚ) ^ (-(k + 1 : ℤ)) + (p : ℚ) ^ (-(k + 1 : ℤ)) := by ring
  rw [hsplit, hring]
  linarith

/-- Composing two full digit shifts adds the shift amounts. -/
theorem gapDig_one_gapDig_one (m n : ℕ) (dig : ℕ →₀ ℕ) :
    gapDig 1 m (gapDig 1 n dig) = gapDig 1 (m + n) dig := by
  ext i
  simp only [gapDig_apply]
  split_ifs <;> first | rfl | omega | (congr 1; omega)

/-- When every head digit vanishes, gap insertion is the full shift. -/
theorem gapDig_eq_gapDig_one_of_head_zero {j : ℕ} {dig : ℕ →₀ ℕ}
    (hhead : ∀ i < j - 1, dig i = 0) (n : ℕ) : gapDig j n dig = gapDig 1 n dig := by
  ext i
  rw [gapDig_apply, gapDig_apply]
  by_cases h1 : i < j - 1
  · rw [if_pos h1, if_neg (by omega : ¬ i < 1 - 1), hhead i h1]
    by_cases h2 : 1 - 1 + n ≤ i
    · rw [if_pos h2, hhead (i - n) (by omega)]
    · rw [if_neg h2]
  · rw [if_neg h1, if_neg (by omega : ¬ i < 1 - 1)]
    by_cases h2 : j - 1 + n ≤ i
    · rw [if_pos h2, if_pos (by omega : 1 - 1 + n ≤ i)]
    · rw [if_neg h2]
      by_cases h3 : 1 - 1 + n ≤ i
      · rw [if_pos h3, hhead (i - n) (by omega)]
      · rw [if_neg h3]

/-- Adding a digit inside the head window commutes with gap insertion. -/
theorem gapDig_add_single {j k : ℕ} (hk : k < j - 1) (n β : ℕ) (dig : ℕ →₀ ℕ) :
    gapDig j n (dig + Finsupp.single k β) = gapDig j n dig + Finsupp.single k β := by
  ext i
  simp only [gapDig_apply, Finsupp.add_apply, Finsupp.single_apply]
  split_ifs <;> first | rfl | omega

/-- Prepending a digit at index `k` to a string with all digits at positions `> k`
commutes with gap insertion at gap position `k + 2`. -/
theorem gapDig_single_add {k β : ℕ} {D : ℕ →₀ ℕ} (hD : ∀ i ≤ k, D i = 0) (m : ℕ) :
    gapDig (k + 2) m (Finsupp.single k β + D) = Finsupp.single k β + gapDig 1 m D := by
  ext i
  rcases lt_or_ge k i with hik | hik
  · have hs : Finsupp.single k β i = 0 := Finsupp.single_eq_of_ne (by omega)
    rw [Finsupp.add_apply, hs, zero_add, gapDig_apply, gapDig_apply,
      if_neg (by omega : ¬ i < k + 2 - 1), if_neg (by omega : ¬ i < 1 - 1)]
    by_cases hm : k + 2 - 1 + m ≤ i
    · rw [if_pos hm, if_pos (by omega : 1 - 1 + m ≤ i), Finsupp.add_apply,
        Finsupp.single_eq_of_ne (by omega : i - m ≠ k), zero_add]
    · rw [if_neg hm]
      by_cases hm2 : 1 - 1 + m ≤ i
      · rw [if_pos hm2, hD (i - m) (by omega)]
      · rw [if_neg hm2]
  · have hL : gapDig (k + 2) m (Finsupp.single k β + D) i
        = Finsupp.single k β i + D i := by
      rw [gapDig_apply, if_pos (by omega : i < k + 2 - 1), Finsupp.add_apply]
    have hR1 : gapDig 1 m D i = 0 := by
      rw [gapDig_apply, if_neg (by omega : ¬ i < 1 - 1)]
      by_cases hm : 1 - 1 + m ≤ i
      · rw [if_pos hm]
        exact hD (i - m) (by omega)
      · rw [if_neg hm]
    rw [hL, hD i hik, add_zero, Finsupp.add_apply, hR1, add_zero]

/-- Membership in the width-`a` rescaling of a set of exponents. -/
theorem div_mem_image_div_iff {a : ℕ+} {S : Set ℚ} {w : ℚ} :
    w / (a : ℚ) ∈ (· / (a : ℚ)) '' S ↔ w ∈ S := by
  have ha : ((a : ℕ) : ℚ) ≠ 0 := by exact_mod_cast a.pos.ne'
  constructor
  · rintro ⟨q', hq', heq⟩
    have hq'w : q' = w := by
      have h1 := congrArg (· * (a : ℚ)) heq
      simpa [div_mul_cancel₀ _ ha] using h1
    exact hq'w ▸ hq'
  · exact fun h => ⟨w, h, rfl⟩

/-- Membership in a first-digit class through a canonical expansion: the class is
detected on the digits themselves. -/
theorem neg_fracVal_mem_firstDigitSet_iff {e : ℕ →₀ ℕ} (he : ∀ i, e i < p) (k β : ℕ) :
    -fracVal p e ∈ firstDigitSet p k β ↔ (∀ i < k, e i = 0) ∧ e k = β := by
  constructor
  · rintro ⟨e', he', heq, hfirst, hval⟩
    obtain rfl : e' = e := eq_of_fracVal_eq p hp.out.one_lt he' he (neg_inj.mp heq).symm
    exact ⟨hfirst, hval⟩
  · rintro ⟨hfirst, hval⟩
    exact ⟨e, he, rfl, hfirst, hval⟩

/-- **First-digit shift**: the restriction of
`x` to the exponents whose first digit is `β` at index `k` (position `k + 1`),
multiplied by the monomial `t^{β p^{-(k+1)}/a}` that erases that digit. -/
noncomputable def firstDigitShift (a : ℕ+) (k β : ℕ) (x : HahnSeries ℚ (𝔽ᵃ_[p])) :
    HahnSeries ℚ (𝔽ᵃ_[p]) :=
  HahnSeries.single ((β : ℚ) * (p : ℚ) ^ (-(k + 1 : ℤ)) / (a : ℚ)) 1
    * hahnRestrict ((· / (a : ℚ)) '' firstDigitSet p k β) x

/-- Coefficients of the first-digit shift: read off the restricted series at the
exponent shifted back by `β p^{-(k+1)}/a`. -/
theorem coeff_firstDigitShift (a : ℕ+) (k β : ℕ) (x : HahnSeries ℚ (𝔽ᵃ_[p])) (g : ℚ) :
    (firstDigitShift a k β x).coeff g
      = (hahnRestrict ((· / (a : ℚ)) '' firstDigitSet p k β) x).coeff
          (g - (β : ℚ) * (p : ℚ) ^ (-(k + 1 : ℤ)) / (a : ℚ)) := by
  rw [firstDigitShift, HahnSeries.coeff_single_mul, one_mul]

/-- The first-digit restriction is recovered from its shift by the inverse monomial. -/
theorem single_neg_mul_firstDigitShift (a : ℕ+) (k β : ℕ) (x : HahnSeries ℚ (𝔽ᵃ_[p])) :
    HahnSeries.single (-((β : ℚ) * (p : ℚ) ^ (-(k + 1 : ℤ)) / (a : ℚ))) 1
        * firstDigitShift a k β x
      = hahnRestrict ((· / (a : ℚ)) '' firstDigitSet p k β) x := by
  rw [firstDigitShift, ← mul_assoc, HahnSeries.single_mul_single, neg_add_cancel,
    mul_one, HahnSeries.single_zero_one, one_mul]

/-- **First-digit shift, support**: erasing a first digit `β` lowers the digit-sum
level by `β`; the exponent `0` appears when the erased digit was the whole string. -/
theorem firstDigitShift_support
    (hsupp : ∀ q : ℚ, x.coeff (q / (a : ℚ)) ≠ 0 → q ∈ Tc p c) (k β : ℕ) (q : ℚ)
    (hq : (firstDigitShift a k β x).coeff (q / (a : ℚ)) ≠ 0) :
    q ∈ Tc p (c - β) ∪ {0} := by
  rw [coeff_firstDigitShift, show q / (a : ℚ) - (β : ℚ) * (p : ℚ) ^ (-(k + 1 : ℤ)) / (a : ℚ)
      = (q - (β : ℚ) * (p : ℚ) ^ (-(k + 1 : ℤ))) / (a : ℚ) by ring] at hq
  by_cases hmem : (q - (β : ℚ) * (p : ℚ) ^ (-(k + 1 : ℤ))) / (a : ℚ)
      ∈ (· / (a : ℚ)) '' firstDigitSet p k β
  · rw [coeff_hahnRestrict_of_mem x hmem] at hq
    rw [div_mem_image_div_iff] at hmem
    obtain ⟨e, he, heq, hfirst, hval⟩ := hmem
    have hTc := hsupp _ hq
    obtain ⟨e₂, he₂, hsum₂, heq₂⟩ := Tc_subset_neg_fracVal p c hTc
    have hee : e₂ = e :=
      eq_of_fracVal_eq p hp.out.one_lt he₂ he (neg_inj.mp (heq₂.symm.trans heq))
    rw [hee] at hsum₂
    have hsplit : fracVal p e
        = fracVal p (e.erase k) + (β : ℚ) * (p : ℚ) ^ (-(k + 1 : ℤ)) := by
      conv_lhs => rw [← Finsupp.erase_add_single k e]
      rw [fracVal_add, fracVal_single, hval]
    have hq_eq : q = -fracVal p (e.erase k) := by linarith [heq, hsplit]
    by_cases he0 : e.erase k = 0
    · right
      rw [Set.mem_singleton_iff, hq_eq, he0, fracVal_zero, neg_zero]
    · left
      rw [hq_eq]
      refine neg_fracVal_mem_Tc (fun i => ?_) ?_ he0
      · rcases eq_or_ne i k with rfl | hne
        · rw [Finsupp.erase_same]
          exact hp.out.pos
        · rw [Finsupp.erase_ne hne]
          exact he i
      · have hsum_split : (e.sum fun _ v => v)
            = ((e.erase k).sum fun _ v => v) + e k := by
          conv_lhs => rw [← Finsupp.erase_add_single k e]
          rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl),
            Finsupp.sum_single_index rfl]
        omega
  · rw [coeff_hahnRestrict_of_notMem x hmem] at hq
    exact absurd rfl hq

/-- **First-digit shift, slice periodicity**: the width-`a` slice of the first-digit
shift is `(M + k + 1, N)`-periodic at level `c - β`.  Twist strings with a digit at an
index `≤ k` give identically vanishing sequences (their evaluation points escape the
first-digit class); a gap beyond `k` absorbs the digit `β` into the head; a shallow gap
rebases the string at gap position `k + 2`, shifting the depth by `k + 2 - j`. -/
theorem firstDigitShift_slice_periodic
    (hper : IsTwistPeriodic p (fun z => x.coeff (z / (a : ℚ))) c M N)
    {k β : ℕ} (hβp : β < p) (hβc : β ≤ c) {P : ℕ+}
    (hP : (M : ℕ) + k + 1 ≤ (P : ℕ)) :
    IsTwistPeriodic p (fun z => (firstDigitShift a k β x).coeff (z / (a : ℚ)))
      (c - β) P N := by
  have hpq : (0 : ℚ) < (p : ℚ) := by exact_mod_cast hp.out.pos
  intro j dig hj hdig hsum n hn
  have hMP := M.pos
  -- Every term is the restricted coefficient at the `β`-augmented digit string.
  have hterm : ∀ n' : ℕ,
      twistSeq p (fun z => (firstDigitShift a k β x).coeff (z / (a : ℚ))) j dig n'
        = (hahnRestrict ((· / (a : ℚ)) '' firstDigitSet p k β) x).coeff
            (-fracVal p (gapDig j n' dig + Finsupp.single k β) / (a : ℚ)) := by
    intro n'
    rw [twistSeq_eq_neg_fracVal_gapDig]
    simp only [coeff_firstDigitShift]
    congr 1
    rw [fracVal_add, fracVal_single]
    ring
  by_cases hA : ∃ i, i < j - 1 ∧ i ≤ k ∧ dig i ≠ 0
  · -- A head digit at index `≤ k`: every evaluation point escapes the class.
    obtain ⟨i, hij, hik, hi0⟩ := hA
    have hzero : ∀ n' : ℕ,
        (hahnRestrict ((· / (a : ℚ)) '' firstDigitSet p k β) x).coeff
          (-fracVal p (gapDig j n' dig + Finsupp.single k β) / (a : ℚ)) = 0 := by
      intro n'
      refine coeff_hahnRestrict_of_notMem x fun hmem => ?_
      rw [div_mem_image_div_iff] at hmem
      obtain ⟨e', he', heq, hfirst, hval⟩ := hmem
      have heqv : fracVal p (gapDig j n' dig + Finsupp.single k β) = fracVal p e' :=
        neg_inj.mp heq
      have hupper : fracVal p e' < ((β : ℚ) + 1) * (p : ℚ) ^ (-(k + 1 : ℤ)) := by
        have h := fracVal_lt_of_first_digit he' hfirst
        rwa [hval] at h
      have hlower : ((β : ℚ) + 1) * (p : ℚ) ^ (-(k + 1 : ℤ))
          ≤ fracVal p (gapDig j n' dig + Finsupp.single k β) := by
        rcases eq_or_lt_of_le hik with heqik | hik'
        · -- the head digit sits at index `k`: the digit there is `dig k + β ≥ β + 1`
          have hijk : k < j - 1 := heqik ▸ hij
          have hi0k : dig k ≠ 0 := heqik ▸ hi0
          have hEk : (gapDig j n' dig + Finsupp.single k β) k = dig k + β := by
            rw [Finsupp.add_apply, gapDig_apply, if_pos hijk, Finsupp.single_eq_same]
          calc ((β : ℚ) + 1) * (p : ℚ) ^ (-(k + 1 : ℤ))
              ≤ ((dig k + β : ℕ) : ℚ) * (p : ℚ) ^ (-(k + 1 : ℤ)) := by
                have h0 : 1 ≤ dig k := Nat.one_le_iff_ne_zero.mpr hi0k
                have h1 : ((β : ℚ) + 1) ≤ ((dig k + β : ℕ) : ℚ) := by
                  push_cast
                  have h0' : (1 : ℚ) ≤ (dig k : ℚ) := by exact_mod_cast h0
                  linarith
                have h2 : (0 : ℚ) < (p : ℚ) ^ (-(k + 1 : ℤ)) := zpow_pos hpq _
                nlinarith
            _ ≤ fracVal p (gapDig j n' dig + Finsupp.single k β) := by
                rw [← hEk]
                exact term_le_fracVal _ k
        · -- the head digit sits strictly below `k`
          have hEi : (gapDig j n' dig + Finsupp.single k β) i = dig i := by
            rw [Finsupp.add_apply, gapDig_apply, if_pos hij,
              Finsupp.single_eq_of_ne (by omega), add_zero]
          have hzk : (p : ℚ) ^ (-(i + 1 : ℤ))
              = (p : ℚ) ^ (k - i : ℕ) * (p : ℚ) ^ (-(k + 1 : ℤ)) := by
            rw [← zpow_natCast (p : ℚ) (k - i), ← zpow_add₀ hpq.ne']
            congr 1
            omega
          have hpk : ((β : ℚ) + 1) ≤ (p : ℚ) ^ (k - i : ℕ) := by
            calc ((β : ℚ) + 1) ≤ (p : ℚ) := by exact_mod_cast hβp
              _ ≤ (p : ℚ) ^ (k - i : ℕ) :=
                  le_self_pow₀ (by exact_mod_cast hp.out.one_le) (by omega)
          have hdig1 : (1 : ℚ) ≤ (dig i : ℚ) :=
            by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hi0
          have h2 : (0 : ℚ) < (p : ℚ) ^ (-(k + 1 : ℤ)) := zpow_pos hpq _
          calc ((β : ℚ) + 1) * (p : ℚ) ^ (-(k + 1 : ℤ))
              ≤ (p : ℚ) ^ (k - i : ℕ) * (p : ℚ) ^ (-(k + 1 : ℤ)) := by nlinarith
            _ = (p : ℚ) ^ (-(i + 1 : ℤ)) := hzk.symm
            _ ≤ (dig i : ℚ) * (p : ℚ) ^ (-(i + 1 : ℤ)) := by
                have h3 : (0 : ℚ) < (p : ℚ) ^ (-(i + 1 : ℤ)) := zpow_pos hpq _
                nlinarith
            _ ≤ fracVal p (gapDig j n' dig + Finsupp.single k β) := by
                rw [show (dig i : ℚ)
                    = (((gapDig j n' dig + Finsupp.single k β) i : ℕ) : ℚ) by rw [hEi]]
                exact term_le_fracVal _ i
      linarith
    rw [hterm, hterm, hzero, hzero]
  · push Not at hA
    -- No head digit at index `≤ k`: for a deep enough gap the evaluation point lies in
    -- the class, with canonical string the `β`-augmented one.
    have hgap0 : ∀ n', k + 1 ≤ n' → ∀ i, i ≤ k → gapDig j n' dig i = 0 := by
      intro n' hn' i hik
      rw [gapDig_apply]
      by_cases h1 : i < j - 1
      · rw [if_pos h1]
        exact hA i h1 hik
      · rw [if_neg h1, if_neg (by omega)]
    have hxterm : ∀ n', k + 1 ≤ n' →
        twistSeq p (fun z => (firstDigitShift a k β x).coeff (z / (a : ℚ))) j dig n'
          = x.coeff (-fracVal p (gapDig j n' dig + Finsupp.single k β) / (a : ℚ)) := by
      intro n' hn'
      rw [hterm n']
      refine coeff_hahnRestrict_of_mem x ⟨_, ⟨_, fun i => ?_, rfl, fun i hik => ?_, ?_⟩, rfl⟩
      · rcases eq_or_ne i k with rfl | hne
        · rw [Finsupp.add_apply, hgap0 n' hn' i le_rfl, Finsupp.single_eq_same, zero_add]
          exact hβp
        · rw [Finsupp.add_apply, Finsupp.single_eq_of_ne hne, add_zero]
          exact gapDig_lt p hdig hp.out.pos _ _ _
      · rw [Finsupp.add_apply, hgap0 n' hn' i (by omega),
          Finsupp.single_eq_of_ne (by omega), add_zero]
      · rw [Finsupp.add_apply, hgap0 n' hn' k le_rfl, Finsupp.single_eq_same, zero_add]
    by_cases hjk : k < j - 1
    · -- Gap beyond `k`: the digit `β` joins the head window.
      have hd'' : ∀ i, (dig + Finsupp.single k β) i < p := by
        intro i
        rcases eq_or_ne i k with rfl | hne
        · rw [Finsupp.add_apply, hA i hjk le_rfl, Finsupp.single_eq_same, zero_add]
          exact hβp
        · rw [Finsupp.add_apply, Finsupp.single_eq_of_ne hne, add_zero]
          exact hdig i
      have hsum'' : ((dig + Finsupp.single k β).sum fun _ v => v) ≤ c := by
        rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl),
          Finsupp.sum_single_index rfl]
        omega
      have hxx : ∀ n', k + 1 ≤ n' →
          twistSeq p (fun z => (firstDigitShift a k β x).coeff (z / (a : ℚ))) j dig n'
            = twistSeq p (fun z => x.coeff (z / (a : ℚ))) j (dig + Finsupp.single k β)
                n' := by
        intro n' hn'
        rw [hxterm n' hn', twistSeq_eq_neg_fracVal_gapDig, gapDig_add_single hjk]
      rw [hxx (n + ↑N) (by omega), hxx n (by omega)]
      exact hper j _ hj hd'' hsum'' n (by omega)
    · -- Shallow gap: rebase the string at gap position `k + 2`, shifting the depth.
      have hhead : ∀ i < j - 1, dig i = 0 := fun i hi => hA i hi (by omega)
      have hD0 : ∀ i ≤ k, gapDig 1 (k + 2 - j) dig i = 0 := by
        intro i hik
        rw [gapDig_apply, if_neg (by omega)]
        by_cases hm : 1 - 1 + (k + 2 - j) ≤ i
        · rw [if_pos hm]
          exact hhead (i - (k + 2 - j)) (by omega)
        · rw [if_neg hm]
      have hkey : ∀ n', k + 1 ≤ n' →
          gapDig j n' dig + Finsupp.single k β
            = gapDig (k + 2) (n' - (k + 2 - j))
                (Finsupp.single k β + gapDig 1 (k + 2 - j) dig) := by
        intro n' hn'
        rw [gapDig_single_add hD0, gapDig_one_gapDig_one,
          show n' - (k + 2 - j) + (k + 2 - j) = n' by omega,
          gapDig_eq_gapDig_one_of_head_zero hhead, add_comm]
      have hd' : ∀ i, (Finsupp.single k β + gapDig 1 (k + 2 - j) dig) i < p := by
        intro i
        rcases eq_or_ne i k with rfl | hne
        · rw [Finsupp.add_apply, hD0 i le_rfl, Finsupp.single_eq_same, add_zero]
          exact hβp
        · rw [Finsupp.add_apply, Finsupp.single_eq_of_ne hne, zero_add]
          exact gapDig_lt p hdig hp.out.pos _ _ _
      have hsum' : ((Finsupp.single k β + gapDig 1 (k + 2 - j) dig).sum
          fun _ v => v) ≤ c := by
        rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl),
          Finsupp.sum_single_index rfl, gapDig_sum]
        omega
      have hxx : ∀ n', k + 1 ≤ n' →
          twistSeq p (fun z => (firstDigitShift a k β x).coeff (z / (a : ℚ))) j dig n'
            = twistSeq p (fun z => x.coeff (z / (a : ℚ))) (k + 2)
                (Finsupp.single k β + gapDig 1 (k + 2 - j) dig) (n' - (k + 2 - j)) := by
        intro n' hn'
        rw [hxterm n' hn', hkey n' hn', twistSeq_eq_neg_fracVal_gapDig]
      rw [hxx (n + ↑N) (by omega), hxx n (by omega),
        show n + ↑N - (k + 2 - j) = n - (k + 2 - j) + ↑N by omega]
      exact hper (k + 2) _ (by omega) hd' hsum' (n - (k + 2 - j)) (by omega)

end FirstDigitShift

end TrustworthyKedlaya.UP
