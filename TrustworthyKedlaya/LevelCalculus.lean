/-
Copyright (c) 2026 Shanwen Wang, Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import TrustworthyKedlaya.FrobeniusUP
public import TrustworthyKedlaya.FiniteImage

/-!
# Dismantling a UP series along digit-sum levels

The level-`c` induction that proves algebraicity of UP series (`lem:up-algebraic`)
dismantles a series along the *levels* of its exponents: for an exponent `s` written as
`as = m - w` with `m ∈ ℤ` and `w ∈ [0,1)`, the level is the digit sum of the canonical
base-`p` expansion of `w`.  The exponents of level `≤ c'` inside `S_{a,b,c}` are exactly
the points of `S_{a,b,c'}` (canonical expansions are unique), so level restriction is
Hahn-series restriction (`hahnRestrict`) to a smaller support set.

## Main statements

- `TrustworthyKedlaya.UP.SliceWitness.levelRestrict`: restricting a UP series to the
  exponents of level at most `c' ≤ c` preserves the UP data, lowering the level to `c'`
  (blueprint `lem:up-level-restrict`).

## References

- K. S. Kedlaya, *The algebraic closure of the power series field in positive
  characteristic*, Proc. Amer. Math. Soc. 129 (2001) [Ked01a], proof of Theorem 8.
-/

@[expose] public section

namespace TrustworthyKedlaya.UP

variable {p : ℕ} [hp : Fact (Nat.Prime p)]

/-- **Level restriction** (blueprint `lem:up-level-restrict`): if `x` is UP, presented
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

/-- Pushing all digits `L` positions deeper divides the fractional value by `p^L`. -/
theorem fracVal_gapDig_one (L : ℕ) (E : ℕ →₀ ℕ) :
    fracVal p (gapDig 1 L E) = (p : ℚ) ^ (-(L : ℤ)) * fracVal p E := by
  have hfv := fracVal_gapDig_split (p := p) 1 L E
  have h1 : (1 : ℕ) - 1 = 0 := rfl
  rw [h1] at hfv
  simp only [Nat.not_lt_zero, Nat.zero_le] at hfv
  rw [(Finsupp.filter_eq_zero_iff _ _).mpr fun x hx => hx.elim,
    (Finsupp.filter_eq_self_iff _ _).mpr fun x _ => trivial, fracVal_zero, zero_add] at hfv
  exact hfv

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

end TrustworthyKedlaya.UP
