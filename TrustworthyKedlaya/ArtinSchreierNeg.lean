/-
Copyright (c) 2026 Shanwen Wang, Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import TrustworthyKedlaya.FiniteImage
public import TrustworthyKedlaya.Frobenius
public import TrustworthyKedlaya.Rescale
public import Mathlib.Algebra.BigOperators.Finprod

/-!
# Artin-Schreier roots of negatively supported UP series

For `y` uniformly periodic with support in `S_{a,b,c} ∩ (-∞, 0)`, the series
`x = ∑_i t^i ∑_{n ≥ 1} (y_{i p^n})^{1/p^n}` is a well-defined Hahn series supported on
`S_{a,b,b+c} ∩ (-∞, 0)`, satisfies `x^p - x = y`, and is again uniformly periodic
(Kedlaya (2001a), part of the proof of Lemma 4; `lem:as-root-neg` of the blueprint).

The uniform periodicity is the hard kernel of the whole Theorem-15 route: the naive
"each twist sequence of `x` is a bounded sum of twist sequences of `y`" argument fails
(the number of contributing terms grows with the prefix depth — the error site of
Kedlaya (2017), Remark 2.7).  The correct argument couples the twist sequences of `x`
*to themselves* along the relation `x^p = x + y`:

* `(x_i)^p = x_{pi} + y_{pi}` coefficientwise, and multiplication by `p` shifts digit
  strings by one place; this couples the twist sequence of `x` at slice `m` and gap
  position `j` to the one at slice `pm - b₁` and gap position `j - 1` (same index),
  resp. at slice `pm` and gap position `1` (index shifted by one) — the two cases of
  `lem:as-twist-couple`.
* At gap position `1` and slice `0` the coupling is a Frobenius-affine recursion
  `c_{n+1}^p = c_n + y_n`, handled by the orbit lemma
  `eventually_periodic_of_frobenius_affine`.
* At gap position `1` and slices `m ≤ -1` the coupled slice `pm` moves away from `0`
  and falls below `-b` after at most `L = log_p b + 1` steps, where all slices of `x`
  and `y` vanish: a downward ladder with preperiod growing by one per step.
* At gap positions `j ≥ 2` the coupling transfers periodicity verbatim (no parameter
  growth), closing an induction on `j`.

All sequence values live in a single finite subfield `𝔽_{p^D}` (`lem:as-subfield`),
as required by the orbit lemma; the resulting uniform data is `(M + L, N·p·D)`.

## Main statements

- `TrustworthyKedlaya.UP.Sabc_mem_div_pow_of_neg`: negative elements of `S_{a,b,c}`
  divided by `p^n` land in `S_{a,b,b+c}`, uniformly in `n`.
- `TrustworthyKedlaya.UP.exists_hahn_asRoot_of_neg_support`: existence of the Hahn
  series root `x` with `x^p = x + y` and the support bounds.
- `TrustworthyKedlaya.UP.exists_uniform_subfield_slices` /
  `TrustworthyKedlaya.UP.pow_pow_eq_self_of_asPair`: the common finite subfield.
- `TrustworthyKedlaya.UP.twistSeq_couple_gap_one` /
  `TrustworthyKedlaya.UP.twistSeq_couple_gap_ge_two`: the coupling relations.
- `TrustworthyKedlaya.UP.sliceWitness_of_asPair`: the ladder — a slice witness for `x`.
- `TrustworthyKedlaya.UP.exists_artinSchreier_root_of_support_neg`: the packaged
  statement (`lem:as-root-neg`).

## References

- K. S. Kedlaya, *The algebraic closure of the power series field in positive
  characteristic*, Proc. Amer. Math. Soc. 129 (2001) [Ked01a], proof of Lemma 4.
- K. S. Kedlaya, *On the algebraicity of generalized power series*, Beiträge Algebra
  Geom. 58 (2017) [Ked17], Example 2.6 and Remark 2.7.
-/

@[expose] public section

namespace TrustworthyKedlaya.UP

variable (p : ℕ) [hp : Fact (Nat.Prime p)]

/-! ### Generic helpers -/

/-- Elements of `S_{a,b,c}` are bounded below by `-(b+1)/a`. -/
theorem neg_lt_of_mem_Sabc {a : ℕ+} {b c : ℕ} {s : ℚ} (hs : s ∈ Sabc p a b c) :
    -(((b : ℚ) + 1) / (a : ℚ)) < s := by
  obtain ⟨n, d, hn, hd, _, rfl⟩ := hs
  have ha : (0 : ℚ) < (a : ℚ) := by exact_mod_cast a.pos
  have h1 : fracVal p d < 1 := fracVal_lt_one p hp.out.one_lt hd
  have h2 : -((b : ℚ)) ≤ (n : ℚ) := by exact_mod_cast hn
  have key : -((b : ℚ) + 1) < (n : ℚ) - fracVal p d := by linarith
  calc -(((b : ℚ) + 1) / (a : ℚ)) = (1 / (a : ℚ)) * (-((b : ℚ) + 1)) := by ring
    _ < (1 / (a : ℚ)) * ((n : ℚ) - d.sum fun i v => (v : ℚ) * (p : ℚ) ^ (-(i + 1 : ℤ))) := by
        rw [fracVal_def]
        exact mul_lt_mul_of_pos_left key (by positivity)

/-- The `p^k`-th power map is injective on `𝔽̄_p`. -/
theorem pow_p_pow_left_injective (k : ℕ) :
    Function.Injective fun v : 𝔽ᵃ_[p] => v ^ p ^ k := by
  intro s t hst
  apply iterateFrobenius_inj (𝔽ᵃ_[p]) p k
  simpa only [iterateFrobenius_def] using hst

/-- Iterates of the inverse Frobenius kill zero. -/
theorem invFrobenius_iterate_zero (k : ℕ) :
    ((frobeniusEquiv (𝔽ᵃ_[p]) p).symm)^[k] (0 : 𝔽ᵃ_[p]) = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply, map_zero, ih]

/-- Slices `m < -b` of a series supported in `S_{a,b,c}` vanish at every canonical
digit evaluation point (uniqueness of canonical representations). -/
theorem coeff_slice_eq_zero_of_slice_lt {x : HahnSeries ℚ (𝔽ᵃ_[p])} {a : ℕ+} {b c : ℕ}
    (hsupp : x.support ⊆ Sabc p a b c) {m : ℤ} (hm : m < -(b : ℤ)) {e : ℕ →₀ ℕ}
    (he : ∀ i, e i < p) :
    x.coeff (((m : ℚ) + -fracVal p e) / (a : ℚ)) = 0 := by
  by_contra h0
  have hmem := hsupp ((HahnSeries.mem_support _ _).mpr h0)
  rw [show ((m : ℚ) + -fracVal p e) / (a : ℚ)
      = (1 / (a : ℚ)) * ((m : ℚ) - fracVal p e) by ring] at hmem
  have := (Sabc_mem_canonical p he hmem).1
  omega

/-- Positive slices of a negatively supported series vanish at every canonical digit
evaluation point. -/
theorem coeff_slice_eq_zero_of_pos_slice {x : HahnSeries ℚ (𝔽ᵃ_[p])} {a : ℕ+}
    (hneg : x.support ⊆ Set.Iio 0) {m : ℤ} (hm : 1 ≤ m) {e : ℕ →₀ ℕ}
    (he : ∀ i, e i < p) :
    x.coeff (((m : ℚ) + -fracVal p e) / (a : ℚ)) = 0 := by
  by_contra h0
  have hmem := hneg ((HahnSeries.mem_support _ _).mpr h0)
  rw [Set.mem_Iio] at hmem
  have h1 : fracVal p e < 1 := fracVal_lt_one p hp.out.one_lt he
  have h2 : (1 : ℚ) ≤ (m : ℚ) := by exact_mod_cast hm
  have ha : (0 : ℚ) < (a : ℚ) := by exact_mod_cast a.pos
  have : (0 : ℚ) < ((m : ℚ) + -fracVal p e) / (a : ℚ) := div_pos (by linarith) ha
  linarith

/-- Splitting off the zeroth term of a finite sum over `ℕ`. -/
theorem finsum_nat_eq_zero_add {M : Type*} [AddCommMonoid M] {f : ℕ → M}
    (hf : (Function.support f).Finite) :
    ∑ᶠ n, f n = f 0 + ∑ᶠ n, f (n + 1) := by
  obtain ⟨K, hK⟩ := hf.bddAbove
  have hsub : Function.support f ⊆ ↑(Finset.range (K + 1)) := fun x hx => by
    simp only [Finset.coe_range, Set.mem_Iio]
    exact Nat.lt_succ_of_le (hK hx)
  have hsub' : Function.support (fun n => f (n + 1)) ⊆ ↑(Finset.range K) := fun x hx => by
    simp only [Finset.coe_range, Set.mem_Iio]
    have : x + 1 ≤ K := hK hx
    omega
  rw [finsum_eq_sum_of_support_subset _ hsub, finsum_eq_sum_of_support_subset _ hsub',
    Finset.sum_range_succ']
  exact add_comm _ _

/-! ### Division by `p^n` on negative support points -/

/-- The fractional value of a pure shift: `gapDig 1 n d` is the digit string of `d`
shifted out by `n` places. -/
theorem fracVal_gapDig_one (n : ℕ) (d : ℕ →₀ ℕ) :
    fracVal p (gapDig 1 n d) = (p : ℚ) ^ (-(n : ℤ)) * fracVal p d := by
  rw [fracVal_gapDig p hp.out.pos 1 n d]
  simp only [Nat.sub_self, Finset.range_zero, Finset.sum_empty, zero_add]
  congr 1
  rw [show (d.support.filter fun i => 1 - 1 ≤ i) = d.support from
    Finset.filter_true_of_mem fun i _ => Nat.zero_le i]
  rfl

/-- **Division by `p^n` on negative support points**: a negative element of
`S_{a,b,c}` divided by `p^n` lies in `S_{a,b,b+c}`, uniformly in `n`.  The integer
part (of size at most `b`) shifts into the fractional digit string, raising the
digit-sum level by at most `b`. -/
theorem Sabc_mem_div_pow_of_neg {a : ℕ+} {b c : ℕ} {s : ℚ}
    (hs : s ∈ Sabc p a b c) (hs0 : s < 0) (n : ℕ) :
    s / (p : ℚ) ^ n ∈ Sabc p a b (b + c) := by
  obtain ⟨m, d, hm, hd, hsum, rfl⟩ := hs
  have hp1 : (1 : ℚ) < (p : ℚ) := by exact_mod_cast hp.out.one_lt
  have ha : (0 : ℚ) < (a : ℚ) := by exact_mod_cast a.pos
  have hw1 : fracVal p d < 1 := fracVal_lt_one p hp.out.one_lt hd
  have hw0 : 0 ≤ fracVal p d := fracVal_nonneg p d
  -- from `s < 0`: the integer part is nonpositive
  have hm0 : m ≤ 0 := by
    by_contra hcon
    have h1 : (1 : ℚ) ≤ (m : ℚ) := by exact_mod_cast (by omega : (1 : ℤ) ≤ m)
    have h2 : (0 : ℚ) < (1 / (a : ℚ)) * ((m : ℚ) - fracVal p d) := by
      apply mul_pos (by positivity)
      rw [fracVal_def] at *
      linarith
    rw [fracVal_def] at hs0
    linarith
  cases n with
  | zero =>
    simpa using Sabc_mono p a le_rfl (Nat.le_add_left c b) ⟨m, d, hm, hd, hsum, rfl⟩
  | succ n =>
    set m' : ℕ := (-m).toNat with hm'def
    have hm'b : m' ≤ b := by omega
    have hmcast : (m : ℚ) = -(m' : ℚ) := by
      have hmz : m = -(((-m).toNat : ℤ)) := by omega
      rw [hm'def]
      exact_mod_cast hmz
    -- the pseudo-expansion: one digit `m'` at position `n` plus the digits of `d`
    -- shifted out by `n + 1` places
    set e : ℕ →₀ ℕ := Finsupp.single n m' + gapDig 1 (n + 1) d with hedef
    have heval : fracVal p e = (p : ℚ) ^ (-(n + 1 : ℤ)) * ((m' : ℚ) + fracVal p d) := by
      rw [hedef, fracVal_add, fracVal_single, fracVal_gapDig_one,
        show (-((n + 1 : ℕ) : ℤ)) = -((n : ℤ) + 1) by push_cast; ring]
      ring
    have hesum : (e.sum fun _ v => v) = m' + d.sum fun _ v => v := by
      rw [hedef, Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl),
        Finsupp.sum_single_index rfl, gapDig_sum]
    obtain ⟨k, dd, hdd, hsumdd, hval⟩ := exists_carry_normalization p e
    have hpow_pos : (0 : ℚ) < (p : ℚ) ^ (n + 1 : ℕ) := by positivity
    have hpow_ge : (1 : ℚ) ≤ (p : ℚ) ^ (n + 1 : ℕ) := one_le_pow₀ hp1.le
    have hzpow : (p : ℚ) ^ (-(n + 1 : ℤ)) = ((p : ℚ) ^ (n + 1 : ℕ))⁻¹ := by
      rw [zpow_neg, ← zpow_natCast]
      norm_num
    -- the carry is at most `b`
    have hkb : k ≤ b := by
      have h1 : (k : ℚ) ≤ fracVal p e := by
        rw [hval]
        have := fracVal_nonneg p dd
        linarith
      have h2 : fracVal p e ≤ (m' : ℚ) + fracVal p d := by
        rw [heval, hzpow]
        rw [inv_mul_le_iff₀ hpow_pos]
        have hm'0 : (0 : ℚ) ≤ (m' : ℚ) + fracVal p d := by positivity
        nlinarith
      have h3 : (k : ℚ) < (b : ℚ) + 1 := by
        have : (m' : ℚ) ≤ (b : ℚ) := by exact_mod_cast hm'b
        linarith
      exact_mod_cast Nat.lt_succ_iff.mp (by exact_mod_cast h3)
    refine ⟨-k, dd, by omega, hdd, ?_, ?_⟩
    · -- digit-sum level
      have h4 := hsumdd
      rw [hesum] at h4
      omega
    · -- the value
      have hkey : fracVal p e = (k : ℚ) + fracVal p dd := hval
      rw [heval] at hkey
      rw [show ((-k : ℤ) : ℚ) = -(k : ℚ) by push_cast; ring, fracVal_def, fracVal_def]
      rw [div_eq_iff (by positivity : ((p : ℚ) ^ (n + 1 : ℕ)) ≠ 0)]
      have hzp : (p : ℚ) ^ (-(n + 1 : ℤ)) * (p : ℚ) ^ (n + 1 : ℕ) = 1 := by
        rw [hzpow]
        field_simp
      calc (1 / (a : ℚ)) * ((m : ℚ) - fracVal p d)
          = -((1 / (a : ℚ)) * ((m' : ℚ) + fracVal p d)) := by rw [hmcast]; ring
        _ = -((1 / (a : ℚ)) * (((p : ℚ) ^ (-(n + 1 : ℤ)) * ((m' : ℚ) + fracVal p d))
              * (p : ℚ) ^ (n + 1 : ℕ))) := by
            rw [show (p : ℚ) ^ (-(n + 1 : ℤ)) * ((m' : ℚ) + fracVal p d)
                  * (p : ℚ) ^ (n + 1 : ℕ)
                = ((m' : ℚ) + fracVal p d)
                  * ((p : ℚ) ^ (-(n + 1 : ℤ)) * (p : ℚ) ^ (n + 1 : ℕ)) by ring, hzp,
              mul_one]
        _ = -((1 / (a : ℚ)) * (((k : ℚ) + fracVal p dd) * (p : ℚ) ^ (n + 1 : ℕ))) := by
            rw [hkey]
        _ = (1 / (a : ℚ)) * (-(k : ℚ) - fracVal p dd) * (p : ℚ) ^ (n + 1 : ℕ) := by ring

/-! ### Construction of the root -/

/-- The coefficient family of the candidate Artin-Schreier root at exponent `i`:
`n ↦ (y_{i·p^n})^{1/p^n}` (the root is `x_i = ∑_{n ≥ 1}` of these). -/
noncomputable def asRootTerm (y : HahnSeries ℚ (𝔽ᵃ_[p])) (i : ℚ) (n : ℕ) : 𝔽ᵃ_[p] :=
  ((frobeniusEquiv (𝔽ᵃ_[p]) p).symm)^[n] (y.coeff (i * (p : ℚ) ^ n))

/-- A term vanishes exactly when the sampled coefficient of `y` does. -/
theorem asRootTerm_eq_zero_iff {y : HahnSeries ℚ (𝔽ᵃ_[p])} {i : ℚ} {n : ℕ} :
    asRootTerm p y i n = 0 ↔ y.coeff (i * (p : ℚ) ^ n) = 0 := by
  constructor
  · intro h
    have := congrArg (fun v => v ^ p ^ n) h
    simpa only [asRootTerm, iterate_frobeniusEquiv_symm_pow_p_pow,
      zero_pow (pow_ne_zero n hp.out.ne_zero)] using this
  · intro h
    rw [asRootTerm, h, invFrobenius_iterate_zero]

/-- Only finitely many terms of the root family are nonzero, at every exponent `i`. -/
theorem asRootTerm_support_finite {y : HahnSeries ℚ (𝔽ᵃ_[p])} {a : ℕ+} {b c : ℕ}
    (hsupp : y.support ⊆ Sabc p a b c) (hneg : y.support ⊆ Set.Iio 0) (i : ℚ) :
    (Function.support (asRootTerm p y i)).Finite := by
  have hp1 : (1 : ℚ) < (p : ℚ) := by exact_mod_cast hp.out.one_lt
  rcases le_or_gt 0 i with hi | hi
  · -- nonnegative exponents sample `y` at nonnegative points: all terms vanish
    convert Set.finite_empty
    ext n
    simp only [Function.mem_support, Set.mem_empty_iff_false, iff_false, not_not]
    rw [asRootTerm_eq_zero_iff]
    by_contra h0
    have := hneg ((HahnSeries.mem_support _ _).mpr h0)
    rw [Set.mem_Iio] at this
    have hpn : (0 : ℚ) < (p : ℚ) ^ n := by positivity
    nlinarith
  · -- negative exponents escape the support bound for large `n`
    obtain ⟨K, hK⟩ := pow_unbounded_of_one_lt ((((b : ℚ) + 1) / (a : ℚ)) / (-i)) hp1
    apply Set.Finite.subset (Set.finite_Iio K)
    intro n hn
    rw [Function.mem_support] at hn
    have hcoeff : y.coeff (i * (p : ℚ) ^ n) ≠ 0 := fun h0 =>
      hn (asRootTerm_eq_zero_iff p |>.mpr h0)
    have hlow := neg_lt_of_mem_Sabc p (hsupp ((HahnSeries.mem_support _ _).mpr hcoeff))
    have hipos : (0 : ℚ) < -i := by linarith
    have hQ : (0 : ℚ) < ((b : ℚ) + 1) / (a : ℚ) := by positivity
    have h1 : (-i) * (p : ℚ) ^ n < ((b : ℚ) + 1) / (a : ℚ) := by linarith
    have h2 : (p : ℚ) ^ n < (((b : ℚ) + 1) / (a : ℚ)) / (-i) := by
      rw [lt_div_iff₀ hipos]
      linarith [h1]
    have h3 : (p : ℚ) ^ n < (p : ℚ) ^ K := h2.trans hK
    have h4 : n < K := by
      by_contra hcon
      exact absurd (pow_le_pow_right₀ hp1.le (not_lt.mp hcon)) (not_le.mpr h3)
    exact Set.mem_Iio.mpr h4

/-- **Existence of the Hahn-series Artin-Schreier root**: for `y` supported in
`S_{a,b,c} ∩ (-∞,0)` there is a Hahn series `x` supported in `S_{a,b,b+c} ∩ (-∞,0)`
with `x^p = x + y` — the series `x = ∑_i t^i ∑_{n ≥ 1} (y_{i·p^n})^{1/p^n}`. -/
theorem exists_hahn_asRoot_of_neg_support {y : HahnSeries ℚ (𝔽ᵃ_[p])} {a : ℕ+} {b c : ℕ}
    (hsupp : y.support ⊆ Sabc p a b c) (hneg : y.support ⊆ Set.Iio 0) :
    ∃ x : HahnSeries ℚ (𝔽ᵃ_[p]), x ^ p = x + y ∧
      x.support ⊆ Sabc p a b (b + c) ∧ x.support ⊆ Set.Iio 0 := by
  have hpq : ((p : ℚ)) ≠ 0 := by exact_mod_cast hp.out.pos.ne'
  -- the coefficient function
  set F : ℚ → 𝔽ᵃ_[p] := fun i => ∑ᶠ n : ℕ, asRootTerm p y i (n + 1) with hF
  -- its support properties
  have hFsuppSabc : ∀ i, F i ≠ 0 → i ∈ Sabc p a b (b + c) ∧ i < 0 := by
    intro i hi
    have hex : ∃ n : ℕ, asRootTerm p y i (n + 1) ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hi (finsum_eq_zero_of_forall_eq_zero hall)
    obtain ⟨n, hn⟩ := hex
    have hcoeff : y.coeff (i * (p : ℚ) ^ (n + 1)) ≠ 0 := fun h0 =>
      hn (asRootTerm_eq_zero_iff p |>.mpr h0)
    have hmem := hsupp ((HahnSeries.mem_support _ _).mpr hcoeff)
    have hmemneg := hneg ((HahnSeries.mem_support _ _).mpr hcoeff)
    rw [Set.mem_Iio] at hmemneg
    have hpn : (0 : ℚ) < (p : ℚ) ^ (n + 1) := by positivity
    have hidiv : i = (i * (p : ℚ) ^ (n + 1)) / (p : ℚ) ^ (n + 1) := by
      field_simp
    constructor
    · rw [hidiv]
      exact Sabc_mem_div_pow_of_neg p hmem hmemneg (n + 1)
    · nlinarith
  have hFpwo : (Function.support F).IsPWO :=
    (Sabc_isPWO p a b (b + c)).mono fun i hi => (hFsuppSabc i hi).1
  set x : HahnSeries ℚ (𝔽ᵃ_[p]) := ⟨F, hFpwo⟩ with hx
  have hxcoeff : ∀ i, x.coeff i = ∑ᶠ n : ℕ, asRootTerm p y i (n + 1) := fun _ => rfl
  -- the key coefficientwise relation
  have hkey : ∀ g : ℚ, (x.coeff g) ^ p
      = x.coeff ((p : ℚ) * g) + y.coeff ((p : ℚ) * g) := by
    intro g
    -- the family at exponent `p·g` with the plain iterate index; the term of `x_g` at
    -- `n + 1` and the term of the family at `n` sample `y` at the same point
    set G : ℕ → 𝔽ᵃ_[p] := asRootTerm p y ((p : ℚ) * g) with hG
    have hpoint : ∀ n : ℕ, g * (p : ℚ) ^ (n + 1) = ((p : ℚ) * g) * (p : ℚ) ^ n :=
      fun n => by ring
    have hGfin : (Function.support G).Finite := asRootTerm_support_finite p hsupp hneg _
    obtain ⟨K, hK⟩ := hGfin.bddAbove
    have hGsub : Function.support G ⊆ ↑(Finset.range (K + 1)) := fun x hx => by
      simp only [Finset.coe_range, Set.mem_Iio]
      exact Nat.lt_succ_of_le (hK hx)
    have hTsub : Function.support (fun n => asRootTerm p y g (n + 1))
        ⊆ ↑(Finset.range (K + 1)) := by
      intro n hn
      rw [Function.mem_support] at hn
      refine hGsub (Function.mem_support.mpr fun h0 => hn ?_)
      rw [hG, asRootTerm_eq_zero_iff, ← hpoint n] at h0
      exact asRootTerm_eq_zero_iff p |>.mpr h0
    -- termwise `p`-th powers step the iterate index down by one
    have hterm : ∀ n : ℕ, (asRootTerm p y g (n + 1)) ^ p = G n := by
      intro n
      rw [asRootTerm, Function.iterate_succ_apply', frobeniusEquiv_symm_pow_p,
        hpoint n, hG, asRootTerm]
    calc (x.coeff g) ^ p
        = (∑ n ∈ Finset.range (K + 1), asRootTerm p y g (n + 1)) ^ p := by
          rw [hxcoeff g, finsum_eq_sum_of_support_subset _ hTsub]
      _ = ∑ n ∈ Finset.range (K + 1), (asRootTerm p y g (n + 1)) ^ p := by
          rw [sum_pow_char]
      _ = ∑ n ∈ Finset.range (K + 1), G n := Finset.sum_congr rfl fun n _ => hterm n
      _ = ∑ᶠ n, G n := (finsum_eq_sum_of_support_subset _ hGsub).symm
      _ = G 0 + ∑ᶠ n, G (n + 1) := finsum_nat_eq_zero_add hGfin
      _ = y.coeff ((p : ℚ) * g) + x.coeff ((p : ℚ) * g) := by
          rw [hxcoeff, hG, show asRootTerm p y ((p : ℚ) * g) 0
              = y.coeff ((p : ℚ) * g) from by
            rw [asRootTerm, Function.iterate_zero_apply, pow_zero, mul_one]]
      _ = x.coeff ((p : ℚ) * g) + y.coeff ((p : ℚ) * g) := add_comm _ _
  -- the Artin-Schreier identity
  refine ⟨x, ?_, fun i hi => (hFsuppSabc i hi).1, fun i hi =>
    Set.mem_Iio.mpr (hFsuppSabc i hi).2⟩
  ext g
  rw [coeff_pow_char, HahnSeries.coeff_add]
  have := hkey (g / (p : ℚ))
  rwa [mul_div_cancel₀ g hpq] at this

/-! ### A common finite subfield for the Artin-Schreier pair -/

/-- **All twist-point values of a width-`a` UP witness lie in one finite subfield**:
there is `D ≥ 1` such that for *every* slice `m : ℤ` and every canonical digit
expansion `e` of digit sum at most `C`, the value `y_{(m - fracVal e)/a}` is fixed by
`v ↦ v^{p^D}`.  Only slices `-b ≤ m ≤ 0` contribute values (the others vanish), and
each contributes a finite subfield by `IsTwistPeriodic.exists_uniform_subfield`. -/
theorem exists_uniform_subfield_slices {y : HahnSeries ℚ (𝔽ᵃ_[p])} {a : ℕ+} {b c : ℕ}
    {M N : ℕ+} (hsupp : y.support ⊆ Sabc p a b c) (hneg : y.support ⊆ Set.Iio 0)
    (hper : ∀ m : ℤ, -(b : ℤ) ≤ m →
      IsTwistPeriodic p (fun z => y.coeff (((m : ℚ) + z) / (a : ℚ))) c M N)
    (C : ℕ) :
    ∃ D : ℕ, 0 < D ∧ ∀ (m : ℤ) (e : ℕ →₀ ℕ), (∀ i, e i < p) → (e.sum fun _ v => v) ≤ C →
      y.coeff (((m : ℚ) + -fracVal p e) / (a : ℚ)) ^ p ^ D
        = y.coeff (((m : ℚ) + -fracVal p e) / (a : ℚ)) := by
  have hall := isTwistPeriodic_slice_upgrade p hsupp hper
  have hslice : ∀ m : ℤ, ∃ d : ℕ, 0 < d ∧ ∀ e : ℕ →₀ ℕ, (∀ i, e i < p) →
      (e.sum fun _ v => v) ≤ C →
      y.coeff (((m : ℚ) + -fracVal p e) / (a : ℚ)) ^ p ^ d
        = y.coeff (((m : ℚ) + -fracVal p e) / (a : ℚ)) := by
    intro m
    obtain ⟨d, hd0, hd⟩ := (hall C m).exists_uniform_subfield
    exact ⟨d, hd0, fun e he hsum => hd e he hsum⟩
  choose dOf hdOf0 hdOf using hslice
  refine ⟨∏ m ∈ Finset.Icc (-(b : ℤ)) 0, dOf m,
    Finset.prod_pos fun m _ => hdOf0 m, ?_⟩
  intro m e he hsum
  rcases lt_or_ge m (-(b : ℤ)) with hm | hm
  · rw [coeff_slice_eq_zero_of_slice_lt p hsupp hm he,
      zero_pow (pow_ne_zero _ hp.out.ne_zero)]
  rcases lt_or_ge 0 m with hm1 | hm1
  · rw [coeff_slice_eq_zero_of_pos_slice p hneg hm1 he,
      zero_pow (pow_ne_zero _ hp.out.ne_zero)]
  · obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem dOf (Finset.mem_Icc.mpr ⟨hm, hm1⟩)
    rw [hk]
    exact pow_pow_mul_eq_self (hdOf m e he hsum) k

/-- **Values of an Artin-Schreier root lie in the same finite subfield**: if
`x^p = x + y` with `x` supported in `S_{a,b',c'} ∩ (-∞,0)` and all twist-point values
of `y` at level `C` are fixed by `v ↦ v^{p^D}`, then so are all twist-point values of
`x` at level `C`.  Iterating `(x_i)^p = x_{pi} + y_{pi}` drives the `x`-term below the
support after finitely many steps, leaving a sum of subfield elements; injectivity of
`p`-th powers then removes the accumulated exponent. -/
theorem pow_pow_eq_self_of_asPair {x y : HahnSeries ℚ (𝔽ᵃ_[p])} {a : ℕ+} {b' c' : ℕ}
    (hAS : x ^ p = x + y)
    (hsuppx : x.support ⊆ Sabc p a b' c') (hnegx : x.support ⊆ Set.Iio 0)
    {C D : ℕ}
    (hy : ∀ (m : ℤ) (e : ℕ →₀ ℕ), (∀ i, e i < p) → (e.sum fun _ v => v) ≤ C →
      y.coeff (((m : ℚ) + -fracVal p e) / (a : ℚ)) ^ p ^ D
        = y.coeff (((m : ℚ) + -fracVal p e) / (a : ℚ))) :
    ∀ (m : ℤ) (e : ℕ →₀ ℕ), (∀ i, e i < p) → (e.sum fun _ v => v) ≤ C →
      x.coeff (((m : ℚ) + -fracVal p e) / (a : ℚ)) ^ p ^ D
        = x.coeff (((m : ℚ) + -fracVal p e) / (a : ℚ)) := by
  have hpq : ((p : ℚ)) ≠ 0 := by exact_mod_cast hp.out.pos.ne'
  -- the coefficientwise Artin-Schreier relation
  have hkey : ∀ g : ℚ, (x.coeff g) ^ p
      = x.coeff ((p : ℚ) * g) + y.coeff ((p : ℚ) * g) := by
    intro g
    have h1 := congrArg (fun z : HahnSeries ℚ (𝔽ᵃ_[p]) => z.coeff ((p : ℚ) * g)) hAS
    simp only [coeff_pow_char, HahnSeries.coeff_add] at h1
    rwa [mul_div_cancel_left₀ g hpq] at h1
  -- multiplying a twist point by `p` yields another twist point at the same level
  have hstep : ∀ (m : ℤ) (e : ℕ →₀ ℕ),
      (p : ℚ) * (((m : ℚ) + -fracVal p e) / (a : ℚ))
        = (((p * m - e 0 : ℤ) : ℚ) + -fracVal p (unshiftDig e)) / (a : ℚ) := by
    intro m e
    have h := p_mul_fracVal p hp.out.pos e
    rw [show (p : ℚ) * (((m : ℚ) + -fracVal p e) / (a : ℚ))
        = ((p : ℚ) * (m : ℚ) + -((p : ℚ) * fracVal p e)) / (a : ℚ) by ring, h]
    push_cast
    ring
  -- iteration: `v^{p^k}` is `x` at the `p^k`-multiplied point plus a subfield element
  have hiter : ∀ (k : ℕ) (m : ℤ) (e : ℕ →₀ ℕ), (∀ i, e i < p) →
      (e.sum fun _ v => v) ≤ C →
      ∃ (m' : ℤ) (e' : ℕ →₀ ℕ) (B : 𝔽ᵃ_[p]), (∀ i, e' i < p) ∧
        (e'.sum fun _ v => v) ≤ C ∧ B ^ p ^ D = B ∧
        ((p : ℚ) ^ k * (((m : ℚ) + -fracVal p e) / (a : ℚ))
          = ((m' : ℚ) + -fracVal p e') / (a : ℚ)) ∧
        x.coeff (((m : ℚ) + -fracVal p e) / (a : ℚ)) ^ p ^ k
          = x.coeff (((m' : ℚ) + -fracVal p e') / (a : ℚ)) + B := by
    intro k
    induction k with
    | zero =>
      intro m e he hsum
      exact ⟨m, e, 0, he, hsum, zero_pow (pow_ne_zero _ hp.out.ne_zero),
        by rw [pow_zero, one_mul], by rw [pow_zero, pow_one, add_zero]⟩
    | succ k ih =>
      intro m e he hsum
      have he₁lt : ∀ i, unshiftDig e i < p := fun i => he (i + 1)
      have he₁sum : ((unshiftDig e).sum fun _ v => v) ≤ C :=
        (unshiftDig_sum_le e).trans hsum
      obtain ⟨m', e', B, he', hsum', hB, hpt, hval⟩ := ih (p * m - e 0) (unshiftDig e)
        he₁lt he₁sum
      refine ⟨m', e', B + y.coeff ((((p * m - e 0 : ℤ) : ℚ)
        + -fracVal p (unshiftDig e)) / (a : ℚ)) ^ p ^ k, he', hsum', ?_, ?_, ?_⟩
      · -- subfield closure of the accumulated term
        rw [add_pow_char_pow, hB]
        congr 1
        calc (y.coeff ((((p * m - e 0 : ℤ) : ℚ)
              + -fracVal p (unshiftDig e)) / (a : ℚ)) ^ p ^ k) ^ p ^ D
            = (y.coeff ((((p * m - e 0 : ℤ) : ℚ)
              + -fracVal p (unshiftDig e)) / (a : ℚ)) ^ p ^ D) ^ p ^ k := by
              rw [← pow_mul, mul_comm (p ^ k) (p ^ D), pow_mul]
          _ = y.coeff ((((p * m - e 0 : ℤ) : ℚ)
              + -fracVal p (unshiftDig e)) / (a : ℚ)) ^ p ^ k := by
              rw [hy (p * m - e 0) (unshiftDig e) he₁lt he₁sum]
      · -- the point after `k + 1` steps
        calc (p : ℚ) ^ (k + 1) * (((m : ℚ) + -fracVal p e) / (a : ℚ))
            = (p : ℚ) ^ k * ((p : ℚ) * (((m : ℚ) + -fracVal p e) / (a : ℚ))) := by
              ring
          _ = (p : ℚ) ^ k * ((((p * m - e 0 : ℤ) : ℚ)
              + -fracVal p (unshiftDig e)) / (a : ℚ)) := by rw [hstep m e]
          _ = ((m' : ℚ) + -fracVal p e') / (a : ℚ) := hpt
      · -- the value after `k + 1` steps
        calc x.coeff (((m : ℚ) + -fracVal p e) / (a : ℚ)) ^ p ^ (k + 1)
            = (x.coeff (((m : ℚ) + -fracVal p e) / (a : ℚ)) ^ p) ^ p ^ k := by
              rw [← pow_mul, pow_succ']
          _ = (x.coeff ((((p * m - e 0 : ℤ) : ℚ)
                + -fracVal p (unshiftDig e)) / (a : ℚ))
              + y.coeff ((((p * m - e 0 : ℤ) : ℚ)
                + -fracVal p (unshiftDig e)) / (a : ℚ))) ^ p ^ k := by
              rw [hkey, hstep m e]
          _ = x.coeff ((((p * m - e 0 : ℤ) : ℚ)
                + -fracVal p (unshiftDig e)) / (a : ℚ)) ^ p ^ k
              + y.coeff ((((p * m - e 0 : ℤ) : ℚ)
                + -fracVal p (unshiftDig e)) / (a : ℚ)) ^ p ^ k := add_pow_char_pow ..
          _ = x.coeff (((m' : ℚ) + -fracVal p e') / (a : ℚ))
              + (B + y.coeff ((((p * m - e 0 : ℤ) : ℚ)
                + -fracVal p (unshiftDig e)) / (a : ℚ)) ^ p ^ k) := by
              rw [hval]
              ring
  -- conclude: escape below the support, then cancel the exponent
  intro m e he hsum
  rcases le_or_gt 0 (((m : ℚ) + -fracVal p e) / (a : ℚ)) with hpt0 | hpt0
  · have hv0 : x.coeff (((m : ℚ) + -fracVal p e) / (a : ℚ)) = 0 := by
      by_contra h0
      have := hnegx ((HahnSeries.mem_support _ _).mpr h0)
      rw [Set.mem_Iio] at this
      linarith
    rw [hv0, zero_pow (pow_ne_zero _ hp.out.ne_zero)]
  · have hp1 : (1 : ℚ) < (p : ℚ) := by exact_mod_cast hp.out.one_lt
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt
      ((((b' : ℚ) + 1) / (a : ℚ)) / (-(((m : ℚ) + -fracVal p e) / (a : ℚ)))) hp1
    obtain ⟨m', e', B, _, _, hB, hptk, hval⟩ := hiter k m e he hsum
    have hx0 : x.coeff (((m' : ℚ) + -fracVal p e') / (a : ℚ)) = 0 := by
      by_contra h0
      have hlow := neg_lt_of_mem_Sabc p (hsuppx ((HahnSeries.mem_support _ _).mpr h0))
      rw [← hptk] at hlow
      have h1 : (0 : ℚ) < -(((m : ℚ) + -fracVal p e) / (a : ℚ)) := by linarith
      have h3 : (p : ℚ) ^ k
          < (((b' : ℚ) + 1) / (a : ℚ)) / (-(((m : ℚ) + -fracVal p e) / (a : ℚ))) := by
        rw [lt_div_iff₀ h1]
        nlinarith
      linarith
    rw [hx0, zero_add] at hval
    apply pow_p_pow_left_injective p k
    change (x.coeff (((m : ℚ) + -fracVal p e) / (a : ℚ)) ^ p ^ D) ^ p ^ k
      = x.coeff (((m : ℚ) + -fracVal p e) / (a : ℚ)) ^ p ^ k
    calc (x.coeff (((m : ℚ) + -fracVal p e) / (a : ℚ)) ^ p ^ D) ^ p ^ k
        = (x.coeff (((m : ℚ) + -fracVal p e) / (a : ℚ)) ^ p ^ k) ^ p ^ D := by
          rw [← pow_mul, mul_comm (p ^ D) (p ^ k), pow_mul]
      _ = B ^ p ^ D := by rw [hval]
      _ = B := hB
      _ = x.coeff (((m : ℚ) + -fracVal p e) / (a : ℚ)) ^ p ^ k := hval.symm

/-! ### The twist-sequence coupling relations

Along `x^p = x + y`, `p`-th powers of the twist sequences of `x` are twist sequences of
`x + y`: the evaluation point is multiplied by `p`, which shifts the digit string one
place — dropping the leading digit into the slice index when the gap sits at `j ≥ 2`,
and shortening the gap by one when it sits at `j = 1` (`lem:as-twist-couple`). -/

/-- **Coupling at gap position 1**: the `p`-th power of the gap-one twist sequence of
the slice `m` of `x` at index `n + 1` is the gap-one twist sequence of the slice `p·m`
of `x + y` at index `n`, with the same digits. -/
theorem twistSeq_couple_gap_one {x y : HahnSeries ℚ (𝔽ᵃ_[p])} {a : ℕ+}
    (hAS : x ^ p = x + y) (m : ℤ) (dig : ℕ →₀ ℕ) (n : ℕ) :
    (twistSeq p (fun z => x.coeff (((m : ℚ) + z) / (a : ℚ))) 1 dig (n + 1)) ^ p
      = twistSeq p (fun z => (x + y).coeff ((((p * m : ℤ) : ℚ) + z) / (a : ℚ)))
          1 dig n := by
  have hpq : ((p : ℚ)) ≠ 0 := by exact_mod_cast hp.out.pos.ne'
  have haq : ((a : ℚ)) ≠ 0 := by exact_mod_cast a.pos.ne'
  rw [twistSeq_eq_neg_fracVal_gapDig, twistSeq_eq_neg_fracVal_gapDig]
  change (x.coeff (((m : ℚ) + -fracVal p (gapDig 1 (n + 1) dig)) / (a : ℚ))) ^ p
    = (x + y).coeff ((((p * m : ℤ) : ℚ) + -fracVal p (gapDig 1 n dig)) / (a : ℚ))
  rw [← hAS, coeff_pow_char]
  have hkey := p_mul_fracVal p hp.out.pos (gapDig 1 (n + 1) dig)
  rw [gapDig_one_apply_zero n dig, unshiftDig_gapDig_one n dig] at hkey
  have harg : ((((p * m : ℤ) : ℚ) + -fracVal p (gapDig 1 n dig)) / (a : ℚ)) / (p : ℚ)
      = ((m : ℚ) + -fracVal p (gapDig 1 (n + 1) dig)) / (a : ℚ) := by
    rw [show fracVal p (gapDig 1 n dig)
        = (p : ℚ) * fracVal p (gapDig 1 (n + 1) dig) from by push_cast at hkey; linarith]
    push_cast
    field_simp
  rw [harg]

/-- **Coupling at gap positions `j ≥ 2`**: the `p`-th power of the twist sequence of
the slice `m` of `x` at gap position `j` is the twist sequence of the slice
`p·m - dig 0` of `x + y` at gap position `j - 1` with the leading digit dropped, at
the same index. -/
theorem twistSeq_couple_gap_ge_two {x y : HahnSeries ℚ (𝔽ᵃ_[p])} {a : ℕ+}
    (hAS : x ^ p = x + y) (m : ℤ) {j : ℕ} (hj : 2 ≤ j) (dig : ℕ →₀ ℕ) (n : ℕ) :
    (twistSeq p (fun z => x.coeff (((m : ℚ) + z) / (a : ℚ))) j dig n) ^ p
      = twistSeq p
          (fun z => (x + y).coeff ((((p * m - dig 0 : ℤ) : ℚ) + z) / (a : ℚ)))
          (j - 1) (unshiftDig dig) n := by
  have hpq : ((p : ℚ)) ≠ 0 := by exact_mod_cast hp.out.pos.ne'
  have haq : ((a : ℚ)) ≠ 0 := by exact_mod_cast a.pos.ne'
  rw [twistSeq_eq_neg_fracVal_gapDig, twistSeq_eq_neg_fracVal_gapDig]
  change (x.coeff (((m : ℚ) + -fracVal p (gapDig j n dig)) / (a : ℚ))) ^ p
    = (x + y).coeff ((((p * m - dig 0 : ℤ) : ℚ)
        + -fracVal p (gapDig (j - 1) n (unshiftDig dig))) / (a : ℚ))
  rw [← hAS, coeff_pow_char]
  have hkey := p_mul_fracVal p hp.out.pos (gapDig j n dig)
  rw [gapDig_apply_zero hj] at hkey
  have harg : ((((p * m - dig 0 : ℤ) : ℚ)
        + -fracVal p (gapDig (j - 1) n (unshiftDig dig))) / (a : ℚ)) / (p : ℚ)
      = ((m : ℚ) + -fracVal p (gapDig j n dig)) / (a : ℚ) := by
    rw [← unshiftDig_gapDig hj n dig,
      show fracVal p (unshiftDig (gapDig j n dig))
          = (p : ℚ) * fracVal p (gapDig j n dig) - (dig 0 : ℚ) from by linarith]
    push_cast
    field_simp
    ring
  rw [harg]

/-- Twist sequences of a sum of series split termwise. -/
theorem twistSeq_slice_add (x y : HahnSeries ℚ (𝔽ᵃ_[p])) (a : ℕ+) (m : ℤ) (j : ℕ)
    (dig : ℕ →₀ ℕ) (n : ℕ) :
    twistSeq p (fun z => (x + y).coeff (((m : ℚ) + z) / (a : ℚ))) j dig n
      = twistSeq p (fun z => x.coeff (((m : ℚ) + z) / (a : ℚ))) j dig n
        + twistSeq p (fun z => y.coeff (((m : ℚ) + z) / (a : ℚ))) j dig n := by
  rw [show (fun z => (x + y).coeff (((m : ℚ) + z) / (a : ℚ)))
      = fun z => x.coeff (((m : ℚ) + z) / (a : ℚ)) + y.coeff (((m : ℚ) + z) / (a : ℚ))
    from funext fun z => HahnSeries.coeff_add, twistSeq_add]

end TrustworthyKedlaya.UP
