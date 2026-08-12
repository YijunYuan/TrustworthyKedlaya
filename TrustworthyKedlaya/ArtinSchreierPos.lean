/-
Copyright (c) 2026 Shanwen Wang, Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import TrustworthyKedlaya.ArtinSchreierNeg
public import TrustworthyKedlaya.FrobeniusUP

/-!
# Artin-Schreier roots of positively supported UP series

For `y` uniformly periodic with support in `S_{a,b,c} ∩ (0, ∞)`, the series
`x = -∑_{k ≥ 0} y^{p^k}` is a well-defined Hahn series supported on
`S_{a,b,c} ∩ (0, ∞)`, satisfies `x^p - x = y`, and is uniformly periodic with the
*same* data `(M, N)` (Kedlaya (2001a), part of the proof of Lemma 4;
`lem:as-root-pos` of the blueprint).

In contrast with the negative-support case, digit shifts here run forward: the `k`-th
term of the defining sum, restricted to a slice and a twist datum, is a twist sequence
of `y^{p^k}` at the *same* index `n`, and `SliceWitness.pow` transfers `y`'s
periodicity data to every power `y^{p^k}` verbatim.  Although the number of
contributing `k` grows with the slice, a termwise-periodic family sums to a periodic
sequence with unchanged parameters — no orbit or ladder argument is needed.

## Main statements

- `TrustworthyKedlaya.UP.Sabc_mem_pow_mul_of_pos`: positive elements of `S_{a,b,c}`
  stay in `S_{a,b,c}` under multiplication by `p^k`.
- `TrustworthyKedlaya.UP.coeff_pow_char_pow`: the iterated Frobenius coefficient
  formula `(y^{p^k})_g = (y_{g/p^k})^{p^k}`.
- `TrustworthyKedlaya.UP.exists_hahn_asRoot_of_pos_support`: existence of the root.
- `TrustworthyKedlaya.UP.sliceWitness_asRoot_pos`: transfer of the slice witness.
- `TrustworthyKedlaya.UP.exists_artinSchreier_root_of_support_pos`: the packaged
  statement (`lem:as-root-pos`).

## References

- K. S. Kedlaya, *The algebraic closure of the power series field in positive
  characteristic*, Proc. Amer. Math. Soc. 129 (2001) [Ked01a], proof of Lemma 4.
-/

@[expose] public section

namespace TrustworthyKedlaya.UP

variable (p : ℕ) [hp : Fact (Nat.Prime p)]

/-! ### Multiplication by `p^k` on positive support points -/

/-- Positive elements of `S_{a,b,c}` stay in `S_{a,b,c}` under multiplication by `p`:
the integer part is at least `1`, so after the digit shift it is at least
`p - (p-1) = 1 ≥ -b`, and the digit sum only drops. -/
theorem Sabc_mem_p_mul_of_pos {a : ℕ+} {b c : ℕ} {s : ℚ} (hs : s ∈ Sabc p a b c)
    (hs0 : 0 < s) : (p : ℚ) * s ∈ Sabc p a b c := by
  obtain ⟨n, d, hn, hd, hsum, rfl⟩ := hs
  have ha : (0 : ℚ) < (a : ℚ) := by exact_mod_cast a.pos
  have hw1 : fracVal p d < 1 := fracVal_lt_one p hp.out.one_lt hd
  have hw0 : 0 ≤ fracVal p d := fracVal_nonneg p d
  have hn1 : 1 ≤ n := by
    rw [fracVal_def] at hs0
    by_contra hcon
    have h1 : (n : ℚ) ≤ 0 := by exact_mod_cast (by omega : n ≤ (0 : ℤ))
    have h1a : (0 : ℚ) < 1 / (a : ℚ) := by positivity
    nlinarith
  refine ⟨p * n - d 0, unshiftDig d, ?_, fun i => hd (i + 1),
    (unshiftDig_sum_le d).trans hsum, ?_⟩
  · have h2 : (d 0 : ℤ) < (p : ℤ) := by exact_mod_cast hd 0
    have h3 : (p : ℤ) ≤ (p : ℤ) * n :=
      le_mul_of_one_le_right (by positivity) hn1
    omega
  · rw [fracVal_def, fracVal_def]
    have hkey := p_mul_fracVal p hp.out.pos d
    push_cast
    linear_combination (-(1 / (a : ℚ))) * hkey

/-- Positive elements of `S_{a,b,c}` stay in `S_{a,b,c}` under multiplication by any
power `p^k`. -/
theorem Sabc_mem_pow_mul_of_pos {a : ℕ+} {b c : ℕ} {s : ℚ} (hs : s ∈ Sabc p a b c)
    (hs0 : 0 < s) (k : ℕ) : (p : ℚ) ^ k * s ∈ Sabc p a b c := by
  induction k with
  | zero => simpa using hs
  | succ k ih =>
    have h1 : (0 : ℚ) < (p : ℚ) ^ k * s := by
      have hp0 : (0 : ℚ) < (p : ℚ) := by exact_mod_cast hp.out.pos
      exact mul_pos (pow_pos hp0 k) hs0
    have h2 := Sabc_mem_p_mul_of_pos p ih h1
    rwa [show (p : ℚ) * ((p : ℚ) ^ k * s) = (p : ℚ) ^ (k + 1) * s by ring] at h2

/-! ### The iterated Frobenius coefficient formula -/

/-- `(y^{p^k})_g = (y_{g/p^k})^{p^k}`: the iterate of `coeff_pow_char`. -/
theorem coeff_pow_char_pow (y : HahnSeries ℚ (𝔽ᵃ_[p])) (k : ℕ) (g : ℚ) :
    (y ^ p ^ k).coeff g = (y.coeff (g / (p : ℚ) ^ k)) ^ p ^ k := by
  induction k generalizing g with
  | zero => simp
  | succ k ih =>
    have hpq : ((p : ℚ)) ≠ 0 := by exact_mod_cast hp.out.pos.ne'
    calc (y ^ p ^ (k + 1)).coeff g
        = ((y ^ p ^ k) ^ p).coeff g := by rw [← pow_mul, ← pow_succ]
      _ = ((y ^ p ^ k).coeff (g / p)) ^ p := coeff_pow_char _ g
      _ = ((y.coeff ((g / p) / (p : ℚ) ^ k)) ^ p ^ k) ^ p := by rw [ih (g / p)]
      _ = (y.coeff (g / (p : ℚ) ^ (k + 1))) ^ p ^ (k + 1) := by
          rw [div_div, ← pow_succ', ← pow_mul, ← pow_succ]

/-! ### Construction of the root -/

/-- The coefficient family of the candidate root at exponent `i`:
`k ↦ (y_{i/p^k})^{p^k}` (the root is `x_i = -∑_{k ≥ 0}` of these). -/
noncomputable def asRootPosTerm (y : HahnSeries ℚ (𝔽ᵃ_[p])) (i : ℚ) (k : ℕ) : 𝔽ᵃ_[p] :=
  (y.coeff (i / (p : ℚ) ^ k)) ^ p ^ k

/-- A term vanishes exactly when the sampled coefficient of `y` does. -/
theorem asRootPosTerm_eq_zero_iff {y : HahnSeries ℚ (𝔽ᵃ_[p])} {i : ℚ} {k : ℕ} :
    asRootPosTerm p y i k = 0 ↔ y.coeff (i / (p : ℚ) ^ k) = 0 := by
  rw [asRootPosTerm]
  constructor
  · exact fun h => pow_eq_zero_iff (pow_ne_zero k hp.out.ne_zero) |>.mp h
  · intro h
    rw [h, zero_pow (pow_ne_zero _ hp.out.ne_zero)]

/-- Only finitely many terms of the root family are nonzero, at every exponent:
the supports of the powers `y^{p^k}` run away to `+∞`. -/
theorem asRootPosTerm_support_finite {y : HahnSeries ℚ (𝔽ᵃ_[p])}
    (hpos : y.support ⊆ Set.Ioi 0) (i : ℚ) :
    (Function.support (asRootPosTerm p y i)).Finite := by
  have hp1 : (1 : ℚ) < (p : ℚ) := by exact_mod_cast hp.out.one_lt
  rcases eq_or_ne y 0 with rfl | hy0
  · convert Set.finite_empty
    ext k
    simp only [Function.mem_support, Set.mem_empty_iff_false, iff_false, not_not]
    rw [asRootPosTerm_eq_zero_iff]
    simp
  · have hne : y.support.Nonempty := HahnSeries.support_nonempty_iff.mpr hy0
    have hε0 : 0 < y.isWF_support.min hne := hpos (y.isWF_support.min_mem hne)
    obtain ⟨K, hK⟩ := pow_unbounded_of_one_lt (i / y.isWF_support.min hne) hp1
    apply Set.Finite.subset (Set.finite_Iio K)
    intro k hk
    rw [Function.mem_support] at hk
    have hcoeff : y.coeff (i / (p : ℚ) ^ k) ≠ 0 := fun h0 =>
      hk (asRootPosTerm_eq_zero_iff p |>.mpr h0)
    have hεle : y.isWF_support.min hne ≤ i / (p : ℚ) ^ k :=
      Set.IsWF.min_le _ hne ((HahnSeries.mem_support _ _).mpr hcoeff)
    have hpk : (0 : ℚ) < (p : ℚ) ^ k := by positivity
    have h2 : (p : ℚ) ^ k ≤ i / y.isWF_support.min hne := by
      rw [le_div_iff₀ hε0]
      calc (p : ℚ) ^ k * y.isWF_support.min hne
          ≤ (p : ℚ) ^ k * (i / (p : ℚ) ^ k) := mul_le_mul_of_nonneg_left hεle hpk.le
        _ = i := by field_simp
    have h3 : (p : ℚ) ^ k < (p : ℚ) ^ K := lt_of_le_of_lt h2 hK
    have h4 : k < K := by
      by_contra hcon
      exact absurd (pow_le_pow_right₀ hp1.le (not_lt.mp hcon)) (not_le.mpr h3)
    exact Set.mem_Iio.mpr h4

/-- **Existence of the Hahn-series Artin-Schreier root, positive support**: for `y`
supported in `S_{a,b,c} ∩ (0,∞)` there is a Hahn series `x` supported in
`S_{a,b,c} ∩ (0,∞)` with `x^p = x + y`, whose coefficients are
`x_P = -∑_{k ≥ 0} (y^{p^k})_P`. -/
theorem exists_hahn_asRoot_of_pos_support {y : HahnSeries ℚ (𝔽ᵃ_[p])} {a : ℕ+} {b c : ℕ}
    (hsupp : y.support ⊆ Sabc p a b c) (hpos : y.support ⊆ Set.Ioi 0) :
    ∃ x : HahnSeries ℚ (𝔽ᵃ_[p]), x ^ p = x + y ∧
      x.support ⊆ Sabc p a b c ∧ x.support ⊆ Set.Ioi 0 ∧
      ∀ P : ℚ, x.coeff P = -∑ᶠ k, (y ^ p ^ k).coeff P := by
  have hpq : ((p : ℚ)) ≠ 0 := by exact_mod_cast hp.out.pos.ne'
  set F : ℚ → 𝔽ᵃ_[p] := fun i => ∑ᶠ k : ℕ, asRootPosTerm p y i k with hF
  have hFsupp : ∀ i, F i ≠ 0 → i ∈ Sabc p a b c ∧ 0 < i := by
    intro i hi
    have hex : ∃ k : ℕ, asRootPosTerm p y i k ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hi (finsum_eq_zero_of_forall_eq_zero hall)
    obtain ⟨k, hk⟩ := hex
    have hcoeff : y.coeff (i / (p : ℚ) ^ k) ≠ 0 := fun h0 =>
      hk (asRootPosTerm_eq_zero_iff p |>.mpr h0)
    have hmem := hsupp ((HahnSeries.mem_support _ _).mpr hcoeff)
    have hmempos := hpos ((HahnSeries.mem_support _ _).mpr hcoeff)
    rw [Set.mem_Ioi] at hmempos
    have hpk : (0 : ℚ) < (p : ℚ) ^ k := by positivity
    have hi' : i = (p : ℚ) ^ k * (i / (p : ℚ) ^ k) := by field_simp
    constructor
    · rw [hi']
      exact Sabc_mem_pow_mul_of_pos p hmem hmempos k
    · rw [hi']
      exact mul_pos hpk hmempos
  have hFpwo : (Function.support F).IsPWO :=
    (Sabc_isPWO p a b c).mono fun i hi => (hFsupp i hi).1
  set X : HahnSeries ℚ (𝔽ᵃ_[p]) := ⟨F, hFpwo⟩ with hX
  have hXcoeff : ∀ i, X.coeff i = ∑ᶠ k : ℕ, asRootPosTerm p y i k := fun _ => rfl
  -- the key coefficientwise relation for `X`
  have hkey : ∀ g : ℚ, (X.coeff g) ^ p = X.coeff ((p : ℚ) * g) + -y.coeff ((p : ℚ) * g) := by
    intro g
    have hpoint : ∀ k : ℕ, g / (p : ℚ) ^ k = ((p : ℚ) * g) / (p : ℚ) ^ (k + 1) := by
      intro k
      rw [pow_succ']
      field_simp
    have hGfin : (Function.support (asRootPosTerm p y ((p : ℚ) * g))).Finite :=
      asRootPosTerm_support_finite p hpos _
    obtain ⟨K, hK⟩ := hGfin.bddAbove
    have hGsub : Function.support (asRootPosTerm p y ((p : ℚ) * g))
        ⊆ ↑(Finset.range (K + 1)) := fun x hx => by
      simp only [Finset.coe_range, Set.mem_Iio]
      exact Nat.lt_succ_of_le (hK hx)
    have hTsub : Function.support (asRootPosTerm p y g) ⊆ ↑(Finset.range (K + 1)) := by
      intro k hk
      rw [Function.mem_support] at hk
      have hk1 : asRootPosTerm p y ((p : ℚ) * g) (k + 1) ≠ 0 := fun h0 => by
        rw [asRootPosTerm_eq_zero_iff, ← hpoint k] at h0
        exact hk (asRootPosTerm_eq_zero_iff p |>.mpr h0)
      have hkK : k + 1 ≤ K := hK (Function.mem_support.mpr hk1)
      simp only [Finset.coe_range, Set.mem_Iio]
      omega
    -- termwise `p`-th powers step the term index up by one
    have hterm : ∀ k : ℕ, (asRootPosTerm p y g k) ^ p
        = asRootPosTerm p y ((p : ℚ) * g) (k + 1) := by
      intro k
      rw [asRootPosTerm, asRootPosTerm, ← pow_mul, ← pow_succ, hpoint k]
    calc (X.coeff g) ^ p
        = (∑ k ∈ Finset.range (K + 1), asRootPosTerm p y g k) ^ p := by
          rw [hXcoeff g, finsum_eq_sum_of_support_subset _ hTsub]
      _ = ∑ k ∈ Finset.range (K + 1), (asRootPosTerm p y g k) ^ p := by
          rw [sum_pow_char]
      _ = ∑ k ∈ Finset.range (K + 1), asRootPosTerm p y ((p : ℚ) * g) (k + 1) :=
          Finset.sum_congr rfl fun k _ => hterm k
      _ = ∑ᶠ k, asRootPosTerm p y ((p : ℚ) * g) (k + 1) :=
          (finsum_eq_sum_of_support_subset _ (fun x hx => by
            simp only [Finset.coe_range, Set.mem_Iio]
            have : x + 1 ≤ K := hK hx
            omega)).symm
      _ = X.coeff ((p : ℚ) * g) + -y.coeff ((p : ℚ) * g) := by
          have hsplit := finsum_nat_eq_zero_add hGfin
          have h0 : asRootPosTerm p y ((p : ℚ) * g) 0 = y.coeff ((p : ℚ) * g) := by
            simp [asRootPosTerm]
          rw [hXcoeff]
          rw [hsplit, h0]
          ring
  -- assemble: `x = -X`
  refine ⟨-X, ?_, ?_, ?_, ?_⟩
  · -- the Artin-Schreier identity
    ext g
    rw [coeff_pow_char, HahnSeries.coeff_add]
    have hneg : (-X).coeff (g / p) = -(X.coeff (g / p)) := by
      rw [HahnSeries.coeff_neg]
    rw [hneg, neg_pow, neg_one_pow_char]
    have := hkey (g / (p : ℚ))
    rw [mul_div_cancel₀ g hpq] at this
    rw [this, HahnSeries.coeff_neg]
    ring
  · intro i hi
    rw [HahnSeries.mem_support, HahnSeries.coeff_neg, neg_ne_zero] at hi
    exact (hFsupp i hi).1
  · intro i hi
    rw [HahnSeries.mem_support, HahnSeries.coeff_neg, neg_ne_zero] at hi
    exact Set.mem_Ioi.mpr (hFsupp i hi).2
  · intro P
    rw [HahnSeries.coeff_neg, hXcoeff, neg_inj]
    exact finsum_congr fun k => by
      rw [asRootPosTerm, coeff_pow_char_pow]

/-! ### Transfer of the slice witness -/

/-- **The slice witness transfers with unchanged data**: if `y` has a width-`a` slice
witness `(b, c, M, N)` and `x` is a series supported in `S_{a,b,c}` with
`x_P = -∑_k (y^{p^k})_P`, then `x` has the *same* slice witness `(b, c, M, N)` — each
term of the sum is a twist sequence of `y^{p^k}`, whose witness `SliceWitness.pow`
keeps `(M, N)` verbatim, and termwise-periodic families sum to periodic sequences. -/
theorem sliceWitness_asRoot_pos {x y : HahnSeries ℚ (𝔽ᵃ_[p])} {a : ℕ+} {b c : ℕ}
    {M N : ℕ+} (hw : SliceWitness p y a b c M N)
    (hsuppx : x.support ⊆ Sabc p a b c)
    (hcoeff : ∀ P : ℚ, x.coeff P = -∑ᶠ k, (y ^ p ^ k).coeff P) :
    SliceWitness p x a b c M N := by
  refine ⟨hsuppx, fun m _ => ?_⟩
  intro j dig hj hdig hsum n hn
  -- every power of `y` has a slice witness with the same periodicity data
  have hwk : ∀ k : ℕ, ∃ bk : ℕ, SliceWitness p (y ^ p ^ k) a bk c M N := by
    intro k
    induction k with
    | zero => exact ⟨b, by simpa using hw⟩
    | succ k ih =>
      obtain ⟨bk, hk⟩ := ih
      refine ⟨p * bk + (p - 1), ?_⟩
      have h2 := hk.pow
      rwa [← pow_mul, ← pow_succ] at h2
  have hterm : ∀ k : ℕ,
      twistSeq p (fun z => (y ^ p ^ k).coeff (((m : ℚ) + z) / (a : ℚ))) j dig (n + N)
        = twistSeq p (fun z => (y ^ p ^ k).coeff (((m : ℚ) + z) / (a : ℚ))) j dig n := by
    intro k
    obtain ⟨bk, hk⟩ := hwk k
    exact isTwistPeriodic_slice_upgrade p hk.1 hk.2 c m j dig hj hdig hsum n hn
  have hexp : ∀ n' : ℕ,
      twistSeq p (fun z => x.coeff (((m : ℚ) + z) / (a : ℚ))) j dig n'
        = -∑ᶠ k, twistSeq p (fun z => (y ^ p ^ k).coeff (((m : ℚ) + z) / (a : ℚ)))
            j dig n' := by
    intro n'
    rw [twistSeq_eq_neg_fracVal_gapDig, hcoeff, neg_inj]
    exact finsum_congr fun k => (twistSeq_eq_neg_fracVal_gapDig p
      (fun z => (y ^ p ^ k).coeff (((m : ℚ) + z) / (a : ℚ))) j dig n').symm
  rw [hexp (n + N), hexp n, neg_inj]
  exact finsum_congr fun k => hterm k

/-- **Artin-Schreier roots of positively supported UP series** (`lem:as-root-pos`):
if `y` has a width-`a` slice witness with data `(b, c, M, N)` and support in
`(0, ∞)`, then there is a Hahn series `x` with `x^p - x = y`, support in `(0, ∞)`,
and the *same* slice witness data `(b, c, M, N)`; in particular `x` is uniformly
periodic. -/
theorem exists_artinSchreier_root_of_support_pos {y : HahnSeries ℚ (𝔽ᵃ_[p])} {a : ℕ+}
    {b c : ℕ} {M N : ℕ+} (hpos : y.support ⊆ Set.Ioi 0)
    (hw : SliceWitness p y a b c M N) :
    ∃ x : HahnSeries ℚ (𝔽ᵃ_[p]), x ^ p - x = y ∧ x.support ⊆ Set.Ioi 0 ∧ IsUP p x ∧
      SliceWitness p x a b c M N := by
  obtain ⟨x, hAS, hxsupp, hxpos, hcoeff⟩ :=
    exists_hahn_asRoot_of_pos_support p hw.1 hpos
  have hwx := sliceWitness_asRoot_pos p hw hxsupp hcoeff
  exact ⟨x, by rw [hAS]; exact add_sub_cancel_left x y, hxpos,
    isUP_iff_exists_sliceWitness.mpr ⟨a, b, c, M, N, hwx⟩, hwx⟩

end TrustworthyKedlaya.UP
