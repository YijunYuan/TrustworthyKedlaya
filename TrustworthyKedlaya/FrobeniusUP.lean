/-
Copyright (c) 2026 Shanwen Wang, Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import TrustworthyKedlaya.Frobenius
public import TrustworthyKedlaya.Rescale
public import TrustworthyKedlaya.SupportSets

/-!
# UP is stable under Frobenius and inverse Frobenius

The Frobenius `x ↦ x^p` of `𝔽̄_p((t^ℚ))` acts coefficientwise with the support scaling
`i ↦ p·i` (`TrustworthyKedlaya.coeff_pow_char`), and both it and its inverse preserve
the class of uniformly periodic series:

- `TrustworthyKedlaya.UP.IsUP.pow_char`: if `x` is UP then so is `x ^ p`;
- `TrustworthyKedlaya.UP.IsUP.of_pow`: if `x ^ p` is UP then so is `x`;
- `TrustworthyKedlaya.UP.isUP_invFrobeniusHahn`: the (unique) `p`-th root of a UP
  series is UP.

The support halves are the digit-shift inclusions `Sabc_mem_p_mul`/`Sabc_mem_div_p`.
For the twist sequences, slicing `x^p` by `m` and sampling at a twist point with digits
`dig` and gap at `j` samples `x` at the slice `m'` (where `m = p·m' - v`, `0 ≤ v < p`)
and the twist point with digits `consDig v dig` and gap at `j + 1`; in the inverse
direction the leading digit `dig 0` is dropped into the slice index (gap `j ≥ 2`), or
the gap itself shrinks by one step (gap `j = 1`).  The digit-sum level moves by at most
`p - 1`, which is immaterial by `isTwistPeriodic_slice_upgrade`.  Periods are
unchanged; the preperiod grows by one only for the inverse direction (gap `j = 1`).
-/

@[expose] public section

namespace TrustworthyKedlaya.UP

variable (p : ℕ) [hp : Fact (Nat.Prime p)]

/-- **Frobenius preserves slice witnesses verbatim** (up to the support shift
`b ↦ pb + (p-1)`): the periodicity data `(M, N)` of `x` transfers unchanged to
`x ^ p`.  This witness-level form is what the Artin-Schreier constructions iterate. -/
theorem SliceWitness.pow {x : HahnSeries ℚ (𝔽ᵃ_[p])} {a : ℕ+} {b c : ℕ} {M N : ℕ+}
    (hx : SliceWitness p x a b c M N) :
    SliceWitness p (x ^ p) a (p * b + (p - 1)) c M N := by
  have hpq : ((p : ℚ)) ≠ 0 := by exact_mod_cast hp.out.pos.ne'
  obtain ⟨hsupp, hper⟩ := hx
  have haq : ((a : ℚ)) ≠ 0 := by exact_mod_cast a.pos.ne'
  have hall := isTwistPeriodic_slice_upgrade p hsupp hper
  refine ⟨?_, ?_⟩
  · -- support: `p · S_{a,b,c} ⊆ S_{a,pb+(p-1),c}`
    intro g hg
    rw [HahnSeries.mem_support, coeff_pow_char] at hg
    have hx0 : x.coeff (g / p) ≠ 0 := fun h => hg (by rw [h]; exact zero_pow hp.out.pos.ne')
    have h2 := Sabc_mem_p_mul p (hsupp ((HahnSeries.mem_support _ _).mpr hx0))
    rwa [mul_div_cancel₀ g hpq] at h2
  · intro m _
    -- write `m = p·m' - v` with `0 ≤ v < p`
    obtain ⟨m', v, hv, hmv⟩ : ∃ (m' : ℤ) (v : ℕ), v < p ∧ m = p * m' - v := by
      have hmod : m % p + (p : ℤ) * (m / p) = m := by rw [Int.emod_def]; ring
      have hr0 : 0 ≤ m % p := Int.emod_nonneg m (by exact_mod_cast hp.out.pos.ne')
      have hrp : m % p < p := Int.emod_lt_of_pos m (by exact_mod_cast hp.out.pos)
      rcases eq_or_lt_of_le hr0 with h0 | h1
      · exact ⟨m / p, 0, hp.out.pos, by push_cast; linarith⟩
      · refine ⟨m / p + 1, (p - m % p).toNat, by omega, ?_⟩
        have htn : (((p - m % p).toNat : ℕ) : ℤ) = (p : ℤ) - m % p :=
          Int.toNat_of_nonneg (by omega)
        have hexp : (p : ℤ) * (m / p + 1) = p * (m / p) + p := by ring
        rw [htn]
        linarith
    intro j dig hj hdig hsum n hn
    have hmq : (m : ℚ) = (p : ℚ) * (m' : ℚ) - (v : ℚ) := by exact_mod_cast hmv
    -- the twist sequence of the `m`-slice of `x^p` is the `p`-th power of a twist
    -- sequence of the `m'`-slice of `x`, with the digit `v` prepended and the gap
    -- moved from `j` to `j+1`
    have key : ∀ k : ℕ,
        twistSeq p (fun z => (x ^ p).coeff (((m : ℚ) + z) / (a : ℚ))) j dig k
          = (twistSeq p (fun z => x.coeff (((m' : ℚ) + z) / (a : ℚ))) (j + 1)
              (consDig v dig) k) ^ p := by
      intro k
      rw [twistSeq_eq_neg_fracVal_gapDig, twistSeq_eq_neg_fracVal_gapDig]
      show (x ^ p).coeff (((m : ℚ) + -fracVal p (gapDig j k dig)) / (a : ℚ))
        = (x.coeff (((m' : ℚ)
            + -fracVal p (gapDig (j + 1) k (consDig v dig))) / (a : ℚ))) ^ p
      rw [coeff_pow_char]
      have harg : (((m : ℚ) + -fracVal p (gapDig j k dig)) / (a : ℚ)) / (p : ℚ)
          = ((m' : ℚ) + -fracVal p (gapDig (j + 1) k (consDig v dig))) / (a : ℚ) := by
        rw [gapDig_consDig hj k v dig, fracVal_consDig p hp.out.pos, hmq]
        field_simp
        ring
      rw [harg]
    rw [key (n + N), key n,
      hall ((p - 1) + c) m' (j + 1) (consDig v dig) (by omega)
        (consDig_lt p hv hdig) (by rw [consDig_sum]; omega) n hn]

/-- **UP is stable under the Frobenius** `x ↦ x^p`. -/
theorem IsUP.pow_char {x : HahnSeries ℚ (𝔽ᵃ_[p])} (hx : IsUP p x) : IsUP p (x ^ p) := by
  obtain ⟨a, b, c, M, N, hw⟩ := isUP_iff_exists_sliceWitness.mp hx
  exact isUP_iff_exists_sliceWitness.mpr ⟨a, p * b + (p - 1), c, M, N, hw.pow⟩

/-- **UP is stable under the inverse Frobenius**: if `x ^ p` is UP then so is `x`. -/
theorem IsUP.of_pow {y : HahnSeries ℚ (𝔽ᵃ_[p])} (hy : IsUP p (y ^ p)) : IsUP p y := by
  have hpq : ((p : ℚ)) ≠ 0 := by exact_mod_cast hp.out.pos.ne'
  obtain ⟨a, b, c, hsupp, M, N, hper⟩ := hy
  have haq : ((a : ℚ)) ≠ 0 := by exact_mod_cast a.pos.ne'
  have hall := isTwistPeriodic_slice_upgrade p hsupp hper
  -- `p`-th powers are injective on `𝔽̄_p`
  have hinj : ∀ s t : 𝔽ᵃ_[p], s ^ p = t ^ p → s = t := fun s t hst =>
    (frobeniusEquiv (𝔽ᵃ_[p]) p).injective
      (by simpa [frobeniusEquiv_apply, frobenius_def] using hst)
  refine ⟨a, b, c + (p - 1), ?_, M + 1, N, ?_⟩
  · -- support: `(1/p) · S_{a,b,c} ⊆ S_{a,b,c+(p-1)}`
    intro g hg
    rw [HahnSeries.mem_support] at hg
    have h1 : (y ^ p).coeff ((p : ℚ) * g) ≠ 0 := by
      rw [coeff_pow_char, mul_div_cancel_left₀ g hpq]
      exact pow_ne_zero p hg
    have h2 := Sabc_mem_div_p p (hsupp ((HahnSeries.mem_support _ _).mpr h1))
    rwa [mul_div_cancel_left₀ g hpq] at h2
  · intro m _ j dig hj hdig hsum n hn
    have hM1 : ((M + 1 : ℕ+) : ℕ) = (M : ℕ) + 1 := rfl
    rcases Nat.lt_or_ge j 2 with hj1 | hj2
    · -- gap at `j = 1`: multiplying the twist point by `p` shrinks the gap by one
      have hj1' : j = 1 := by omega
      subst hj1'
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      have key : ∀ k : ℕ,
          (twistSeq p (fun z => y.coeff (((m : ℚ) + z) / (a : ℚ))) 1 dig (k + 1)) ^ p
            = twistSeq p
                (fun z => (y ^ p).coeff ((((p * m : ℤ) : ℚ) + z) / (a : ℚ)))
                1 dig k := by
        intro k
        rw [twistSeq_eq_neg_fracVal_gapDig, twistSeq_eq_neg_fracVal_gapDig]
        show (y.coeff (((m : ℚ) + -fracVal p (gapDig 1 (k + 1) dig)) / (a : ℚ))) ^ p
          = (y ^ p).coeff ((((p * m : ℤ) : ℚ)
              + -fracVal p (gapDig 1 k dig)) / (a : ℚ))
        rw [coeff_pow_char]
        have hkey := p_mul_fracVal p hp.out.pos (gapDig 1 (k + 1) dig)
        rw [gapDig_one_apply_zero k dig, unshiftDig_gapDig_one k dig] at hkey
        have harg : ((((p * m : ℤ) : ℚ)
              + -fracVal p (gapDig 1 k dig)) / (a : ℚ)) / (p : ℚ)
            = ((m : ℚ) + -fracVal p (gapDig 1 (k + 1) dig)) / (a : ℚ) := by
          rw [show fracVal p (gapDig 1 k dig)
              = (p : ℚ) * fracVal p (gapDig 1 (k + 1) dig) from by
            push_cast at hkey
            linarith]
          push_cast
          field_simp
        rw [harg]
      refine hinj _ _ ?_
      rw [show k + 1 + (N : ℕ) = (k + N) + 1 from by omega, key (k + N), key k,
        hall (c + (p - 1)) (p * m) 1 dig one_pos hdig hsum k
          (by rw [hM1] at hn; omega)]
    · -- gap at `j ≥ 2`: the leading digit is dropped into the slice index
      have key : ∀ k : ℕ,
          (twistSeq p (fun z => y.coeff (((m : ℚ) + z) / (a : ℚ))) j dig k) ^ p
            = twistSeq p
                (fun z => (y ^ p).coeff ((((p * m - dig 0 : ℤ) : ℚ) + z) / (a : ℚ)))
                (j - 1) (unshiftDig dig) k := by
        intro k
        rw [twistSeq_eq_neg_fracVal_gapDig, twistSeq_eq_neg_fracVal_gapDig]
        show (y.coeff (((m : ℚ) + -fracVal p (gapDig j k dig)) / (a : ℚ))) ^ p
          = (y ^ p).coeff ((((p * m - dig 0 : ℤ) : ℚ)
              + -fracVal p (gapDig (j - 1) k (unshiftDig dig))) / (a : ℚ))
        rw [coeff_pow_char]
        have hkey := p_mul_fracVal p hp.out.pos (gapDig j k dig)
        rw [gapDig_apply_zero hj2] at hkey
        have harg : ((((p * m - dig 0 : ℤ) : ℚ)
              + -fracVal p (gapDig (j - 1) k (unshiftDig dig))) / (a : ℚ)) / (p : ℚ)
            = ((m : ℚ) + -fracVal p (gapDig j k dig)) / (a : ℚ) := by
          rw [← unshiftDig_gapDig hj2 k dig,
            show fracVal p (unshiftDig (gapDig j k dig))
                = (p : ℚ) * fracVal p (gapDig j k dig) - (dig 0 : ℚ) from by
              linarith]
          push_cast
          field_simp
          ring
        rw [harg]
      refine hinj _ _ ?_
      rw [key (n + N), key n,
        hall (c + (p - 1)) (p * m - dig 0) (j - 1) (unshiftDig dig) (by omega)
          (fun i => hdig (i + 1)) ((unshiftDig_sum_le dig).trans hsum) n (by omega)]

/-- The (unique) `p`-th root of a UP series is UP: inverse-Frobenius stability in the
form used by the Artin-Schreier induction. -/
theorem isUP_invFrobeniusHahn {x : HahnSeries ℚ (𝔽ᵃ_[p])} (hx : IsUP p x) :
    IsUP p (invFrobeniusHahn p x) :=
  IsUP.of_pow p (by rwa [invFrobeniusHahn_pow])

end TrustworthyKedlaya.UP
