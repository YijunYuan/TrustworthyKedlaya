/-
Copyright (c) 2026 Shanwen Wang, Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import TrustworthyKedlaya.Rescale

/-!
# Coefficientwise combinations of UP series

For any function `φ : 𝔽̄_p → 𝔽̄_p → 𝔽̄_p` with `φ 0 0 = 0` and UP series `x`, `y`,
the series with coefficient `φ (x.coeff q) (y.coeff q)` at each exponent `q` is UP
(`lem:up-coeffwise`).  Twist sequences evaluate slices pointwise, so they transform
termwise under `φ`; supports unite as for addition, and the periodicity data
combines as `(max M M', lcm N N')` after the common-width upgrade of
`TrustworthyKedlaya.Rescale`.

This is the `K = 𝔽̄_p` replacement for Kedlaya's closure of twist-recurrent
sequences under fixed polynomial combinations: an arbitrary zero-preserving
function suffices, because eventual periodicity (unlike twist-recurrence) is
preserved by any termwise image.

## Main statements

- `TrustworthyKedlaya.UP.coeffwise`: the coefficientwise combination of two Hahn
  series.
- `TrustworthyKedlaya.UP.IsUP.coeffwise`: UP is stable under coefficientwise
  combinations (`lem:up-coeffwise`).

## References

- K. S. Kedlaya, *Power series and p-adic algebraic closures*, J. Number Theory 89
  (2001) [Ked01b], proof of Theorem 7 (the ring property of `B`).
-/

@[expose] public section

namespace TrustworthyKedlaya.UP

variable (p : ℕ) [hp : Fact (Nat.Prime p)]

/-- The **coefficientwise combination** of two Hahn series under a zero-preserving
binary function: the series with coefficient `φ (x.coeff q) (y.coeff q)` at each
exponent `q`.  The hypothesis `φ 0 0 = 0` keeps the support inside the union of
the two supports. -/
noncomputable def coeffwise (φ : 𝔽ᵃ_[p] → 𝔽ᵃ_[p] → 𝔽ᵃ_[p]) (hφ : φ 0 0 = 0)
    (x y : HahnSeries ℚ (𝔽ᵃ_[p])) : HahnSeries ℚ (𝔽ᵃ_[p]) where
  coeff q := φ (x.coeff q) (y.coeff q)
  isPWO_support' := (x.isPWO_support'.union y.isPWO_support').mono fun q hq => by
    rw [Function.mem_support] at hq
    rcases eq_or_ne (x.coeff q) 0 with hx0 | hx0
    · rcases eq_or_ne (y.coeff q) 0 with hy0 | hy0
      · exact absurd (by rw [hx0, hy0, hφ]) hq
      · exact Set.mem_union_right _ (Function.mem_support.mpr hy0)
    · exact Set.mem_union_left _ (Function.mem_support.mpr hx0)

variable {p}

@[simp] theorem coeff_coeffwise (φ : 𝔽ᵃ_[p] → 𝔽ᵃ_[p] → 𝔽ᵃ_[p]) (hφ : φ 0 0 = 0)
    (x y : HahnSeries ℚ (𝔽ᵃ_[p])) (q : ℚ) :
    (coeffwise p φ hφ x y).coeff q = φ (x.coeff q) (y.coeff q) := rfl

/-- Twist sequences of a pointwise binary combination are the termwise combinations
of the twist sequences (twist sequences are computed pointwise). -/
lemma twistSeq_comp₂ (φ : 𝔽ᵃ_[p] → 𝔽ᵃ_[p] → 𝔽ᵃ_[p]) (f g : ℚ → 𝔽ᵃ_[p]) (j : ℕ)
    (b : ℕ →₀ ℕ) (n : ℕ) :
    twistSeq p (fun z => φ (f z) (g z)) j b n
      = φ (twistSeq p f j b n) (twistSeq p g j b n) := rfl

/-- The termwise binary image of two periodic functions is periodic, with preperiod
the maximum and period the least common multiple of the originals. -/
lemma IsTwistPeriodic.comp₂ {f g : ℚ → 𝔽ᵃ_[p]} {c : ℕ} {Mf Mg Nf Ng : ℕ+}
    (hf : IsTwistPeriodic p f c Mf Nf) (hg : IsTwistPeriodic p g c Mg Ng)
    (φ : 𝔽ᵃ_[p] → 𝔽ᵃ_[p] → 𝔽ᵃ_[p]) :
    IsTwistPeriodic p (fun z => φ (f z) (g z)) c (max Mf Mg) (Nf.lcm Ng) := by
  have hf' : IsTwistPeriodic p f c (max Mf Mg) (Nf.lcm Ng) :=
    hf.mono le_rfl (by exact_mod_cast le_max_left Mf Mg)
      (PNat.dvd_iff.mp (PNat.dvd_lcm_left Nf Ng))
  have hg' : IsTwistPeriodic p g c (max Mf Mg) (Nf.lcm Ng) :=
    hg.mono le_rfl (by exact_mod_cast le_max_right Mf Mg)
      (PNat.dvd_iff.mp (PNat.dvd_lcm_right Nf Ng))
  intro j dig hj hd hs n hn
  rw [twistSeq_comp₂, twistSeq_comp₂, hf' j dig hj hd hs n hn, hg' j dig hj hd hs n hn]

/-- **Coefficientwise combinations at a common slice width**: if `x` and `y` carry UP
data with the same support parameter `a`, then `coeffwise φ hφ x y` is UP with
parameters `(a, max b b', max c c')` and periodicity data
`(max M M', lcm N N')`. -/
theorem isUP_coeffwise_of_common_width {x y : HahnSeries ℚ (𝔽ᵃ_[p])} {a : ℕ+}
    {b b' c c' : ℕ} {M M' N N' : ℕ+}
    (φ : 𝔽ᵃ_[p] → 𝔽ᵃ_[p] → 𝔽ᵃ_[p]) (hφ : φ 0 0 = 0)
    (hxsupp : x.support ⊆ Sabc p a b c)
    (hxper : ∀ m : ℤ, -(b : ℤ) ≤ m →
      IsTwistPeriodic p (fun z => x.coeff (((m : ℚ) + z) / (a : ℚ))) c M N)
    (hysupp : y.support ⊆ Sabc p a b' c')
    (hyper : ∀ m : ℤ, -(b' : ℤ) ≤ m →
      IsTwistPeriodic p (fun z => y.coeff (((m : ℚ) + z) / (a : ℚ))) c' M' N') :
    IsUP p (coeffwise p φ hφ x y) := by
  refine ⟨a, max b b', max c c', ?_, max M M', N.lcm N', fun m _ => ?_⟩
  · -- the support lies in the union of the two supports, which unite by monotonicity
    intro g hg
    rw [HahnSeries.mem_support, coeff_coeffwise] at hg
    rcases eq_or_ne (x.coeff g) 0 with hx0 | hx0
    · rcases eq_or_ne (y.coeff g) 0 with hy0 | hy0
      · exact absurd (by rw [hx0, hy0, hφ]) hg
      · exact Sabc_mono p a (le_max_right b b') (le_max_right c c')
          (hysupp ((HahnSeries.mem_support _ _).mpr hy0))
    · exact Sabc_mono p a (le_max_left b b') (le_max_left c c')
        (hxsupp ((HahnSeries.mem_support _ _).mpr hx0))
  · -- slices combine pointwise; upgrade both summands to the common level and all `m`
    have hx := isTwistPeriodic_slice_upgrade p hxsupp hxper (max c c') m
    have hy := isTwistPeriodic_slice_upgrade p hysupp hyper (max c c') m
    exact hx.comp₂ hy φ

/-- **UP is stable under coefficientwise combinations** (`lem:up-coeffwise`): for any
binary function `φ` with `φ 0 0 = 0` and UP series `x`, `y`, the series with
coefficients `φ (x.coeff q) (y.coeff q)` is UP.  This subsumes Hadamard products
and coefficientwise applications of Witt carry digits. -/
theorem IsUP.coeffwise {x y : HahnSeries ℚ (𝔽ᵃ_[p])} (hx : IsUP p x) (hy : IsUP p y)
    (φ : 𝔽ᵃ_[p] → 𝔽ᵃ_[p] → 𝔽ᵃ_[p]) (hφ : φ 0 0 = 0) :
    IsUP p (coeffwise p φ hφ x y) := by
  obtain ⟨a, b, c, hxs, M, N, hxp⟩ := hx
  obtain ⟨a', b', c', hys, M', N', hyp⟩ := hy
  obtain ⟨b₁, c₁, M₁, hs₁, hp₁⟩ := SliceWitness.width_mul a' ⟨hxs, hxp⟩
  obtain ⟨b₂, c₂, M₂, hs₂, hp₂⟩ := SliceWitness.width_mul a ⟨hys, hyp⟩
  rw [mul_comm a a'] at hs₂ hp₂
  exact isUP_coeffwise_of_common_width φ hφ hs₁ hp₁ hs₂ hp₂

end TrustworthyKedlaya.UP
