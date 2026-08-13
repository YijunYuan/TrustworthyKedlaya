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

end TrustworthyKedlaya.UP
