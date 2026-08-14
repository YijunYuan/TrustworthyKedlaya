/-
Copyright (c) 2026 Shanwen Wang, Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import TrustworthyKedlaya.SupportSets

/-!
# UP is stable under addition and scalars (common slice width)

For two UP series presented with the *same* support parameter `a`, the sum is UP:
the supports unite inside `S_{a, max b b', max c c'}` (monotonicity of the support
sets — no carry estimate is needed for a union), each slice of `x + y` is the
pointwise sum of the slices of `x` and of `y`, and termwise sums of periodic
sequences are periodic with data `(max M M', lcm N N')` after upgrading both
summands to the common level (`isTwistPeriodic_slice_upgrade`).  Scalar multiples
and negation act pointwise on values, so they preserve the data verbatim.

The general addition statement (arbitrary parameters `a`, `a'`) reduces to this one
by passing to a common slice width, which is the content of the exponent-rescaling
lemma; see `TrustworthyKedlaya.Rescale` for that upgrade and the
resulting unrestricted `IsUP.add`.

## Main statements

- `TrustworthyKedlaya.UP.isUP_add_of_common_width`: `x + y` is UP, given UP data for
  `x` and `y` with the same `a`.
- `TrustworthyKedlaya.UP.IsUP.smul` / `TrustworthyKedlaya.UP.IsUP.neg`: scalar
  multiples and negatives of UP series are UP.
- `TrustworthyKedlaya.UP.isUP_zero`: the zero series is UP.

## References

- K. S. Kedlaya, *The algebraic closure of the power series field in positive
  characteristic*, Proc. Amer. Math. Soc. 129 (2001) [Ked01a], proof of Lemma 4.
-/

@[expose] public section

namespace TrustworthyKedlaya.UP

variable (p : ℕ) [hp : Fact (Nat.Prime p)]

variable {p} in
/-- **UP is stable under addition at a common slice width**: if `x` and `y` carry UP
data with the same support parameter `a`, then `x + y` is UP with parameters
`(a, max b b', max c c')` and periodicity data `(max M M', lcm N N')`. -/
theorem isUP_add_of_common_width {x y : HahnSeries ℚ (𝔽ᵃ_[p])} {a : ℕ+}
    {b b' c c' : ℕ} {M M' N N' : ℕ+}
    (hxsupp : x.support ⊆ Sabc p a b c)
    (hxper : ∀ m : ℤ, -(b : ℤ) ≤ m →
      IsTwistPeriodic p (fun z => x.coeff (((m : ℚ) + z) / (a : ℚ))) c M N)
    (hysupp : y.support ⊆ Sabc p a b' c')
    (hyper : ∀ m : ℤ, -(b' : ℤ) ≤ m →
      IsTwistPeriodic p (fun z => y.coeff (((m : ℚ) + z) / (a : ℚ))) c' M' N') :
    IsUP p (x + y) := by
  refine ⟨a, max b b', max c c', ?_, max M M', N.lcm N', fun m _ => ?_⟩
  · -- supports unite by monotonicity of the support sets
    intro g hg
    have hg' := HahnSeries.support_add_subset x y hg
    rcases hg' with hgx | hgy
    · exact Sabc_mono p a (le_max_left b b') (le_max_left c c') (hxsupp hgx)
    · exact Sabc_mono p a (le_max_right b b') (le_max_right c c') (hysupp hgy)
  · -- slices add pointwise; both summands upgrade to the common level and all `m`
    have hx := isTwistPeriodic_slice_upgrade p hxsupp hxper (max c c') m
    have hy := isTwistPeriodic_slice_upgrade p hysupp hyper (max c c') m
    have hsum := hx.add hy
    simpa only [HahnSeries.coeff_add', Pi.add_apply] using hsum

variable {p} in
/-- **UP is stable under scalar multiplication**: values are multiplied pointwise, so
the support only shrinks and every twist sequence is post-composed with `λ * ·`. -/
theorem IsUP.smul {x : HahnSeries ℚ (𝔽ᵃ_[p])} (l : 𝔽ᵃ_[p]) (hx : IsUP p x) :
    IsUP p (l • x) := by
  obtain ⟨a, b, c, hsupp, M, N, hper⟩ := hx
  refine ⟨a, b, c, ?_, M, N, fun m hm => ?_⟩
  · intro g hg
    rw [HahnSeries.mem_support, HahnSeries.coeff_smul, smul_eq_mul] at hg
    exact hsupp ((HahnSeries.mem_support _ _).mpr fun h0 => hg (by rw [h0, mul_zero]))
  · have hcomp := (hper m hm).comp (fun v => l * v)
    simpa only [HahnSeries.coeff_smul, smul_eq_mul] using hcomp

variable {p} in
/-- UP is stable under negation. -/
theorem IsUP.neg {x : HahnSeries ℚ (𝔽ᵃ_[p])} (hx : IsUP p x) : IsUP p (-x) := by
  have h := hx.smul (-1)
  rwa [neg_one_smul] at h

/-- The zero series is UP. -/
theorem isUP_zero : IsUP p (0 : HahnSeries ℚ (𝔽ᵃ_[p])) :=
  isUP_of_support_int_div 1 fun s hs => by simp at hs

end TrustworthyKedlaya.UP
