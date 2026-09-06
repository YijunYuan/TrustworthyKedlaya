/-
Copyright (c) 2026 Shanwen Wang, Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import TrustworthyKedlaya.WittVector
public import Mathlib.RingTheory.WittVector.TeichmullerSeries

/-!
# Teichmüller digits of a two-term carry

Every Witt vector over the perfect field `𝔽̄_p` has a Teichmüller digit expansion:
modulo `p^{K+1}`, `w` is the sum of the lifts of its digits
`φ^{-i}(w.coeff i)` times `p^i` (`i ≤ K`), with `φ` the Frobenius.  Applying this
to the sum of two Teichmüller lifts packages the Witt addition carries into
**digit functions** `carryDigit i : 𝔽̄_p × 𝔽̄_p → 𝔽̄_p` with
`[a] + [b] ≡ [a + b] + ∑_{1 ≤ i ≤ K} [carryDigit i a b]·pⁱ  (mod p^{K+1})`.
These functions vanish at `(0,0)`, so they can be
applied coefficientwise to UP series (`TrustworthyKedlaya.Kedlaya.Coeffwise`); no
explicit Witt addition polynomials are needed.

## Main statements

- `TrustworthyKedlaya.teichDigit`: the `i`-th Teichmüller digit of a Witt vector.
- `TrustworthyKedlaya.carryDigit`: the digit functions of a two-term carry.
- `TrustworthyKedlaya.teichmuller_add_sub_sum_carryDigit_dvd`: the congruence
  above.

## References

- K. S. Kedlaya, *Power series and p-adic algebraic closures*, J. Number Theory 89
  (2001) [Ked01b], proof of Theorem 7.
-/

@[expose] public section

namespace TrustworthyKedlaya

open WittVector

variable (p : ℕ) [hp : Fact (Nat.Prime p)]

/-- The `i`-th **Teichmüller digit** of a Witt vector over `𝔽̄_p`: the
Frobenius-inverse iterate of its `i`-th Witt coordinate.  Modulo `p^{K+1}` a Witt
vector is the sum of the Teichmüller lifts of its digits times `p^i`, `i ≤ K`. -/
noncomputable def teichDigit (i : ℕ) (w : ℤᶜᵘⁿ_[p]) : 𝔽ᵃ_[p] :=
  ((_root_.frobeniusEquiv (𝔽ᵃ_[p]) p).symm ^ i) (w.coeff i)

/-- The Teichmüller digit expansion of a Witt vector, truncated at `K`, agrees with
it modulo `p^{K+1}` (mathlib's
`WittVector.dvd_sub_sum_teichmuller_iterateFrobeniusEquiv_coeff`). -/
theorem sub_sum_teichDigit_dvd (w : ℤᶜᵘⁿ_[p]) (K : ℕ) :
    (p : ℤᶜᵘⁿ_[p]) ^ (K + 1) ∣
      w - ∑ i ∈ Finset.Iic K, teichmuller p (teichDigit p i w) * (p : ℤᶜᵘⁿ_[p]) ^ i :=
  WittVector.dvd_sub_sum_teichmuller_iterateFrobeniusEquiv_coeff w K

/-- The zeroth Teichmüller digit is the zeroth Witt coordinate. -/
theorem teichDigit_zero (w : ℤᶜᵘⁿ_[p]) : teichDigit p 0 w = w.coeff 0 := by
  simp [teichDigit]

/-- The **carry digit functions** of a two-term Teichmüller sum: the Teichmüller
digits of `[a] + [b]`. -/
noncomputable def carryDigit (i : ℕ) (a b : 𝔽ᵃ_[p]) : 𝔽ᵃ_[p] :=
  teichDigit p i (teichmuller p a + teichmuller p b)

/-- The carry digits vanish at `(0, 0)`, so they act coefficientwise on Hahn
series without enlarging supports. -/
@[simp] theorem carryDigit_zero_zero (i : ℕ) : carryDigit p i (0 : 𝔽ᵃ_[p]) 0 = 0 := by
  simp [carryDigit, teichDigit]

/-- The zeroth carry digit is the sum: the zeroth Witt coordinate of `[a] + [b]`
is `a + b`. -/
theorem carryDigit_zero (a b : 𝔽ᵃ_[p]) : carryDigit p 0 a b = a + b := by
  rw [carryDigit, teichDigit_zero, WittVector.add_coeff_zero]
  simp

/-- **Teichmüller digits of a two-term carry**: modulo
`p^{K+1}`, the sum of two Teichmüller lifts is the lift of the sum plus carry
terms `[carryDigit i a b]·pⁱ` for `1 ≤ i ≤ K`. -/
theorem teichmuller_add_sub_sum_carryDigit_dvd (a b : 𝔽ᵃ_[p]) (K : ℕ) :
    (p : ℤᶜᵘⁿ_[p]) ^ (K + 1) ∣
      (teichmuller p a + teichmuller p b) - (teichmuller p (a + b) +
        ∑ i ∈ Finset.Icc 1 K, teichmuller p (carryDigit p i a b) * (p : ℤᶜᵘⁿ_[p]) ^ i) := by
  have h := sub_sum_teichDigit_dvd p (teichmuller p a + teichmuller p b) K
  have hsplit : Finset.Iic K = insert 0 (Finset.Icc 1 K) := by
    ext i
    simp only [Finset.mem_Iic, Finset.mem_insert, Finset.mem_Icc]
    omega
  rw [hsplit, Finset.sum_insert (by simp)] at h
  simpa [carryDigit, carryDigit_zero, teichDigit_zero, WittVector.add_coeff_zero]
    using h

end TrustworthyKedlaya
