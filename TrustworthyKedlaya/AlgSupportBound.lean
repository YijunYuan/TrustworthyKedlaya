/-
Copyright (c) 2026 Shanwen Wang, Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import TrustworthyKedlaya.IntegralToAlgCoeff
public import TrustworthyKedlaya.SabcOrderType

/-!
# Support bound for integral `p`-adic Hahn series

`lem:alg-support-bound` and the `ω^ω` bound of Kedlaya (2001b), Section 4, for
`ℚᵘⁿ_[p]`-integral elements.

An element `f ∈ 𝕃_[p]` integral over `ℚᵘⁿ_[p]` is truncationwise UP
(`isTruncUP_of_isIntegral_QpUn`, the subring form of
`prop:integral-to-alg-coeff`).  Below a natural cutoff `n` the canonical
coefficient function of `f` agrees with its truncation below `n + 1`, whose
support lies in a support set `S_{a,b,c}` by the support clause of `IsUP`; hence
`supp(f) ⊆ S_{a,b,c} ∪ (n, ∞)`.  Feeding this family of bounds into
`TrustworthyKedlaya.UP.typeLT_le_omega0_opow_omega0` bounds the order type of
`supp(f)` by `ω^ω`.

## Main statements

- `TrustworthyKedlaya.pAdicHahnSeries.support_subset_Sabc_union_Ioi_of_isIntegral`:
  `lem:alg-support-bound`.
- `TrustworthyKedlaya.pAdicHahnSeries.typeLT_support_le_of_isIntegral`: the
  `ω^ω` bound for `ℚᵘⁿ_[p]`-integral elements.

## References

- K. S. Kedlaya, *Power series and p-adic algebraic closures*, J. Number Theory 89
  (2001) [Ked01b], Section 4.
-/

@[expose] public section

namespace TrustworthyKedlaya.pAdicHahnSeries

variable {p : ℕ} [hp : Fact (Nat.Prime p)]

/-- **Support bound for integral `p`-adic Hahn series** (`lem:alg-support-bound`):
below every natural cutoff `n`, the support of an element of `𝕃_[p]` integral over
`ℚᵘⁿ_[p]` lies in a support set `S_{a,b,c}`. -/
theorem support_subset_Sabc_union_Ioi_of_isIntegral {f : 𝕃_[p]}
    (hf : IsIntegral ℚᵘⁿ_[p] f) (n : ℕ) :
    ∃ (a : ℕ+) (b c : ℕ), f.support ⊆ UP.Sabc p a b c ∪ Set.Ioi (n : ℚ) := by
  obtain ⟨a, b, c, hsupp, -⟩ := isTruncUP_of_isIntegral_QpUn hf (n + 1)
  refine ⟨a, b, c, fun q hq => ?_⟩
  rcases lt_or_ge (n : ℚ) q with hqn | hqn
  · exact Or.inr hqn
  · refine Or.inl (hsupp ?_)
    have hlt : q < (((n + 1 : ℕ) : ℚ)) := by push_cast; linarith
    rw [HahnSeries.mem_support, coeff_trunc_of_lt hlt]
    exact (mem_support_iff f q).mp hq

open Ordinal in
/-- The order type of the support of a `ℚᵘⁿ_[p]`-integral `p`-adic Hahn series is at
most `ω^ω`: combine `lem:alg-support-bound` with `lem:sabc-order-type`. -/
theorem typeLT_support_le_of_isIntegral {f : 𝕃_[p]}
    (hf : IsIntegral ℚᵘⁿ_[p] f) :
    typeLT f.support ≤ omega0 ^ omega0 := by
  have hWF : f.support.IsWF := by
    simpa [pAdicHahnSeries.support] using (TrustworthyKedlaya.support_IsPWO (p := p) f).isWF
  exact UP.typeLT_le_omega0_opow_omega0 p hWF
    (fun n => support_subset_Sabc_union_Ioi_of_isIntegral hf n)

end TrustworthyKedlaya.pAdicHahnSeries
