/-
Copyright (c) 2026 Shanwen Wang, Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import TrustworthyKedlaya.Kedlaya.WittCarryUP
public import TrustworthyKedlaya.Kedlaya.UPAlgebraic
public import TrustworthyKedlaya.Kedlaya.SeparableUP

/-!
# The truncationwise-UP elements are the closure of the algebraic-coefficient set

The closure identification of Kedlaya 2001b/2017: inside `𝕃_[p]`, the closure
of the set `A` of elements whose canonical coefficient function is the coefficient
function of a Hahn series algebraic over `𝔽̄_p((t))` equals the set `B'` of
truncationwise-UP elements (`IsTruncUP`, from `TrustworthyKedlaya.Kedlaya.WittCarryUP`).

* `A ⊆ B'`: such an element *is* the shadow of its algebraic (hence integral,
  hence UP by `UP.isUP_of_isIntegral`) coefficient series, and shadows of UP
  series are truncationwise UP; `B'` is `p`-adically closed
  (`isTruncUP_of_forall_exists_near`), so `closure A ⊆ B'`.
* `B' ⊆ closure A`: for `g ∈ B'` and a cutoff `n` the truncation
  `trunc n g` is UP, hence algebraic over the Laurent field (`UP.IsUP.isAlgebraic`),
  and its shadow approximates `g` to valuation `≥ n` (`le_val_sub_shadow_trunc`).

The topological bridge is `mem_closure_of_forall_exists_near` /
`exists_near_of_mem_closure`: membership in a closure for the valued topology of
`𝕃_[p]` (`Valued.mk' (val p)`) is equivalent to admitting approximants of
arbitrarily high valuation defect.  The valued topology's value group is
`Multiplicative (WithTop ℚ)ᵒᵈ`, definitionally the additive `WithTop ℚ` of
`val p`, so the comparisons transport by `rfl`.

## References

- K. S. Kedlaya, *The algebraic closure of the power series field in positive
  characteristic*, Proc. Amer. Math. Soc. 129 (2001) [Ked01b], Theorem 7.
- K. S. Kedlaya, *On the algebraicity of generalized power series*, Beiträge
  Algebra Geom. 58 (2017) [Ked17], Theorem 13.5.
-/

@[expose] public section

namespace TrustworthyKedlaya.pAdicHahnSeries

open scoped TrustworthyKedlaya.UP
open LaurentSeries

variable {p : ℕ} [Fact (Nat.Prime p)]

/-! ### Closure in the valued topology via valuation approximants -/

/-- An element admitting approximants in `S` of arbitrarily high valuation defect
lies in the closure of `S` (for the valued topology of `𝕃_[p]`). -/
theorem mem_closure_of_forall_exists_near {S : Set 𝕃_[p]} {g : 𝕃_[p]}
    (h : ∀ n : ℕ, ∃ a ∈ S, ((n : ℚ) : WithTop ℚ) ≤ val p (g - a)) :
    g ∈ closure S := by
  rw [mem_closure_iff_nhds]
  intro U hU
  rw [Valued.mem_nhds] at hU
  obtain ⟨γ, hγ⟩ := hU
  -- the ambient threshold of the ball, and its additive avatar
  have hc0 : MonoidWithZeroHom.ValueGroup₀.embedding γ.1 ≠ 0 :=
    MonoidWithZeroHom.ValueGroup₀.embedding_unit_ne_zero γ
  have hcne : OrderDual.ofDual (Multiplicative.toAdd
      (MonoidWithZeroHom.ValueGroup₀.embedding γ.1)) ≠ (⊤ : WithTop ℚ) := by
    intro htop
    apply hc0
    calc MonoidWithZeroHom.ValueGroup₀.embedding γ.1
        = Multiplicative.ofAdd (OrderDual.toDual (OrderDual.ofDual (Multiplicative.toAdd
            (MonoidWithZeroHom.ValueGroup₀.embedding γ.1)))) := rfl
      _ = Multiplicative.ofAdd (OrderDual.toDual (⊤ : WithTop ℚ)) := by rw [htop]
      _ = 0 := rfl
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hcne
  obtain ⟨n, hn⟩ := exists_nat_gt r
  obtain ⟨a, haS, hval⟩ := h n
  have hswap : val p (a - g) = val p (g - a) := by
    rw [← neg_sub, (val p).map_neg]
  have hlt : OrderDual.ofDual (Multiplicative.toAdd
      (MonoidWithZeroHom.ValueGroup₀.embedding γ.1)) < val p (a - g) := by
    rw [← hr, hswap]
    exact lt_of_lt_of_le (by exact_mod_cast hn) hval
  have hball : Valued.v.restrict (a - g) < γ := by
    rw [Valuation.restrict_lt_iff_lt_embedding]
    exact hlt
  exact ⟨a, hγ hball, haS⟩

/-- Conversely, an element of the closure of `S` admits approximants in `S` of
arbitrarily high valuation defect. -/
theorem exists_near_of_mem_closure {S : Set 𝕃_[p]} {g : 𝕃_[p]}
    (hg : g ∈ closure S) (n : ℕ) :
    ∃ a ∈ S, ((n : ℚ) : WithTop ℚ) ≤ val p (g - a) := by
  rw [mem_closure_iff_nhds] at hg
  -- the radius-`n` ball at `g`, witnessed by the one-term series of valuation `n`
  have hwit : val p (single (p := p) (n : ℚ) (1 : 𝔽ᵃ_[p])) = ((n : ℚ) : WithTop ℚ) :=
    val_single _ one_ne_zero
  have hane : Valued.v.restrict (single (p := p) (n : ℚ) (1 : 𝔽ᵃ_[p])) ≠ 0 := by
    rw [ne_eq, Valuation.restrict_eq_zero_iff]
    intro h0
    have htop : val p (single (p := p) (n : ℚ) (1 : 𝔽ᵃ_[p])) = ⊤ := h0
    rw [hwit] at htop
    exact WithTop.coe_ne_top htop
  have hnhds : {y : 𝕃_[p] | Valued.v.restrict (y - g)
      < Units.mk0 (Valued.v.restrict (single (p := p) (n : ℚ) (1 : 𝔽ᵃ_[p]))) hane}
      ∈ nhds g := by
    rw [Valued.mem_nhds]
    exact ⟨Units.mk0 _ hane, subset_rfl⟩
  obtain ⟨a, haU, haS⟩ := hg _ hnhds
  refine ⟨a, haS, ?_⟩
  simp only [Set.mem_ofPred_eq] at haU
  rw [Valuation.restrict_lt_iff_lt_embedding, Units.val_mk0,
    Valuation.embedding_restrict] at haU
  -- additively: `val p (single n 1) < val p (a - g)`, i.e. `n < val p (a - g)`
  have hlt : ((n : ℚ) : WithTop ℚ) < val p (a - g) := by
    rw [← hwit]
    exact haU
  have hswap : val p (a - g) = val p (g - a) := by
    rw [← neg_sub, (val p).map_neg]
  rw [hswap] at hlt
  exact hlt.le

/-! ### The closure bridge -/

/-- **The truncationwise-UP elements are the closure of the algebraic-coefficient
set** (the first step of Kedlaya 2001b, Theorem 7 /
Kedlaya 2017, Theorem 13.5): the closure of the set of `f ∈ 𝕃_[p]` whose
canonical coefficient function is the coefficient function of a Hahn series
algebraic over `𝔽̄_p((t))` is exactly the set `B'` of truncationwise-UP elements
(`IsTruncUP`). -/
theorem closure_algebraic_coeff_eq_setOf_isTruncUP :
    closure {f : 𝕃_[p] | ∃ f' : HahnSeries ℚ (𝔽ᵃ_[p]),
        IsAlgebraic ((𝔽ᵃ_[p])⸨X⸩) f' ∧ coeff f = f'.coeff}
      = {g : 𝕃_[p] | IsTruncUP g} := by
  apply Set.Subset.antisymm
  · -- `closure A ⊆ B'`: `A` consists of shadows of UP series, and `B'` is closed
    intro g hg
    refine isTruncUP_of_forall_exists_near fun n => ?_
    obtain ⟨a, haS, hval⟩ := exists_near_of_mem_closure hg n
    obtain ⟨f', hf'alg, hf'coeff⟩ := haS
    refine ⟨a, ?_, hval⟩
    have ha : a = shadow f' := by
      rw [← shadow_coeffSeries a]
      congr 1
      exact HahnSeries.ext hf'coeff
    rw [ha]
    exact isTruncUP_shadow (UP.isUP_of_isIntegral hf'alg.isIntegral)
  · -- `B' ⊆ closure A`: truncations are UP, hence algebraic, and their shadows
    -- approximate to the cutoff
    intro g hg
    refine mem_closure_of_forall_exists_near fun n => ?_
    have hUP : UP.IsUP p (trunc ((n : ℤ) : ℚ) g) := hg.trunc_intCast (n : ℤ)
    rw [Int.cast_natCast] at hUP
    exact ⟨shadow (trunc (n : ℚ) g),
      ⟨trunc (n : ℚ) g, hUP.isAlgebraic, coeff_shadow _⟩,
      le_val_sub_shadow_trunc (n : ℚ) g⟩

end TrustworthyKedlaya.pAdicHahnSeries
