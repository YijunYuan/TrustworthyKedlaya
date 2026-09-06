/-
Copyright (c) 2026 Shanwen Wang, Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import TrustworthyKedlaya.Kedlaya.ApproxByIntegral

/-!
# Algebraic coefficient functions give completed-integral elements

This file proves Kedlaya 2001b, Theorem 7, part 2 (Kedlaya 2017, Theorem
13.5): the shadow of a Hahn series integral over `𝔽̄_p((t))` lies in the
closure `C` of the integral closure of `ℚᶜᵘⁿ_[p]` in `𝕃_[p]`, and consequently
the closure of the algebraic-coefficient set equals `C`.

The iteration consumes the full-unit-gain approximation by integral elements
exactly as the source does: the shadow `f = S(f')` is truncationwise UP,
each residual `f - g` stays in `B'` because `C ⊆ B'` (`B'` contains the
integral elements and is `p`-adically closed) and `B'` is closed under
subtraction, so every stage gains a full unit of valuation and the partial
sums converge to `f` inside the closed set `C`.

## Main statements

- `TrustworthyKedlaya.pAdicHahnSeries.isTruncUP_of_mem_closure_integralClosure`:
  `C ⊆ B'`.
- `TrustworthyKedlaya.pAdicHahnSeries.shadow_mem_closure_integralClosure_of_isIntegral`:
  the iterated approximation.
- `TrustworthyKedlaya.pAdicHahnSeries.closure_integralClosure_eq_closure_algebraic_coeff`:
  the two closures coincide (Kedlaya 2017, Theorem 13.4).

## References

- K. S. Kedlaya, *Power series and `p`-adic algebraic closures*, J. Number
  Theory 89 (2001) [Ked01b], pp. 335–336 (published version), Theorem 7.
- K. S. Kedlaya, *On the algebraicity of generalized power series*, Beiträge
  Algebra Geom. 58 (2017) [Ked17], Theorem 13.5.
-/

@[expose] public section

namespace TrustworthyKedlaya.pAdicHahnSeries

open scoped TrustworthyKedlaya.UP
open LaurentSeries

variable {p : ℕ} [hp : Fact (Nat.Prime p)]

/-- Every element of the closure of the integral closure of `ℚᶜᵘⁿ_[p]` is
truncationwise UP: `C ⊆ B'` (`B'` is `p`-adically closed and contains the
integral elements). -/
theorem isTruncUP_of_mem_closure_integralClosure {z : 𝕃_[p]}
    (hz : z ∈ closure (integralClosure ℚᶜᵘⁿ_[p] 𝕃_[p]).carrier) : IsTruncUP z := by
  refine isTruncUP_of_forall_exists_near fun n => ?_
  obtain ⟨a, haS, hval⟩ := exists_near_of_mem_closure hz n
  exact ⟨a, isTruncUP_of_isIntegral_QpCUn haS, hval⟩

/-- **Shadows of integral Hahn series are completed-integral**
(the iteration): the shadow of a Hahn series
integral over `𝔽̄_p((t))` lies in the closure of the integral closure of
`ℚᶜᵘⁿ_[p]` in `𝕃_[p]`.  Iterate the full unit gain of the approximation by
integral elements, staying inside `B'` at every stage. -/
theorem shadow_mem_closure_integralClosure_of_isIntegral
    {f' : HahnSeries ℚ (𝔽ᵃ_[p])} (hf' : IsIntegral ((𝔽ᵃ_[p])⸨X⸩) f') :
    shadow f' ∈ closure (integralClosure ℚᶜᵘⁿ_[p] 𝕃_[p]).carrier := by
  classical
  set f : 𝕃_[p] := shadow f' with hf
  have hfB : IsTruncUP f := isTruncUP_shadow (UP.isUP_of_isIntegral hf')
  by_cases hf0 : f = 0
  · rw [hf0]
    exact subset_closure (Subalgebra.zero_mem _)
  have hne : val p f ≠ ⊤ := fun h => hf0 (val_eq_top_iff.mp h)
  obtain ⟨s₀, hs₀⟩ := WithTop.ne_top_iff_exists.mp hne
  -- at every stage `k` there is an approximant in `C` at depth `s₀ + k`
  have hiter : ∀ k : ℕ, ∃ g ∈ closure (integralClosure ℚᶜᵘⁿ_[p] 𝕃_[p]).carrier,
      ((s₀ + k : ℚ) : WithTop ℚ) ≤ val p (f - g) := by
    intro k
    induction k with
    | zero =>
      refine ⟨0, subset_closure (Subalgebra.zero_mem _), ?_⟩
      rw [sub_zero, ← hs₀, WithTop.coe_le_coe]
      simp
    | succ k ih =>
      obtain ⟨g, hgC, hgval⟩ := ih
      by_cases hr0 : f - g = 0
      · refine ⟨g, hgC, ?_⟩
        rw [hr0, (val p).map_zero]
        exact le_top
      · have hrB : IsTruncUP (f - g) := by
          rw [sub_eq_add_neg]
          exact hfB.add (isTruncUP_of_mem_closure_integralClosure hgC).neg
        have hrne : val p (f - g) ≠ ⊤ := fun h => hr0 (val_eq_top_iff.mp h)
        obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.mp hrne
        obtain ⟨z, hzC, hzval⟩ :=
          exists_mem_closure_integralClosure_near_of_isTruncUP hrB hs.symm
        refine ⟨g + z, add_mem_closure_integralClosure hgC hzC, ?_⟩
        have hsub : f - (g + z) = (f - g) - z := by ring
        rw [hsub]
        refine le_trans ?_ hzval
        rw [WithTop.coe_le_coe]
        have h1 : (s₀ + k : ℚ) ≤ s := by
          rw [← WithTop.coe_le_coe, hs]
          exact hgval
        push_cast
        linarith
  -- `f` is approximated at arbitrary depth by elements of the closed set `C`
  have hmem : f ∈ closure (closure (integralClosure ℚᶜᵘⁿ_[p] 𝕃_[p]).carrier) := by
    refine mem_closure_of_forall_exists_near fun N => ?_
    obtain ⟨kN, hkN⟩ := exists_nat_ge ((N : ℚ) - s₀)
    obtain ⟨g, hgC, hgval⟩ := hiter kN
    refine ⟨g, hgC, le_trans ?_ hgval⟩
    rw [WithTop.coe_le_coe]
    linarith
  rwa [closure_closure] at hmem

/-- **Algebraic coefficient functions give completed-integral elements**
(closure form): the closure of the
algebraic-coefficient set is contained in the closure of the integral closure
of `ℚᶜᵘⁿ_[p]`. -/
theorem closure_algebraic_coeff_subset_closure_integralClosure :
    closure {g : 𝕃_[p] | ∃ f' : HahnSeries ℚ (𝔽ᵃ_[p]),
        IsAlgebraic ((𝔽ᵃ_[p])⸨X⸩) f' ∧ coeff g = f'.coeff}
      ⊆ closure (integralClosure ℚᶜᵘⁿ_[p] 𝕃_[p]).carrier := by
  refine closure_minimal ?_ isClosed_closure
  rintro g ⟨f', hf'alg, hf'coeff⟩
  have hg : g = shadow f' := by
    rw [← shadow_coeffSeries g]
    congr 1
    exact HahnSeries.ext hf'coeff
  rw [hg]
  exact shadow_mem_closure_integralClosure_of_isIntegral hf'alg.isIntegral

/-- **Kedlaya (2017), Theorem 13.4 / Kedlaya (2001b), Theorem 7**
(stated below `MainResults.lean` in the import graph):
the closure of the integral closure of `ℚᶜᵘⁿ_[p]` in `𝕃_[p]` coincides with the
closure of the set of elements whose canonical coefficient function is the
coefficient function of a Hahn series algebraic over `𝔽̄_p((t))`. -/
theorem closure_integralClosure_eq_closure_algebraic_coeff :
    closure (integralClosure ℚᶜᵘⁿ_[p] 𝕃_[p]).carrier
      = closure {g : 𝕃_[p] | ∃ f' : HahnSeries ℚ (𝔽ᵃ_[p]),
          IsAlgebraic ((𝔽ᵃ_[p])⸨X⸩) f' ∧ coeff g = f'.coeff} := by
  refine Set.Subset.antisymm ?_ closure_algebraic_coeff_subset_closure_integralClosure
  refine closure_minimal ?_ isClosed_closure
  intro x hx
  exact mem_closure_algebraic_coeff_of_isIntegral hx

end TrustworthyKedlaya.pAdicHahnSeries
