/-
Copyright (c) 2026 Shanwen Wang, Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import TrustworthyKedlaya.FrobeniusUP
public import TrustworthyKedlaya.TowerEmbedding
public import Mathlib.RingTheory.Polynomial.SeparableDegree

/-!
# Integral elements of the Hahn field are UP

A Hahn series `x ∈ 𝔽̄_p((t^ℚ))` that is integral over `B = 𝔽̄_p((t))` is
uniformly periodic (Kedlaya (2001a), proof of Theorem 15; `lem:separable-up`
and `thm:integral-implies-up` of the blueprint).

Separable case: the splitting field `L` of the minimal polynomial `P` is finite
Galois over `B` (the normal closure of `B(x)`), so it embeds over `B` into
`𝔽̄_p((t^ℚ))` with UP image by `TrustworthyKedlaya.UP.exists_ringHom_forall_isUP`.
The images of the `deg P` distinct roots of `P` in `L` are `deg P` distinct
roots of `P` in `𝔽̄_p((t^ℚ))`; since `P` has at most `deg P` roots there and `x`
is one of them, `x` lies in the (UP) image.

General case: in characteristic `p` the minimal polynomial is `Q(X^{p^e})` with
`Q` separable (separable contraction), so `x^{p^e}` is UP by the separable case
and `x` is UP by iterated inverse-Frobenius stability
(`TrustworthyKedlaya.UP.IsUP.of_pow_pow`).

## Main statements

- `TrustworthyKedlaya.UP.isUP_of_isIntegral_separable`: the separable case
  (`lem:separable-up`).
- `TrustworthyKedlaya.UP.isUP_of_isIntegral`: the general case
  (`thm:integral-implies-up`).

## References

- K. S. Kedlaya, *The algebraic closure of the power series field in positive
  characteristic*, Proc. Amer. Math. Soc. 129 (2001) [Ked01a], proof of Theorem 15.
-/

@[expose] public section

namespace TrustworthyKedlaya.UP

open LaurentSeries Polynomial

variable {p : ℕ} [hp : Fact (Nat.Prime p)]

/-- **Separable algebraic elements are UP** (`lem:separable-up`): a Hahn series
integral over `𝔽̄_p((t))` with separable minimal polynomial is uniformly periodic. -/
theorem isUP_of_isIntegral_separable {x : HahnSeries ℚ (𝔽ᵃ_[p])}
    (hint : IsIntegral ((𝔽ᵃ_[p])⸨X⸩) x)
    (hsep : (minpoly ((𝔽ᵃ_[p])⸨X⸩) x).Separable) : IsUP p x := by
  classical
  set P := minpoly ((𝔽ᵃ_[p])⸨X⸩) x with hP_def
  -- the splitting field of `P` is the normal closure of `B(x)`: finite Galois over `B`
  have : IsGalois ((𝔽ᵃ_[p])⸨X⸩) P.SplittingField :=
    IsGalois.of_separable_splitting_field hsep
  obtain ⟨τ, hcomp, hUP⟩ := exists_ringHom_forall_isUP (p := p) (L := P.SplittingField)
  -- mapping `P` into the Hahn field through `L` is the same as through the base
  have hmapmap : (P.map (algebraMap ((𝔽ᵃ_[p])⸨X⸩) P.SplittingField)).map τ
      = P.map (intHahnEmbedding p) := by
    rw [Polynomial.map_map]
    congr 1
    exact RingHom.ext hcomp
  have hP0 : P ≠ 0 := minpoly.ne_zero hint
  have hmap0 : P.map (intHahnEmbedding p) ≠ 0 := Polynomial.map_ne_zero hP0
  -- the `deg P` distinct roots of `P` in the splitting field, pushed into the Hahn field
  set R := (P.map (algebraMap ((𝔽ᵃ_[p])⸨X⸩) P.SplittingField)).roots with hR_def
  have hRnodup : R.Nodup := Polynomial.nodup_roots hsep.map
  have hRcard : Multiset.card R = P.natDegree := by
    rw [hR_def, Polynomial.splits_iff_card_roots.mp (SplittingField.splits P),
      Polynomial.natDegree_map]
  set S := R.toFinset.image τ with hS_def
  have hScard : S.card = P.natDegree := by
    rw [hS_def, Finset.card_image_of_injective _ τ.injective,
      Multiset.toFinset_card_of_nodup hRnodup, hRcard]
  have hSroots : ∀ z ∈ S, (P.map (intHahnEmbedding p)).IsRoot z := by
    intro z hz
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hz
    have hrroot : (P.map (algebraMap ((𝔽ᵃ_[p])⸨X⸩) P.SplittingField)).IsRoot r :=
      Polynomial.isRoot_of_mem_roots (Multiset.mem_toFinset.mp hr)
    have := hrroot.map (f := τ)
    rwa [hmapmap] at this
  -- `x` is a root of `P` over the Hahn field
  have hxroot : (P.map (intHahnEmbedding p)).IsRoot x := by
    have := minpoly.aeval ((𝔽ᵃ_[p])⸨X⸩) x
    rwa [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map] at this
  -- `P` has at most `deg P` roots in the Hahn field, so `x` is one of the images
  by_contra hxUP
  have hxS : x ∉ S := fun hxS => by
    obtain ⟨r, -, hr⟩ := Finset.mem_image.mp hxS
    exact hxUP (hr ▸ hUP r)
  have hsub : insert x S ⊆ (P.map (intHahnEmbedding p)).roots.toFinset := by
    intro z hz
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hmap0]
    rcases Finset.mem_insert.mp hz with rfl | hzS
    · exact hxroot
    · exact hSroots z hzS
  have hle := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hxS, hScard] at hle
  have h1 := (P.map (intHahnEmbedding p)).roots.toFinset_card_le
  have h2 : Multiset.card (P.map (intHahnEmbedding p)).roots ≤ P.natDegree := by
    have := (P.map (intHahnEmbedding p)).card_roots'
    rwa [Polynomial.natDegree_map] at this
  omega

/-- **Integral over `𝔽̄_p((t))` implies uniformly periodic**
(`thm:integral-implies-up`; Kedlaya (2001a), Theorem 15, one direction): every
Hahn series integral over `𝔽̄_p((t))` is uniformly periodic.  In characteristic
`p` the minimal polynomial is `Q(X^{p^e})` with `Q` separable, so `x^{p^e}` is
UP by the separable case, and `x` is UP by inverse-Frobenius stability. -/
theorem isUP_of_isIntegral {x : HahnSeries ℚ (𝔽ᵃ_[p])}
    (hint : IsIntegral ((𝔽ᵃ_[p])⸨X⸩) x) : IsUP p x := by
  have hCharB : CharP ((𝔽ᵃ_[p])⸨X⸩) p :=
    charP_of_injective_algebraMap (algebraMap (𝔽ᵃ_[p]) ((𝔽ᵃ_[p])⸨X⸩)).injective p
  -- contract the minimal polynomial to a separable polynomial `Q` with `Q(X^{p^e}) = P`
  obtain ⟨Q, hQsep, e, hQe⟩ := (minpoly.irreducible hint).hasSeparableContraction p
  -- `x^{p^e}` is integral with separable minimal polynomial, hence UP
  have hzQ : Polynomial.aeval (x ^ p ^ e) Q = 0 := by
    rw [← Polynomial.expand_aeval (p ^ e) Q x, hQe]
    exact minpoly.aeval _ _
  have hzsep : (minpoly ((𝔽ᵃ_[p])⸨X⸩) (x ^ p ^ e)).Separable :=
    hQsep.of_dvd (minpoly.dvd _ _ hzQ)
  exact IsUP.of_pow_pow (isUP_of_isIntegral_separable (hint.pow _) hzsep)

end TrustworthyKedlaya.UP
