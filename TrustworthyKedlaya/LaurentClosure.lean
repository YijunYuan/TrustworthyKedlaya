/-
Copyright (c) 2026 Shanwen Wang, Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import TrustworthyKedlaya.SeparableUP
public import Mathlib.FieldTheory.AlgebraicClosure
public import Mathlib.FieldTheory.Isaacs
public import Mathlib.Algebra.Polynomial.Expand

/-!
# The algebraic closure of `𝔽̄_p((t))` inside the Hahn field

Every polynomial over `B = 𝔽̄_p((t))` splits over the Hahn field `𝔽̄_p((t^ℚ))`, so the
relative algebraic closure of `B` in the Hahn field is an algebraic closure of `B`
(Kedlaya 2001a, Theorem 15 / 2001b; blueprint `lem:laurent-closure-in-hahn`).

The route: factor into irreducibles (`B[X]` is a UFD).  An irreducible `P` has a
separable contraction `P = Q(X^{p^e})`; the splitting field of the separable `Q` is
finite Galois over `B`, so it embeds into the Hahn field over `B`
(`TrustworthyKedlaya.UP.exists_ringHom_forall_isUP`, the Artin-Schreier tower), whence
`Q` splits there.  The Hahn field is perfect (`TrustworthyKedlaya.pow_char_bijective`),
so each linear factor `X - y` of `Q` contributes `(X - y^{1/pᵉ})^{pᵉ}` to `Q(X^{pᵉ})`,
and `P` splits as well.  Finally, an algebraic extension of `B` in which every monic
irreducible polynomial over `B` has a root is an algebraic closure of `B` (Isaacs'
theorem, `IsAlgClosure.of_exists_root`), applied to the relative algebraic closure.

## Main declarations

- `TrustworthyKedlaya.UP.splits_expand_pow_char`: over a perfect field of
  characteristic `q`, `Splits g` implies `Splits (expand (q^e) g)`;
- `TrustworthyKedlaya.UP.splits_map_intHahnEmbedding`: every polynomial over
  `𝔽̄_p((t))` splits over the Hahn field;
- `TrustworthyKedlaya.UP.exists_eval_map_intHahnEmbedding_eq_zero`: root existence;
- `TrustworthyKedlaya.UP.isAlgClosure_algebraicClosure`: the relative algebraic
  closure of `𝔽̄_p((t))` in `𝔽̄_p((t^ℚ))` is an algebraic closure of `𝔽̄_p((t))`.
-/

@[expose] public section

namespace TrustworthyKedlaya.UP

open LaurentSeries Polynomial

variable (p : ℕ) [hp : Fact (Nat.Prime p)]

/-- The Hahn field `𝔽̄_p((t^ℚ))` is perfect: its Frobenius is bijective
(`TrustworthyKedlaya.pow_char_bijective`, coefficientwise inverse plus support
scaling). -/
instance : PerfectRing (HahnSeries ℚ (𝔽ᵃ_[p])) p := ⟨pow_char_bijective⟩

/-! ### Splitting is stable under `expand` over a perfect field -/

/-- Over a perfect field of characteristic `q`, if `g` splits then so does
`g(X^q)`: each linear factor `X - a` contributes `(X - a^{1/q})^q`. -/
theorem splits_expand_char {K : Type*} [Field K] {q : ℕ} [Fact q.Prime] [CharP K q]
    [PerfectRing K q] {g : K[X]} (hg : g.Splits) : (expand K q g).Splits := by
  have hCharKX : CharP K[X] q := charP_of_injective_ringHom Polynomial.C_injective q
  obtain ⟨m, hm⟩ := splits_iff_exists_multiset.mp hg
  rw [hm, map_mul, expand_C, map_multiset_prod]
  refine (Splits.C _).mul (Splits.multisetProd ?_)
  intro f hf
  rw [Multiset.map_map, Multiset.mem_map] at hf
  obtain ⟨a, -, rfl⟩ := hf
  have hroot : (X - C ((frobeniusEquiv K q).symm a) : K[X]) ^ q = expand K q (X - C a) := by
    rw [sub_pow_char, map_sub, expand_X, expand_C, ← Polynomial.C_pow,
      frobeniusEquiv_symm_pow_p]
  rw [Function.comp_apply, ← hroot]
  exact (Splits.X_sub_C _).pow q

/-- Over a perfect field of characteristic `q`, if `g` splits then so does
`g(X^{q^e})`. -/
theorem splits_expand_pow_char {K : Type*} [Field K] {q : ℕ} [Fact q.Prime] [CharP K q]
    [PerfectRing K q] {g : K[X]} (hg : g.Splits) (e : ℕ) : (expand K (q ^ e) g).Splits := by
  induction e with
  | zero => simpa [expand_one] using hg
  | succ e ih =>
    rw [pow_succ', ← expand_expand]
    exact splits_expand_char ih

/-! ### Every polynomial over `𝔽̄_p((t))` splits over the Hahn field -/

/-- A **separable** polynomial over `𝔽̄_p((t))` splits over the Hahn field: its
splitting field is finite Galois over `𝔽̄_p((t))` and embeds into the Hahn field by
the Artin-Schreier tower (`lem:tower-embedding`). -/
theorem splits_map_intHahnEmbedding_of_separable {Q : ((𝔽ᵃ_[p])⸨X⸩)[X]}
    (hsep : Q.Separable) : (Q.map (intHahnEmbedding p)).Splits := by
  have : IsGalois ((𝔽ᵃ_[p])⸨X⸩) Q.SplittingField :=
    IsGalois.of_separable_splitting_field hsep
  obtain ⟨τ, hcomp, -⟩ := exists_ringHom_forall_isUP (p := p) (L := Q.SplittingField)
  have h1 : (Q.map (algebraMap ((𝔽ᵃ_[p])⸨X⸩) Q.SplittingField)).Splits :=
    SplittingField.splits Q
  have h2 := h1.map τ
  rwa [Polynomial.map_map,
    show τ.comp (algebraMap ((𝔽ᵃ_[p])⸨X⸩) Q.SplittingField) = intHahnEmbedding p from
      RingHom.ext hcomp] at h2

/-- An **irreducible** polynomial over `𝔽̄_p((t))` splits over the Hahn field: it is
`Q(X^{p^e})` for a separable `Q` (separable contraction), `Q` splits by the Galois
case, and `expand` preserves splitting over the perfect Hahn field. -/
theorem splits_map_intHahnEmbedding_of_irreducible {P : ((𝔽ᵃ_[p])⸨X⸩)[X]}
    (hirr : Irreducible P) : (P.map (intHahnEmbedding p)).Splits := by
  have hCharB : CharP ((𝔽ᵃ_[p])⸨X⸩) p :=
    charP_of_injective_algebraMap (algebraMap (𝔽ᵃ_[p]) ((𝔽ᵃ_[p])⸨X⸩)).injective p
  obtain ⟨Q, hQsep, e, hQe⟩ := hirr.hasSeparableContraction p
  have hkey : P.map (intHahnEmbedding p)
      = expand (HahnSeries ℚ (𝔽ᵃ_[p])) (p ^ e) (Q.map (intHahnEmbedding p)) := by
    rw [← hQe, map_expand]
  rw [hkey]
  exact splits_expand_pow_char (splits_map_intHahnEmbedding_of_separable p hQsep) e

/-- **Every polynomial over `𝔽̄_p((t))` splits over the Hahn field `𝔽̄_p((t^ℚ))`**
(`lem:laurent-closure-in-hahn`): factor into irreducibles and split each factor. -/
theorem splits_map_intHahnEmbedding (f : ((𝔽ᵃ_[p])⸨X⸩)[X]) :
    (f.map (intHahnEmbedding p)).Splits := by
  induction f using WfDvdMonoid.induction_on_irreducible with
  | zero => simp
  | unit u hu =>
    exact Splits.of_natDegree_eq_zero
      (by rw [Polynomial.natDegree_map]; exact natDegree_eq_zero_of_isUnit hu)
  | mul a i ha0 hirr ih =>
    rw [Polynomial.map_mul]
    exact (splits_map_intHahnEmbedding_of_irreducible p hirr).mul ih

/-- Root existence in the Hahn field for nonconstant polynomials over `𝔽̄_p((t))`. -/
theorem exists_eval_map_intHahnEmbedding_eq_zero {f : ((𝔽ᵃ_[p])⸨X⸩)[X]}
    (hdeg : f.natDegree ≠ 0) :
    ∃ x : HahnSeries ℚ (𝔽ᵃ_[p]), (f.map (intHahnEmbedding p)).eval x = 0 := by
  refine (splits_map_intHahnEmbedding p f).exists_eval_eq_zero ?_
  rw [Polynomial.degree_map]
  exact degree_ne_of_natDegree_ne hdeg

/-! ### The relative algebraic closure is an algebraic closure -/

/-- **The relative algebraic closure of `𝔽̄_p((t))` in the Hahn field is an algebraic
closure of `𝔽̄_p((t))`** (`lem:laurent-closure-in-hahn`; Kedlaya 2001a/2001b): it is
algebraic by definition, and every monic irreducible polynomial over `𝔽̄_p((t))` has a
root in it (the root in the Hahn field is integral, hence lies in the relative
algebraic closure), so Isaacs' theorem applies. -/
instance isAlgClosure_algebraicClosure :
    IsAlgClosure ((𝔽ᵃ_[p])⸨X⸩)
      (algebraicClosure ((𝔽ᵃ_[p])⸨X⸩) (HahnSeries ℚ (𝔽ᵃ_[p]))) := by
  refine IsAlgClosure.of_exists_root fun P hmonic hirr => ?_
  obtain ⟨x, hx⟩ := exists_eval_map_intHahnEmbedding_eq_zero p
    (f := P) hirr.natDegree_pos.ne'
  have haev : Polynomial.aeval x P = 0 := by
    rwa [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
  have hxint : IsIntegral ((𝔽ᵃ_[p])⸨X⸩) x := ⟨P, hmonic, haev⟩
  have hmem : x ∈ algebraicClosure ((𝔽ᵃ_[p])⸨X⸩) (HahnSeries ℚ (𝔽ᵃ_[p])) :=
    mem_algebraicClosure_iff'.mpr hxint
  refine ⟨⟨x, hmem⟩, ?_⟩
  have hcoe : Polynomial.aeval (x : HahnSeries ℚ (𝔽ᵃ_[p])) P
      = ((Polynomial.aeval (⟨x, hmem⟩ :
          algebraicClosure ((𝔽ᵃ_[p])⸨X⸩) (HahnSeries ℚ (𝔽ᵃ_[p])))) P
        : HahnSeries ℚ (𝔽ᵃ_[p])) :=
    IntermediateField.aeval_coe _
      (⟨x, hmem⟩ : algebraicClosure ((𝔽ᵃ_[p])⸨X⸩) (HahnSeries ℚ (𝔽ᵃ_[p]))) P
  rw [haev] at hcoe
  exact_mod_cast hcoe.symm

/-- The relative algebraic closure of `𝔽̄_p((t))` in the Hahn field is algebraically
closed. -/
instance : IsAlgClosed
    (algebraicClosure ((𝔽ᵃ_[p])⸨X⸩) (HahnSeries ℚ (𝔽ᵃ_[p]))) :=
  (isAlgClosure_algebraicClosure p).isAlgClosed

end TrustworthyKedlaya.UP
