/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.GroupTheory.IndexNormal
public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.Sylow

/-!
# One step of a `p`-group Galois tower

Let `E/F` be a finite Galois extension whose Galois group is a `p`-group of order `> 1`.
This file proves that `E/F` contains a degree-`p` Galois subextension with a `p`-group
remainder on top: there is an intermediate field `M` with `M/F` Galois of degree `p` and
`Gal(E/M)` again a `p`-group (`TrustworthyKedlaya.exists_intermediateField_isGalois_of_isPGroup`).
Iterating this step exhibits `E` as the top of a tower of degree-`p` Galois extensions
over `F`; consumers perform that iteration as an induction on the degree.

The proof: `Gal(E/F)` has order `p^n` with `n ≥ 1`, so by Sylow's theorem it has a
subgroup `H` of order `p^{n-1}`; its index `p` is the smallest prime factor of the group
order, so `H` is normal, and the Galois correspondence turns `H` into the required
intermediate field `M = E^H`.

This is Lemma `lem:p-group-tower` of the blueprint (Kedlaya 2001a, proof of Lemma 3).
-/

@[expose] public section

namespace TrustworthyKedlaya

/-- **One step of a `p`-group Galois tower**: a finite Galois extension `E/F` of degree
`> 1` whose Galois group is a `p`-group has an intermediate field `M` such that `M/F` is
Galois of degree `p` and `Gal(E/M)` is again a `p`-group. -/
theorem exists_intermediateField_isGalois_of_isPGroup
    (p : ℕ) [Fact p.Prime] {F E : Type*} [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] [IsGalois F E]
    (hG : IsPGroup p (E ≃ₐ[F] E)) (hlt : 1 < Module.finrank F E) :
    ∃ M : IntermediateField F E, IsGalois F M ∧ Module.finrank F M = p ∧
      IsPGroup p (E ≃ₐ[M] E) := by
  have hp : p.Prime := Fact.out
  -- The Galois group has order `p^n` with `n ≥ 1`.
  have hcard : Nat.card (E ≃ₐ[F] E) = Module.finrank F E := IsGalois.card_aut_eq_finrank F E
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hG
  have hn1 : n ≠ 0 := by
    rintro rfl
    rw [hn, pow_zero] at hcard
    omega
  -- A subgroup of order `p^{n-1}`, hence of index `p`.
  obtain ⟨H, hHcard⟩ := Sylow.exists_subgroup_card_pow_prime (G := E ≃ₐ[F] E) p
    (n := n - 1) (by rw [hn]; exact pow_dvd_pow p (Nat.sub_le n 1))
  have hidx : H.index = p := by
    have hmul := Subgroup.card_mul_index H
    rw [hHcard, hn, ← pow_sub_one_mul hn1 p] at hmul
    exact Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos _) hmul
  -- The index is the smallest prime factor of the group order, so `H` is normal.
  have hnormal : H.Normal := Subgroup.normal_of_index_eq_minFac_card
    (by rw [hidx, hn, hp.pow_minFac hn1])
  refine ⟨IntermediateField.fixedField H, IsGalois.of_fixedField_normal_subgroup H, ?_, ?_⟩
  · -- `[E^H : F] = p` by the degree formula and `[E : E^H] = |H| = p^{n-1}`.
    have h1 : Module.finrank (IntermediateField.fixedField H) E = p ^ (n - 1) := by
      rw [IntermediateField.finrank_fixedField_eq_card, hHcard]
    have h2 := Module.finrank_mul_finrank F (IntermediateField.fixedField H) E
    rw [h1, ← hcard, hn, ← pow_sub_one_mul hn1 p, mul_comm (p ^ (n - 1)) p] at h2
    exact Nat.eq_of_mul_eq_mul_right (pow_pos hp.pos _) h2
  · -- `Gal(E/E^H) ≅ H` is again a `p`-group.
    exact (hG.to_subgroup H).of_equiv (IntermediateField.subgroupEquivAlgEquiv H)

end TrustworthyKedlaya
