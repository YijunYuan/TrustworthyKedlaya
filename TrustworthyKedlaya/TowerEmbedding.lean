/-
Copyright (c) 2026 Shanwen Wang, Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import TrustworthyKedlaya.ArtinSchreierClosure
public import TrustworthyKedlaya.GaloisTower
public import TrustworthyKedlaya.Multiplicative
public import TrustworthyKedlaya.Rescale
public import TrustworthyKedlaya.Additive
public import TrustworthyKedlaya.Frobenius
public import Mathlib.FieldTheory.KummerExtension
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# Embedding the Artin-Schreier tower with UP image

Every finite Galois extension `L` of `B = 𝔽̄_p((t))` embeds over `B` into the Hahn
field `𝔽̄_p((t^ℚ))` with image consisting of uniformly periodic series (Kedlaya
(2001a), proof of Theorem 15).

The Artin-Schreier tower `B(t^{1/n}) = M₀ ≤ ⋯ ≤ M_r = L` of
`TrustworthyKedlaya.Ext.exists_artinSchreier_tower` is embedded step by step:

* the base `B(u)` (`u^n = t`, `n` prime to `p`) goes to `𝔽̄_p((t^{1/n}))`: the
  minimal polynomial of `u` divides `X^n - t`, which splits over the Hahn field
  with roots `ζ^i t^{1/n}` (Kummer theory, `ζ` a primitive `n`-th root of unity of
  `𝔽̄_p`), and series supported on `(1/n)ℤ` are UP;
* each Artin-Schreier step `M_{i+1} = M_i(θ)`, `θ^p - θ = a ∈ M_i`, extends the
  embedding `τᵢ`: `X^p - X - τᵢ(a)` has a UP root (the UP series are Artin-Schreier
  closed), and translating by the `𝔽_p`-constants shows it splits, so the image of
  the minimal polynomial of `θ` has a root — necessarily UP — to send `θ` to;
* UP-ness of the image propagates because every element of a simple extension is a
  polynomial in the generator (UP series are closed under sums and products).

## Main statements

- `TrustworthyKedlaya.UP.intHahnEmbedding`: the inclusion `𝔽̄_p((t)) →+* 𝔽̄_p((t^ℚ))`
  (definitionally equal copy of the one in `Kedlaya.lean`; pinned in `DefeqGuards`).
- `TrustworthyKedlaya.UP.exists_ringHom_forall_isUP`: the embedding theorem.

## References

- K. S. Kedlaya, *The algebraic closure of the power series field in positive
  characteristic*, Proc. Amer. Math. Soc. 129 (2001) [Ked01a], proof of Theorem 15.
-/

@[expose] public section

namespace TrustworthyKedlaya.UP

open LaurentSeries IntermediateField

variable (p : ℕ) [hp : Fact (Nat.Prime p)]

/-- The order-embedding `ℤ ↪ ℚ` of value groups induces the ring inclusion of the
integer-supported Hahn series `𝔽̄_p((t))` into `𝔽̄_p((t^ℚ))` (definitionally equal
copy, below `Kedlaya.lean` in the import graph, of `intHahnEmbedding` there; the
`rfl`-guard lives in `DefeqGuards.lean`). -/
noncomputable def intHahnEmbedding :
    (𝔽ᵃ_[p])⸨X⸩ →+* HahnSeries ℚ (𝔽ᵃ_[p]) :=
  HahnSeries.embDomainRingHom (Int.castAddHom ℚ) Rat.intCast_injective
    (fun _ _ => by exact_mod_cast Int.cast_le)

/-- `intHahnEmbedding` sends single terms to single terms. -/
theorem intHahnEmbedding_single {g : ℤ} {r : 𝔽ᵃ_[p]} :
    intHahnEmbedding p (HahnSeries.single g r) = HahnSeries.single ((g : ℚ)) r :=
  HahnSeries.embDomain_single

/-- The `𝔽̄_p((t))`-algebra structure on `𝔽̄_p((t^ℚ))` induced by `intHahnEmbedding`
(scoped to `TrustworthyKedlaya.UP`; the global one for the target statements is
declared in `Kedlaya.lean`). -/
noncomputable scoped instance : Algebra (𝔽ᵃ_[p])⸨X⸩ (HahnSeries ℚ (𝔽ᵃ_[p])) :=
  (intHahnEmbedding p).toAlgebra

/-- The single term `t^0 = 1` is UP. -/
theorem isUP_one : IsUP p (1 : HahnSeries ℚ (𝔽ᵃ_[p])) := by
  simpa using isUP_single_zero p (1 : 𝔽ᵃ_[p])

variable {p}

/-- **UP is stable under powers** (iterated `IsUP.mul`). -/
protected theorem IsUP.pow {x : HahnSeries ℚ (𝔽ᵃ_[p])} (hx : IsUP p x) :
    ∀ n : ℕ, IsUP p (x ^ n)
  | 0 => by simpa using isUP_one p
  | n + 1 => by rw [pow_succ]; exact (hx.pow n).mul hx

/-- **UP is stable under finite sums** (iterated `IsUP.add`). -/
theorem isUP_sum {ι : Type*} {s : Finset ι} {f : ι → HahnSeries ℚ (𝔽ᵃ_[p])}
    (h : ∀ i ∈ s, IsUP p (f i)) : IsUP p (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.cons_induction with
  | empty => simpa using isUP_zero p
  | cons i s his ih =>
    rw [Finset.sum_cons]
    exact (h i (Finset.mem_cons_self ..)).add (ih fun j hj => h j (Finset.mem_cons_of_mem hj))

/-- Polynomial expressions with UP coefficients in a UP series are UP: if the
structure map of an `R`-algebra structure on `𝔽̄_p((t^ℚ))` has UP values and `ξ` is
UP, then `aeval ξ q` is UP for every `q : R[X]`. -/
theorem isUP_aeval {R : Type*} [CommRing R] [Algebra R (HahnSeries ℚ (𝔽ᵃ_[p]))]
    (hbase : ∀ r : R, IsUP p (algebraMap R (HahnSeries ℚ (𝔽ᵃ_[p])) r))
    {ξ : HahnSeries ℚ (𝔽ᵃ_[p])} (hξ : IsUP p ξ) (q : Polynomial R) :
    IsUP p (Polynomial.aeval ξ q) := by
  rw [Polynomial.aeval_eq_sum_range]
  exact isUP_sum fun i _ => by
    rw [Algebra.smul_def]
    exact (hbase _).mul (hξ.pow i)

/-- The image of a Laurent series in the Hahn field is UP: its support consists of
integers, and integer-supported series are UP. -/
theorem isUP_intHahnEmbedding (b : (𝔽ᵃ_[p])⸨X⸩) : IsUP p (intHahnEmbedding p b) := by
  refine isUP_of_support_int_div 1 fun s hs => ?_
  have : s ∈ Set.range ((Int.castAddHom ℚ : ℤ →+ ℚ)) := by
    by_contra hnot
    exact hs (HahnSeries.embDomain_of_notMem_range hnot)
  obtain ⟨k, hk⟩ := this
  exact ⟨k, by rw [← hk]; simp⟩

section ArtinSchreierSplits

/-- The Artin-Schreier polynomial `X^p - X - C y` over `𝔽̄_p((t^ℚ))` has degree `p`. -/
theorem natDegree_artinSchreier (y : HahnSeries ℚ (𝔽ᵃ_[p])) :
    (Polynomial.X ^ p - Polynomial.X - Polynomial.C y :
      Polynomial (HahnSeries ℚ (𝔽ᵃ_[p]))).natDegree = p := by
  rw [sub_sub]
  have h1 : (Polynomial.X + Polynomial.C y :
        Polynomial (HahnSeries ℚ (𝔽ᵃ_[p]))).natDegree
      < (Polynomial.X ^ p : Polynomial (HahnSeries ℚ (𝔽ᵃ_[p]))).natDegree := by
    rw [Polynomial.natDegree_X_add_C, Polynomial.natDegree_X_pow]
    exact hp.out.one_lt
  rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt h1, Polynomial.natDegree_X_pow]

theorem artinSchreier_ne_zero (y : HahnSeries ℚ (𝔽ᵃ_[p])) :
    (Polynomial.X ^ p - Polynomial.X - Polynomial.C y :
      Polynomial (HahnSeries ℚ (𝔽ᵃ_[p]))) ≠ 0 := by
  intro h0
  have := natDegree_artinSchreier y
  rw [h0, Polynomial.natDegree_zero] at this
  exact hp.out.ne_zero this.symm

/-- **The Artin-Schreier polynomial splits over `𝔽̄_p((t^ℚ))` once it has a root**:
the `p` translates `x₀ + c`, `c ∈ 𝔽_p`, of a root `x₀` are distinct roots of
`X^p - X - C y`, and the degree is `p`. -/
theorem artinSchreier_splits {y x₀ : HahnSeries ℚ (𝔽ᵃ_[p])} (h : x₀ ^ p - x₀ = y) :
    (Polynomial.X ^ p - Polynomial.X - Polynomial.C y :
      Polynomial (HahnSeries ℚ (𝔽ᵃ_[p]))).Splits := by
  classical
  set Q : Polynomial (HahnSeries ℚ (𝔽ᵃ_[p])) :=
    Polynomial.X ^ p - Polynomial.X - Polynomial.C y with hQ
  -- the `p` translates of `x₀` by the `𝔽_p`-constants
  set root : ZMod p → HahnSeries ℚ (𝔽ᵃ_[p]) :=
    fun c => x₀ + HahnSeries.C (algebraMap (ZMod p) (𝔽ᵃ_[p]) c) with hroot_def
  have hroot : ∀ c : ZMod p, Q.IsRoot (root c) := by
    intro c
    have hfix : algebraMap (ZMod p) (𝔽ᵃ_[p]) c ^ p = algebraMap (ZMod p) (𝔽ᵃ_[p]) c := by
      rw [← map_pow, ZMod.pow_card]
    simp only [Polynomial.IsRoot, hQ, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_C, hroot_def]
    rw [add_pow_char, ← map_pow (HahnSeries.C : 𝔽ᵃ_[p] →+* HahnSeries ℚ (𝔽ᵃ_[p])), hfix, ← h]
    ring
  have hinj : Function.Injective root := by
    intro c₁ c₂ hcc
    have h1 : HahnSeries.C (algebraMap (ZMod p) (𝔽ᵃ_[p]) c₁)
        = HahnSeries.C (algebraMap (ZMod p) (𝔽ᵃ_[p]) c₂) := add_left_cancel hcc
    exact (algebraMap (ZMod p) (𝔽ᵃ_[p])).injective
      ((HahnSeries.C : 𝔽ᵃ_[p] →+* HahnSeries ℚ (𝔽ᵃ_[p])).injective h1)
  have hQ0 : Q ≠ 0 := artinSchreier_ne_zero y
  -- count roots: at least `p` distinct ones, at most `natDegree = p` in total
  have hcard : p ≤ Q.roots.card := by
    calc p = (Finset.univ.image root).card := by
          rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, ZMod.card]
      _ ≤ Q.roots.toFinset.card := by
          refine Finset.card_le_card fun z hz => ?_
          obtain ⟨c, -, rfl⟩ := Finset.mem_image.mp hz
          exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hQ0).mpr (hroot c))
      _ ≤ Q.roots.card := Q.roots.toFinset_card_le
  have hub : Q.roots.card ≤ p := by
    have h := Q.card_roots'
    rwa [show Q.natDegree = p from natDegree_artinSchreier y] at h
  rw [Polynomial.splits_iff_card_roots, show Q.natDegree = p from natDegree_artinSchreier y]
  omega

end ArtinSchreierSplits

section Tower

variable {L : Type*} [Field L] [Algebra (𝔽ᵃ_[p])⸨X⸩ L] [Module.Finite (𝔽ᵃ_[p])⸨X⸩ L]

/-- **Base of the tower**: `B(u)` with `u^n = t`, `n` prime to `p`, embeds over
`B = 𝔽̄_p((t))` into the Hahn field with UP image — the minimal polynomial of `u`
divides `X^n - t`, which splits over the Hahn field with roots `ζ^i t^{1/n}`. -/
theorem exists_algHom_adjoin_forall_isUP {u : L} {n : ℕ} (hnF : (n : 𝔽ᵃ_[p]) ≠ 0)
    (hu : u ^ n = algebraMap (𝔽ᵃ_[p])⸨X⸩ L (HahnSeries.single 1 1)) :
    ∃ ψ : (𝔽ᵃ_[p])⸨X⸩⟮u⟯ →ₐ[(𝔽ᵃ_[p])⸨X⸩] HahnSeries ℚ (𝔽ᵃ_[p]),
      ∀ z, IsUP p (ψ z) := by
  have hn0 : n ≠ 0 := fun h => hnF (by rw [h, Nat.cast_zero])
  have hnQ : ((n : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr hn0
  -- a primitive `n`-th root of unity of `𝔽̄_p`, pushed into the Hahn field
  have : NeZero ((n : 𝔽ᵃ_[p])) := ⟨hnF⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (𝔽ᵃ_[p]) n
  have hζH : IsPrimitiveRoot (HahnSeries.C ζ : HahnSeries ℚ (𝔽ᵃ_[p])) n :=
    hζ.map_of_injective
      (f := (HahnSeries.C : 𝔽ᵃ_[p] →+* HahnSeries ℚ (𝔽ᵃ_[p]))) (RingHom.injective _)
  -- the distinguished root `t^{1/n}`
  set s : HahnSeries ℚ (𝔽ᵃ_[p]) := HahnSeries.single ((n : ℚ)⁻¹) 1 with hs_def
  have hsn : s ^ n = algebraMap (𝔽ᵃ_[p])⸨X⸩ (HahnSeries ℚ (𝔽ᵃ_[p])) (HahnSeries.single 1 1) := by
    rw [hs_def, HahnSeries.single_pow, one_pow, nsmul_eq_mul, mul_inv_cancel₀ hnQ,
      show algebraMap (𝔽ᵃ_[p])⸨X⸩ (HahnSeries ℚ (𝔽ᵃ_[p])) (HahnSeries.single 1 1)
        = intHahnEmbedding p (HahnSeries.single 1 1) from rfl,
      intHahnEmbedding_single]
    norm_num
  -- the minimal polynomial of `u` divides `X^n - t`
  have huint : IsIntegral ((𝔽ᵃ_[p])⸨X⸩) u := Algebra.IsIntegral.isIntegral u
  have hdvd : minpoly ((𝔽ᵃ_[p])⸨X⸩) u ∣
      (Polynomial.X ^ n - Polynomial.C (HahnSeries.single 1 1)) := by
    refine minpoly.dvd _ _ ?_
    rw [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, hu, sub_self]
  have hmapdvd : (minpoly ((𝔽ᵃ_[p])⸨X⸩) u).map
        (algebraMap ((𝔽ᵃ_[p])⸨X⸩) (HahnSeries ℚ (𝔽ᵃ_[p]))) ∣
      (Polynomial.X ^ n - Polynomial.C
        (algebraMap ((𝔽ᵃ_[p])⸨X⸩) (HahnSeries ℚ (𝔽ᵃ_[p])) (HahnSeries.single 1 1))) := by
    have := Polynomial.map_dvd (algebraMap ((𝔽ᵃ_[p])⸨X⸩) (HahnSeries ℚ (𝔽ᵃ_[p]))) hdvd
    rwa [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C] at this
  -- so its image over the Hahn field splits; pick a root `ξ`
  have hQsplits : (Polynomial.X ^ n - Polynomial.C
      (algebraMap ((𝔽ᵃ_[p])⸨X⸩) (HahnSeries ℚ (𝔽ᵃ_[p])) (HahnSeries.single 1 1))).Splits :=
    X_pow_sub_C_splits_of_isPrimitiveRoot hζH hsn
  have hQ0 : (Polynomial.X ^ n - Polynomial.C
      (algebraMap ((𝔽ᵃ_[p])⸨X⸩) (HahnSeries ℚ (𝔽ᵃ_[p])) (HahnSeries.single 1 1))) ≠ 0 :=
    Polynomial.X_pow_sub_C_ne_zero (Nat.pos_of_ne_zero hn0) _
  have hmm_splits := hQsplits.of_dvd hQ0 hmapdvd
  have hmmdeg : ((minpoly ((𝔽ᵃ_[p])⸨X⸩) u).map
      (algebraMap ((𝔽ᵃ_[p])⸨X⸩) (HahnSeries ℚ (𝔽ᵃ_[p])))).degree ≠ 0 := by
    rw [Polynomial.degree_map]
    exact (minpoly.degree_pos huint).ne'
  set ξ := Polynomial.rootOfSplits hmm_splits hmmdeg with hξ_def
  have hξeval : ((minpoly ((𝔽ᵃ_[p])⸨X⸩) u).map
      (algebraMap ((𝔽ᵃ_[p])⸨X⸩) (HahnSeries ℚ (𝔽ᵃ_[p])))).eval ξ = 0 :=
    Polynomial.eval_rootOfSplits hmm_splits hmmdeg
  -- `ξ` is one of the roots `ζ^i t^{1/n}`, so it is supported on `(1/n)ℤ` and UP
  have hξbig : (Polynomial.X ^ n - Polynomial.C
      (algebraMap ((𝔽ᵃ_[p])⸨X⸩) (HahnSeries ℚ (𝔽ᵃ_[p])) (HahnSeries.single 1 1))).eval ξ = 0 := by
    obtain ⟨R, hR⟩ := hmapdvd
    rw [hR, Polynomial.eval_mul, hξeval, zero_mul]
  have hξUP : IsUP p ξ := by
    rw [X_pow_sub_C_eq_prod hζH (Nat.pos_of_ne_zero hn0) hsn,
      Polynomial.eval_prod, Finset.prod_eq_zero_iff] at hξbig
    obtain ⟨i, -, hzero⟩ := hξbig
    rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero] at hzero
    rw [hzero, ← map_pow, hs_def]
    refine isUP_of_support_int_div ⟨n, Nat.pos_of_ne_zero hn0⟩ fun g hg => ?_
    have : g ∈ (HahnSeries.single ((n : ℚ)⁻¹) (ζ ^ i)).support := by
      rwa [show (HahnSeries.C (ζ ^ i) : HahnSeries ℚ (𝔽ᵃ_[p]))
            * HahnSeries.single ((n : ℚ)⁻¹) 1
          = HahnSeries.single ((n : ℚ)⁻¹) (ζ ^ i) by
        rw [HahnSeries.C_apply, HahnSeries.single_mul_single, zero_add, mul_one]]
        at hg
    have hgm := HahnSeries.support_single_subset this
    refine ⟨1, ?_⟩
    rw [Set.mem_singleton_iff.mp hgm]
    push_cast
    rw [one_div]
    rfl
  -- lift along the power basis of `B(u)`
  have haev : Polynomial.aeval ξ
      (minpoly ((𝔽ᵃ_[p])⸨X⸩) (AdjoinSimple.gen ((𝔽ᵃ_[p])⸨X⸩) u)) = 0 := by
    rw [minpoly_gen, Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
    exact hξeval
  refine ⟨(IntermediateField.adjoin.powerBasis huint).lift ξ (by
    rwa [IntermediateField.adjoin.powerBasis_gen]), fun z => ?_⟩
  obtain ⟨q, -, rfl⟩ := (IntermediateField.adjoin.powerBasis huint).exists_eq_aeval z
  rw [← Polynomial.aeval_algHom_apply, PowerBasis.lift_gen]
  exact isUP_aeval (fun b => isUP_intHahnEmbedding b) hξUP q

/-- **One Artin-Schreier step**: an embedding of `N` into the Hahn field with UP image
extends across `N' = N(θ)`, `θ^p - θ ∈ N` — the Artin-Schreier polynomial over the
image has a UP root and splits, so the image of the minimal polynomial of `θ` has a
root, necessarily UP. -/
theorem exists_algHom_sup_adjoin_forall_isUP {N N' : IntermediateField ((𝔽ᵃ_[p])⸨X⸩) L}
    (τ : N →ₐ[(𝔽ᵃ_[p])⸨X⸩] HahnSeries ℚ (𝔽ᵃ_[p])) (hτ : ∀ z, IsUP p (τ z)) {θ : L}
    (hAS : θ ^ p - θ ∈ N)
    (hsup : N' = N ⊔ IntermediateField.adjoin ((𝔽ᵃ_[p])⸨X⸩) {θ}) :
    ∃ τ' : N' →ₐ[(𝔽ᵃ_[p])⸨X⸩] HahnSeries ℚ (𝔽ᵃ_[p]), ∀ z, IsUP p (τ' z) := by
  let _ : Algebra N (HahnSeries ℚ (𝔽ᵃ_[p])) := τ.toRingHom.toAlgebra
  let _ : IsScalarTower ((𝔽ᵃ_[p])⸨X⸩) N (HahnSeries ℚ (𝔽ᵃ_[p])) :=
    IsScalarTower.of_algebraMap_eq fun b => (τ.commutes b).symm
  set a : N := ⟨θ ^ p - θ, hAS⟩ with ha_def
  have hy : IsUP p (algebraMap N (HahnSeries ℚ (𝔽ᵃ_[p])) a) := hτ a
  -- a UP Artin-Schreier root of `τ(a)` exists, so the AS polynomial splits over Hahn
  obtain ⟨x₀, hx₀, -⟩ := exists_artinSchreier_root_isUP hy
  have hθint : IsIntegral N θ :=
    IsIntegral.tower_top (Algebra.IsIntegral.isIntegral (R := (𝔽ᵃ_[p])⸨X⸩) θ)
  have hdvd : minpoly N θ ∣ (Polynomial.X ^ p - Polynomial.X - Polynomial.C a) := by
    refine minpoly.dvd _ _ ?_
    rw [map_sub, map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C]
    have hcoe : algebraMap N L a = θ ^ p - θ := rfl
    rw [hcoe, sub_self]
  have hmapdvd : (minpoly N θ).map (algebraMap N (HahnSeries ℚ (𝔽ᵃ_[p]))) ∣
      (Polynomial.X ^ p - Polynomial.X
        - Polynomial.C (algebraMap N (HahnSeries ℚ (𝔽ᵃ_[p])) a)) := by
    have := Polynomial.map_dvd (algebraMap N (HahnSeries ℚ (𝔽ᵃ_[p]))) hdvd
    rwa [Polynomial.map_sub, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.map_C] at this
  have hmm_splits := (artinSchreier_splits hx₀).of_dvd
    (artinSchreier_ne_zero _) hmapdvd
  have hmmdeg : ((minpoly N θ).map (algebraMap N (HahnSeries ℚ (𝔽ᵃ_[p])))).degree ≠ 0 := by
    rw [Polynomial.degree_map]
    exact (minpoly.degree_pos hθint).ne'
  set ξ := Polynomial.rootOfSplits hmm_splits hmmdeg with hξ_def
  have hξeval : ((minpoly N θ).map (algebraMap N (HahnSeries ℚ (𝔽ᵃ_[p])))).eval ξ = 0 :=
    Polynomial.eval_rootOfSplits hmm_splits hmmdeg
  -- the root is an Artin-Schreier root of `τ(a)`, hence UP
  have hξAS : ξ ^ p - ξ = algebraMap N (HahnSeries ℚ (𝔽ᵃ_[p])) a := by
    obtain ⟨R, hR⟩ := hmapdvd
    have h0 : (Polynomial.X ^ p - Polynomial.X
        - Polynomial.C (algebraMap N (HahnSeries ℚ (𝔽ᵃ_[p])) a)).eval ξ = 0 := by
      rw [hR, Polynomial.eval_mul, hξeval, zero_mul]
    rw [Polynomial.eval_sub, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_C, sub_eq_zero] at h0
    exact h0
  have hξUP : IsUP p ξ := isUP_of_artinSchreier_root hy hξAS
  -- lift along the power basis of `N(θ)` and restrict scalars back to `B`
  have haev : Polynomial.aeval ξ (minpoly N (AdjoinSimple.gen N θ)) = 0 := by
    rw [minpoly_gen, Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
    exact hξeval
  set ψ : N⟮θ⟯ →ₐ[N] HahnSeries ℚ (𝔽ᵃ_[p]) :=
    (IntermediateField.adjoin.powerBasis hθint).lift ξ (by
      rwa [IntermediateField.adjoin.powerBasis_gen]) with hψ_def
  have hψUP : ∀ z, IsUP p (ψ z) := by
    intro z
    obtain ⟨q, -, rfl⟩ := (IntermediateField.adjoin.powerBasis hθint).exists_eq_aeval z
    rw [hψ_def, ← Polynomial.aeval_algHom_apply, PowerBasis.lift_gen]
    exact isUP_aeval (fun r => hτ r) hξUP q
  have hEq : N' = IntermediateField.restrictScalars ((𝔽ᵃ_[p])⸨X⸩)
      (IntermediateField.adjoin N {θ}) := by
    rw [IntermediateField.restrictScalars_adjoin, hsup, IntermediateField.adjoin_union,
      IntermediateField.adjoin_self]
  exact ⟨(ψ.restrictScalars ((𝔽ᵃ_[p])⸨X⸩)).comp
      (IntermediateField.equivOfEq hEq).toAlgHom,
    fun z => hψUP _⟩

/-- **Embedding the tower with UP image** (Kedlaya (2001a), proof of Theorem 15):
every finite Galois extension `L` of `B = 𝔽̄_p((t))` admits a
`B`-embedding `τ : L → 𝔽̄_p((t^ℚ))` — over the inclusion `intHahnEmbedding` of `B` —
whose image consists of uniformly periodic series.  The Artin-Schreier tower of
`Ext.exists_artinSchreier_tower` is embedded stage by stage. -/
theorem exists_ringHom_forall_isUP [IsGalois ((𝔽ᵃ_[p])⸨X⸩) L] :
    ∃ τ : L →+* HahnSeries ℚ (𝔽ᵃ_[p]),
      (∀ b : (𝔽ᵃ_[p])⸨X⸩, τ (algebraMap ((𝔽ᵃ_[p])⸨X⸩) L b) = intHahnEmbedding p b) ∧
      ∀ x : L, IsUP p (τ x) := by
  obtain ⟨n, u, r, M, hnF, hu, hM0, hMlast, hMstep⟩ := Ext.exists_artinSchreier_tower
    (K := 𝔽ᵃ_[p]) (L := L) p
  -- embed each stage of the chain
  have key : ∀ i : Fin (r + 1), ∃ τ : M i →ₐ[(𝔽ᵃ_[p])⸨X⸩] HahnSeries ℚ (𝔽ᵃ_[p]),
      ∀ z, IsUP p (τ z) := by
    intro i
    induction i using Fin.induction with
    | zero =>
      obtain ⟨ψ, hψ⟩ := exists_algHom_adjoin_forall_isUP (p := p) hnF hu
      exact ⟨ψ.comp (IntermediateField.equivOfEq hM0).toAlgHom, fun z => hψ _⟩
    | succ i IH =>
      obtain ⟨τ, hτ⟩ := IH
      obtain ⟨θ, hAS, hsupθ⟩ := hMstep i
      exact exists_algHom_sup_adjoin_forall_isUP τ hτ hAS hsupθ
  obtain ⟨τtop, hτtop⟩ := key (Fin.last r)
  -- transport along `M (last r) = ⊤ ≃ L`
  set τL : L →ₐ[(𝔽ᵃ_[p])⸨X⸩] HahnSeries ℚ (𝔽ᵃ_[p]) :=
    (τtop.comp (IntermediateField.equivOfEq hMlast.symm).toAlgHom).comp
      IntermediateField.topEquiv.symm.toAlgHom with hτL_def
  exact ⟨τL.toRingHom, fun b => τL.commutes b, fun x => hτtop _⟩

end Tower

end TrustworthyKedlaya.UP
