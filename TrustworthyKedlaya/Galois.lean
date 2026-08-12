/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import TrustworthyKedlaya.Extension
public import Mathlib.Algebra.CharP.Reduced
public import Mathlib.FieldTheory.Fixed
public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.RingTheory.IntegralDomain

/-!
# The residue map and the tame character of a finite extension of `K⸨X⸩`

Let `B = K⸨X⸩` over an algebraically closed field `K`, and let `L/B` be a finite
extension, carrying the spectral norm (`TrustworthyKedlaya.Extension`). This file
constructs the residue map and the tame character of `L/B`:

* `TrustworthyKedlaya.Ext.residue` : the residue map of the closed unit ball of `L`
  onto the residue field `K` — `residue K y` is the unique constant `c : K` with
  `‖y - c‖ < 1` (junk value `0` outside the ball). It is multiplicative on the closed
  unit ball (`residue_mul`), fixes constants (`residue_C`), does not vanish on
  norm-one elements (`residue_ne_zero`), and is invariant under `B`-automorphisms
  (`residue_algEquiv`).
* `TrustworthyKedlaya.Ext.tameCharacter` : for a fixed nonzero `u : L`, the group
  homomorphism `θ : (L ≃ₐ[B] L) →* Kˣ`, `θ g = residue (g u / u)` — "`g u / u` mod
  the maximal ideal". It does not depend on the choice of `u` among elements of equal
  spectral norm (`tameCharacter_eq_of_spectralNorm_eq`); in particular it does not
  depend on the choice of a uniformizer.
* `isCyclic_range_tameCharacter`, `not_dvd_natCard_range_tameCharacter` : the range
  of `θ` is a finite subgroup of `Kˣ`, hence cyclic, and its order is prime to the
  characteristic `p` of `K` (`Kˣ` has no `p`-torsion, by injectivity of Frobenius).

This is Lemma `lem:tame-cyclic` of the blueprint (Kedlaya 2001a, proof of Lemma 3).
-/

@[expose] public section

namespace TrustworthyKedlaya.Ext

open LaurentSeries
open scoped Valued WithZero

variable {K : Type*} [Field K]

section Constants

/-- Nonzero constants have valuation `1` in `K⸨X⸩`. -/
theorem valuation_C {a : K} (ha : a ≠ 0) :
    Valued.v (HahnSeries.C a : K⸨X⸩) = 1 := by
  have hle : ∀ b : K, Valued.v (HahnSeries.C b : K⸨X⸩) ≤ 1 := fun b => by
    have h := (LaurentSeries.valuation_le_iff_coeff_lt_eq_zero K (D := 0)
        (f := (HahnSeries.C b : K⸨X⸩))).mpr
      fun n hn => by rw [HahnSeries.C_apply, HahnSeries.coeff_single_of_ne hn.ne]
    rwa [neg_zero, WithZero.exp_zero] at h
  refine le_antisymm (hle a) ?_
  have hCmul : (HahnSeries.C a : K⸨X⸩) * HahnSeries.C a⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ ha, map_one]
  have hmul : Valued.v (HahnSeries.C a : K⸨X⸩) * Valued.v (HahnSeries.C a⁻¹ : K⸨X⸩) = 1 := by
    rw [← map_mul, hCmul, map_one]
  calc (1 : ℤᵐ⁰) = Valued.v (HahnSeries.C a : K⸨X⸩) * Valued.v (HahnSeries.C a⁻¹ : K⸨X⸩) :=
        hmul.symm
    _ ≤ Valued.v (HahnSeries.C a : K⸨X⸩) * 1 := mul_le_mul_right (hle a⁻¹) _
    _ = Valued.v (HahnSeries.C a : K⸨X⸩) := mul_one _

/-- Nonzero constants have norm `1` in `K⸨X⸩`. -/
theorem norm_C {a : K} (ha : a ≠ 0) : ‖(HahnSeries.C a : K⸨X⸩)‖ = 1 := by
  have h := norm_eq_of_valuation_eq (f := (HahnSeries.C a : K⸨X⸩)) (g := 1)
    (by rw [valuation_C ha, map_one])
  rwa [norm_one] at h

variable {L : Type*} [Field L] [Algebra K⸨X⸩ L] [Module.Finite K⸨X⸩ L]

omit [Module.Finite K⸨X⸩ L] in
/-- Nonzero constants have spectral norm `1` in a finite extension of `K⸨X⸩`. -/
theorem spectralNorm_C {a : K} (ha : a ≠ 0) :
    spectralNorm K⸨X⸩ L (algebraMap K⸨X⸩ L (HahnSeries.C a)) = 1 := by
  rw [spectralNorm_extends, norm_C ha]

omit [Module.Finite K⸨X⸩ L] in
/-- Constants have spectral norm at most `1` in a finite extension of `K⸨X⸩`. -/
theorem spectralNorm_C_le_one (a : K) :
    spectralNorm K⸨X⸩ L (algebraMap K⸨X⸩ L (HahnSeries.C a)) ≤ 1 := by
  rcases eq_or_ne a 0 with rfl | ha
  · rw [map_zero, map_zero, spectralNorm_zero]
    exact zero_le_one
  · rw [spectralNorm_C ha]

end Constants

section ResidueMap

variable {L : Type*} [Field L] [Algebra K⸨X⸩ L] [Module.Finite K⸨X⸩ L]

omit [Module.Finite K⸨X⸩ L] in
/-- `B`-automorphisms of a finite extension `L` of `B = K⸨X⸩` preserve the spectral
norm (they preserve minimal polynomials). -/
theorem spectralNorm_algEquiv (g : L ≃ₐ[K⸨X⸩] L) (x : L) :
    spectralNorm K⸨X⸩ L (g x) = spectralNorm K⸨X⸩ L x := by
  simp only [spectralNorm, minpoly.algEquiv_eq]

/-- The residue constant of an element of the closed unit ball is unique: two constants
within distance `< 1` of the same element coincide. -/
theorem residue_unique {y : L} {c c' : K}
    (hc : spectralNorm K⸨X⸩ L (y - algebraMap K⸨X⸩ L (HahnSeries.C c)) < 1)
    (hc' : spectralNorm K⸨X⸩ L (y - algebraMap K⸨X⸩ L (HahnSeries.C c')) < 1) :
    c = c' := by
  by_contra hne
  let _ : NormedField L := spectralNorm.normedField K⸨X⸩ L
  have hnorm : ∀ y : L, ‖y‖ = spectralNorm K⸨X⸩ L y := fun _ => rfl
  have _ : IsUltrametricDist L :=
    IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm
      (isNonarchimedean_spectralNorm (K := K⸨X⸩) (L := L))
  have hdiff : algebraMap K⸨X⸩ L (HahnSeries.C (c - c')) =
      (y - algebraMap K⸨X⸩ L (HahnSeries.C c')) + -(y - algebraMap K⸨X⸩ L (HahnSeries.C c)) := by
    rw [map_sub, map_sub]
    ring
  have hlt : ‖algebraMap K⸨X⸩ L (HahnSeries.C (c - c'))‖ < 1 := by
    rw [hdiff]
    refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ ?_)
    · rw [hnorm]; exact hc'
    · rw [norm_neg, hnorm]; exact hc
  rw [hnorm, spectralNorm_C (sub_ne_zero.mpr hne)] at hlt
  exact absurd hlt (lt_irrefl 1)

variable [IsAlgClosed K]

variable (K) in
/-- The **residue map** of a finite extension `L` of `B = K⸨X⸩` with `K` algebraically
closed: `residue K y` is the unique constant `c : K` with `‖y - c‖ < 1`, for `y` in the
closed unit ball of the spectral norm (junk value `0` outside it). -/
noncomputable def residue (y : L) : K :=
  if h : spectralNorm K⸨X⸩ L y ≤ 1 then (exists_residue y h).choose else 0

theorem residue_spec {y : L} (hy : spectralNorm K⸨X⸩ L y ≤ 1) :
    spectralNorm K⸨X⸩ L (y - algebraMap K⸨X⸩ L (HahnSeries.C (residue K y))) < 1 := by
  unfold residue
  rw [dif_pos hy]
  exact (exists_residue y hy).choose_spec

/-- Any constant within distance `< 1` of `y` *is* the residue of `y`. -/
theorem residue_eq_of {y : L} {c : K}
    (hc : spectralNorm K⸨X⸩ L (y - algebraMap K⸨X⸩ L (HahnSeries.C c)) < 1) :
    residue K y = c := by
  have hy : spectralNorm K⸨X⸩ L y ≤ 1 := by
    let _ : NormedField L := spectralNorm.normedField K⸨X⸩ L
    have hnorm : ∀ y : L, ‖y‖ = spectralNorm K⸨X⸩ L y := fun _ => rfl
    have _ : IsUltrametricDist L :=
      IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm
        (isNonarchimedean_spectralNorm (K := K⸨X⸩) (L := L))
    have hy' : y = (y - algebraMap K⸨X⸩ L (HahnSeries.C c)) +
        algebraMap K⸨X⸩ L (HahnSeries.C c) := by ring
    rw [← hnorm, hy']
    refine le_trans (IsUltrametricDist.norm_add_le_max _ _) (max_le ?_ ?_)
    · rw [hnorm]; exact hc.le
    · rw [hnorm]; exact spectralNorm_C_le_one c
  exact residue_unique (residue_spec hy) hc

/-- The residue map fixes constants. -/
theorem residue_C (c : K) : residue K (algebraMap K⸨X⸩ L (HahnSeries.C c)) = c :=
  residue_eq_of (by rw [sub_self, spectralNorm_zero]; exact one_pos)

/-- The residue of `1` is `1`. -/
theorem residue_one : residue K (1 : L) = 1 := by
  have h := residue_C (L := L) (1 : K)
  rwa [map_one, map_one] at h

/-- The residue of a norm-one element is nonzero. -/
theorem residue_ne_zero {y : L} (hy : spectralNorm K⸨X⸩ L y = 1) : residue K y ≠ 0 := by
  intro h0
  have h := residue_spec (K := K) (y := y) hy.le
  rw [h0, map_zero, map_zero, sub_zero, hy] at h
  exact absurd h (lt_irrefl 1)

/-- The residue map is multiplicative on the closed unit ball. -/
theorem residue_mul {y z : L} (hy : spectralNorm K⸨X⸩ L y ≤ 1)
    (hz : spectralNorm K⸨X⸩ L z ≤ 1) :
    residue K (y * z) = residue K y * residue K z := by
  refine residue_eq_of ?_
  let _ : NormedField L := spectralNorm.normedField K⸨X⸩ L
  have hnorm : ∀ y : L, ‖y‖ = spectralNorm K⸨X⸩ L y := fun _ => rfl
  have _ : IsUltrametricDist L :=
    IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm
      (isNonarchimedean_spectralNorm (K := K⸨X⸩) (L := L))
  have key : y * z - algebraMap K⸨X⸩ L (HahnSeries.C (residue K y * residue K z)) =
      (y - algebraMap K⸨X⸩ L (HahnSeries.C (residue K y))) * z +
        algebraMap K⸨X⸩ L (HahnSeries.C (residue K y)) *
          (z - algebraMap K⸨X⸩ L (HahnSeries.C (residue K z))) := by
    rw [map_mul, map_mul]
    ring
  rw [← hnorm, key]
  refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ ?_)
  · rw [norm_mul]
    refine lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _) ?_) ?_
    · rw [hnorm]; exact hz
    · rw [hnorm]; exact residue_spec hy
  · rw [norm_mul]
    refine lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) ?_) ?_
    · rw [hnorm]; exact spectralNorm_C_le_one _
    · rw [hnorm]; exact residue_spec hz

/-- The residue map is invariant under `B`-automorphisms: they fix the residue field `K`
pointwise (its elements are constants, coming from `B`). -/
theorem residue_algEquiv (g : L ≃ₐ[K⸨X⸩] L) (y : L) :
    residue K (g y) = residue K y := by
  rcases le_or_gt (spectralNorm K⸨X⸩ L y) 1 with hy | hy
  · refine residue_eq_of ?_
    have h : g y - algebraMap K⸨X⸩ L (HahnSeries.C (residue K y)) =
        g (y - algebraMap K⸨X⸩ L (HahnSeries.C (residue K y))) := by
      rw [map_sub, AlgEquiv.commutes]
    rw [h, spectralNorm_algEquiv]
    exact residue_spec hy
  · unfold residue
    rw [dif_neg (not_le.mpr (by rwa [spectralNorm_algEquiv])), dif_neg (not_le.mpr hy)]

end ResidueMap

section TameCharacter

variable {L : Type*} [Field L] [Algebra K⸨X⸩ L] [Module.Finite K⸨X⸩ L]

/-- `g u / u` has spectral norm one, for any `B`-automorphism `g` and any nonzero `u`. -/
theorem spectralNorm_algEquiv_apply_div (g : L ≃ₐ[K⸨X⸩] L) (u : Lˣ) :
    spectralNorm K⸨X⸩ L (g (u : L) / u) = 1 := by
  let _ : NormedField L := spectralNorm.normedField K⸨X⸩ L
  have hnorm : ∀ y : L, ‖y‖ = spectralNorm K⸨X⸩ L y := fun _ => rfl
  rw [← hnorm, norm_div, hnorm (g (u : L)), spectralNorm_algEquiv, ← hnorm]
  exact div_self (norm_ne_zero_iff.mpr u.ne_zero)

variable [IsAlgClosed K]

variable (K) in
/-- The **tame character** of a finite extension `L/B`, `B = K⸨X⸩` with `K` algebraically
closed: for a fixed nonzero `u : L`, the group homomorphism `θ : (L ≃ₐ[B] L) →* Kˣ`,
`θ g = residue (g u / u)` — "`g u / u` mod the maximal ideal". It does not depend on the
choice of `u` among elements of equal spectral norm
(`tameCharacter_eq_of_spectralNorm_eq`); in particular it does not depend on the choice
of a uniformizer. -/
noncomputable def tameCharacter (u : Lˣ) : (L ≃ₐ[K⸨X⸩] L) →* Kˣ where
  toFun g := Units.mk0 (residue K (g (u : L) / u))
    (residue_ne_zero (spectralNorm_algEquiv_apply_div g u))
  map_one' := by
    refine Units.ext ?_
    rw [Units.val_mk0, Units.val_one, AlgEquiv.one_apply, div_self u.ne_zero, residue_one]
  map_mul' g h := by
    refine Units.ext ?_
    have h1 : spectralNorm K⸨X⸩ L (g ((h (u : L)) / u)) = 1 := by
      rw [spectralNorm_algEquiv]
      exact spectralNorm_algEquiv_apply_div h u
    have h2 : spectralNorm K⸨X⸩ L (g (u : L) / u) = 1 :=
      spectralNorm_algEquiv_apply_div g u
    have hgu : g (u : L) ≠ 0 := fun hc => u.ne_zero (g.injective (hc.trans (map_zero g).symm))
    have key : g (h (u : L)) / (u : L) = g ((h (u : L)) / u) * (g (u : L) / u) := by
      rw [map_div₀]
      field_simp
    rw [Units.val_mul, Units.val_mk0, Units.val_mk0, Units.val_mk0, AlgEquiv.mul_apply, key,
      residue_mul h1.le h2.le, residue_algEquiv]
    exact mul_comm _ _

/-- The tame character does not depend on the choice of `u` among elements of equal
spectral norm; in particular it does not depend on the choice of a uniformizer. -/
theorem tameCharacter_eq_of_spectralNorm_eq {u u' : Lˣ}
    (h : spectralNorm K⸨X⸩ L (u : L) = spectralNorm K⸨X⸩ L (u' : L)) :
    tameCharacter K u = tameCharacter K u' := by
  refine MonoidHom.ext fun g => Units.ext ?_
  change residue K (g (u : L) / u) = residue K (g (u' : L) / u')
  let _ : NormedField L := spectralNorm.normedField K⸨X⸩ L
  have hnorm : ∀ y : L, ‖y‖ = spectralNorm K⸨X⸩ L y := fun _ => rfl
  set w : L := (u' : L) / u with hw
  have hwnorm : spectralNorm K⸨X⸩ L w = 1 := by
    rw [← hnorm, hw, norm_div, hnorm (u' : L), ← h, hnorm (u : L), ← hnorm]
    exact div_self (norm_ne_zero_iff.mpr u.ne_zero)
  have hgu : g (u : L) ≠ 0 := fun hc => u.ne_zero (g.injective (hc.trans (map_zero g).symm))
  have hkey : (g (u' : L) / u') * w = g w * (g (u : L) / u) := by
    rw [hw, map_div₀]
    field_simp
  have h1 : spectralNorm K⸨X⸩ L (g (u' : L) / u') = 1 :=
    spectralNorm_algEquiv_apply_div g u'
  have h2 : spectralNorm K⸨X⸩ L (g w) = 1 := by
    rw [spectralNorm_algEquiv]; exact hwnorm
  have h3 : spectralNorm K⸨X⸩ L (g (u : L) / u) = 1 :=
    spectralNorm_algEquiv_apply_div g u
  have hres : residue K (g (u' : L) / u') * residue K w =
      residue K (g w) * residue K (g (u : L) / u) := by
    rw [← residue_mul h1.le hwnorm.le, ← residue_mul h2.le h3.le, hkey]
  rw [residue_algEquiv] at hres
  rw [mul_comm] at hres
  exact (mul_left_cancel₀ (residue_ne_zero hwnorm) hres).symm

section Range

/-- The range of the tame character is a finite subgroup of `Kˣ` (the automorphism
group of a finite extension is finite). -/
theorem finite_range_tameCharacter (u : Lˣ) : Finite (tameCharacter K u).range :=
  Set.finite_range _ |>.to_subtype

/-- **The image of the tame character is cyclic**: it is a finite subgroup of the
multiplicative group of the field `K`. -/
theorem isCyclic_range_tameCharacter (u : Lˣ) : IsCyclic (tameCharacter K u).range := by
  have := finite_range_tameCharacter (K := K) u
  exact isCyclic_subgroup_units _

/-- **The image of the tame character has order prime to `p`**: `Kˣ` has no `p`-torsion
in characteristic `p`, by injectivity of the Frobenius. -/
theorem not_dvd_natCard_range_tameCharacter (p : ℕ) [Fact p.Prime] [CharP K p] (u : Lˣ) :
    ¬ p ∣ Nat.card (tameCharacter K u).range := by
  intro hdvd
  have := finite_range_tameCharacter (K := K) u
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hdvd
  have hpow : x ^ p = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have hxK : ((x : Kˣ) : K) ^ p = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← SubmonoidClass.coe_pow, hpow, OneMemClass.coe_one,
      Units.val_one]
  have hx1 : ((x : Kˣ) : K) = 1 := frobenius_inj K p (by
    rw [frobenius_def, frobenius_def, one_pow]
    exact hxK)
  have hxone : x = 1 := Subtype.ext (Units.ext (hx1.trans Units.val_one.symm))
  rw [hxone, orderOf_one] at hx
  exact (Fact.out : p.Prime).one_lt.ne hx

end Range

section WildInertia

theorem mem_ker_tameCharacter_iff {u : Lˣ} {g : L ≃ₐ[K⸨X⸩] L} :
    g ∈ (tameCharacter K u).ker ↔ residue K (g (u : L) / u) = 1 := by
  rw [MonoidHom.mem_ker, Units.ext_iff]
  simp only [tameCharacter, MonoidHom.coe_mk, OneHom.coe_mk, Units.val_mk0, Units.val_one]

/-- An automorphism in the kernel of the tame character whose order is prime to `p` is
the identity: averaging the uniformizer `u` over the powers of `σ` produces a
`σ`-fixed element of the same norm, whose powers `1, u', …, u'^{d-1}` span `L` over
`B`; `σ` fixes the span pointwise. -/
theorem eq_one_of_mem_ker_tameCharacter (p : ℕ) [Fact p.Prime] [CharP K p] {u : Lˣ}
    (hu : spectralNorm K⸨X⸩ L (u : L) ^ Module.finrank K⸨X⸩ L =
      ‖(HahnSeries.single 1 1 : K⸨X⸩)‖)
    {σ : L ≃ₐ[K⸨X⸩] L} (hσ : σ ∈ (tameCharacter K u).ker) {m : ℕ} (hm0 : 0 < m)
    (hmp : ¬ p ∣ m) (hσm : σ ^ m = 1) : σ = 1 := by
  let _ : NormedField L := spectralNorm.normedField K⸨X⸩ L
  have hnorm : ∀ y : L, ‖y‖ = spectralNorm K⸨X⸩ L y := fun _ => rfl
  have _ : IsUltrametricDist L :=
    IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm
      (isNonarchimedean_spectralNorm (K := K⸨X⸩) (L := L))
  set d : ℕ := Module.finrank K⸨X⸩ L with hd
  have hd0 : 0 < d := Module.finrank_pos
  -- every power of `σ` lies in the kernel, so each `σ^k(u)/u` has residue `1`
  have hterm : ∀ k : ℕ, ‖(σ ^ k) (u : L) / u - 1‖ < 1 := fun k => by
    have hres : residue K ((σ ^ k) (u : L) / u) = 1 :=
      mem_ker_tameCharacter_iff.mp (pow_mem hσ k)
    have h := residue_spec (K := K)
      (y := (σ ^ k) (u : L) / u) (spectralNorm_algEquiv_apply_div (σ ^ k) u).le
    rw [hres, map_one, map_one] at h
    rw [hnorm]
    exact h
  -- `m` is a unit: it is a nonzero constant
  have hmK : ((m : K)) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff K p]
    exact hmp
  have hmcast : algebraMap K⸨X⸩ L (HahnSeries.C (m : K)) = (m : L) := by
    rw [map_natCast (HahnSeries.C : K →+* K⸨X⸩) m, map_natCast]
  have hmnorm : ‖(m : L)‖ = 1 := by
    rw [hnorm, ← hmcast, spectralNorm_C hmK]
  have hmL : ((m : L)) ≠ 0 := by
    intro hc
    rw [hc, norm_zero] at hmnorm
    exact zero_ne_one hmnorm
  -- the average of `u` over the powers of `σ`
  set u' : L := (m : L)⁻¹ * ∑ k ∈ Finset.range m, (σ ^ k) (u : L) with hu'def
  have hσu' : σ u' = u' := by
    rw [hu'def, map_mul, map_inv₀, map_natCast, map_sum]
    congr 1
    calc ∑ k ∈ Finset.range m, σ ((σ ^ k) (u : L))
        = ∑ k ∈ Finset.range m, (σ ^ (k + 1)) (u : L) :=
          Finset.sum_congr rfl fun k _ => by rw [pow_succ', AlgEquiv.mul_apply]
      _ = ∑ k ∈ Finset.range m, (σ ^ k) (u : L) := by
          have hshift := (Finset.sum_range_succ' (fun k => (σ ^ k) (u : L)) m).symm.trans
            (Finset.sum_range_succ (fun k => (σ ^ k) (u : L)) m)
          rw [hσm, pow_zero] at hshift
          exact add_right_cancel hshift
  -- `u'/u` is within distance `< 1` of `1`, so `u'` is a uniformizer too
  have hufrac : u' / u - 1 =
      (m : L)⁻¹ * ∑ k ∈ Finset.range m, ((σ ^ k) (u : L) / u - 1) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one,
      hu'def]
    field_simp
    rw [mul_sub, Finset.mul_sum]
    congr 1
    · exact Finset.sum_congr rfl fun k _ => by
        rw [← mul_div_assoc, mul_div_cancel_left₀ _ (Units.ne_zero u)]
    · exact mul_comm _ _
  have hsum_lt : ‖u' / u - 1‖ < 1 := by
    rw [hufrac, norm_mul, norm_inv, hmnorm, inv_one, one_mul]
    obtain ⟨i, _, hi_le⟩ := IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty
      (Finset.nonempty_range_iff.mpr hm0.ne') (fun k => (σ ^ k) (u : L) / u - 1)
    exact lt_of_le_of_lt hi_le (hterm i)
  have hu'u : ‖u' / u‖ = 1 := by
    have hle : ‖u' / u‖ ≤ 1 := by
      have hsplit : u' / u = (u' / u - 1) + 1 := by ring
      rw [hsplit]
      exact le_trans (IsUltrametricDist.norm_add_le_max _ _)
        (max_le hsum_lt.le norm_one.le)
    have hone : (1 : L) = u' / u + -(u' / u - 1) := by ring
    have hmax := IsUltrametricDist.norm_add_le_max (u' / u) (-(u' / u - 1))
    rw [← hone, norm_one, norm_neg] at hmax
    have hge : 1 ≤ ‖u' / u‖ := by
      by_contra hlt
      push Not at hlt
      exact absurd hmax (not_le.mpr (max_lt hlt hsum_lt))
    exact le_antisymm hle hge
  have hu'0 : u' ≠ 0 := by
    intro hc
    rw [hc, zero_div, norm_zero] at hu'u
    exact zero_ne_one hu'u
  have hu'normu : ‖u'‖ = ‖(u : L)‖ := by
    rw [norm_div] at hu'u
    exact (div_eq_one_iff_eq (norm_ne_zero_iff.mpr u.ne_zero)).mp hu'u
  -- `u'` has the two uniformizer properties, via the chosen uniformizer `π`
  obtain ⟨π, hπd, hπall⟩ := exists_spectralNorm_uniformizer_pow_finrank (K := K) (L := L)
  have huπ : ‖(u : L)‖ = spectralNorm K⸨X⸩ L π := by
    refine (pow_left_strictMonoOn₀ (M₀ := ℝ) (n := d) hd0.ne').injOn
      (norm_nonneg _) (spectralNorm_nonneg _) ?_
    rw [hnorm, hu, hπd]
  have hu'e : spectralNorm K⸨X⸩ L u' ^ d = ‖(HahnSeries.single 1 1 : K⸨X⸩)‖ := by
    rw [← hnorm, hu'normu, hnorm, hu]
  have hu'all : ∀ x : L, x ≠ 0 →
      ∃ j : ℤ, spectralNorm K⸨X⸩ L x = spectralNorm K⸨X⸩ L u' ^ j := by
    intro x hx
    obtain ⟨j, hj⟩ := hπall x hx
    refine ⟨j, ?_⟩
    rw [hj, ← hnorm u', hu'normu, huπ]
  -- the powers of `u'` span `L`, and `σ` fixes them all
  have hspan := span_pow_eq_top_of_spectralNorm_pow_eq (K := K) (L := L) hd0 hu'e hu'all
  refine AlgEquiv.ext fun x => ?_
  rw [AlgEquiv.one_apply]
  have hx : x ∈ Submodule.span K⸨X⸩ (Set.range fun i : Fin d => u' ^ (i : ℕ)) := by
    rw [hspan]
    exact Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy => obtain ⟨i, rfl⟩ := hy; rw [map_pow, hσu']
  | zero => rw [map_zero]
  | add a b _ _ ha hb => rw [map_add, ha, hb]
  | smul c a _ ha => rw [map_smul, ha]

/-- **The wild subgroup is a `p`-group**: the kernel of the tame character of `L/B` at a
uniformizer `u` consists of automorphisms of `p`-power order. -/
theorem isPGroup_ker_tameCharacter (p : ℕ) [Fact p.Prime] [CharP K p] {u : Lˣ}
    (hu : spectralNorm K⸨X⸩ L (u : L) ^ Module.finrank K⸨X⸩ L =
      ‖(HahnSeries.single 1 1 : K⸨X⸩)‖) :
    IsPGroup p (tameCharacter K u).ker := by
  rw [IsPGroup.iff_card]
  have hcard0 : Nat.card (tameCharacter K u).ker ≠ 0 := Nat.card_pos.ne'
  refine ⟨(Nat.card (tameCharacter K u).ker).primeFactorsList.length,
    Nat.eq_prime_pow_of_unique_prime_dvd hcard0 fun {q} hq hqdvd => ?_⟩
  by_contra hqp
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := (tameCharacter K u).ker) q hqdvd
  have hσ : (g : L ≃ₐ[K⸨X⸩] L) ∈ (tameCharacter K u).ker := SetLike.coe_mem g
  have hσq : (g : L ≃ₐ[K⸨X⸩] L) ^ q = 1 := by
    have hgq : g ^ q = 1 := by rw [← hg]; exact pow_orderOf_eq_one g
    rw [← SubgroupClass.coe_pow, hgq]
    rfl
  have hpq : ¬ p ∣ q := fun hdvd =>
    hqp ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) hq).mp hdvd).symm
  have h1 : (g : L ≃ₐ[K⸨X⸩] L) = 1 :=
    eq_one_of_mem_ker_tameCharacter p hu hσ hq.pos hpq hσq
  have hg1 : g = 1 := Subtype.ext h1
  rw [hg1, orderOf_one] at hg
  exact hq.one_lt.ne hg

/-- The quotient of the Galois group by the wild subgroup is cyclic: it is isomorphic to
the image of the tame character. -/
theorem isCyclic_quotient_ker_tameCharacter (u : Lˣ) :
    IsCyclic ((L ≃ₐ[K⸨X⸩] L) ⧸ (tameCharacter K u).ker) := by
  rw [(QuotientGroup.quotientKerEquivRange (tameCharacter K u)).isCyclic]
  exact isCyclic_range_tameCharacter u

/-- The quotient of the Galois group by the wild subgroup has order prime to `p`. -/
theorem not_dvd_natCard_quotient_ker_tameCharacter (p : ℕ) [Fact p.Prime] [CharP K p]
    (u : Lˣ) : ¬ p ∣ Nat.card ((L ≃ₐ[K⸨X⸩] L) ⧸ (tameCharacter K u).ker) := by
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange (tameCharacter K u)).toEquiv]
  exact not_dvd_natCard_range_tameCharacter p u

end WildInertia

end TameCharacter

end TrustworthyKedlaya.Ext
