/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.FieldTheory.KummerExtension
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
public import TrustworthyKedlaya.Extension
public import TrustworthyKedlaya.LaurentRoots

/-!
# Tame cyclic extensions of `K⸨X⸩` are `X^{1/m}`-extensions

Let `B = K⸨X⸩` with `K` algebraically closed and let `L/B` be a finite Galois extension,
cyclic of degree `m` with `m` invertible in `K`.  This file proves
`TrustworthyKedlaya.Ext.exists_pow_finrank_eq_X_adjoin_eq_top_of_isCyclic`:
`L = B(u)` for an element `u` with `u ^ m = X`.

The proof: `K ⊆ B` contains a primitive `m`-th root of unity, so Kummer theory
(`exists_root_adjoin_eq_top_of_isCyclic`) gives `L = B(α)` with `x := α ^ m ∈ B`.  The
`m`-th power decomposition of Laurent series (`exists_single_order_mul_pow`) normalizes
`α` to a generator `β` with `β ^ m = X ^ v`, `v = ord x`.  Then `gcd(v, m) = 1`: for a
common divisor `d > 1`, the element `β ^ (m/d) / X ^ (v/d)` is a `d`-th root of unity,
hence lies in the image of `K` — forcing `[B(β) : B] ≤ m/d < m`.  Bézout then yields
`u = β ^ a * X ^ b` with `u ^ m = X`, and the value-group argument
(`exists_spectralNorm_uniformizer_pow_finrank`: finite extensions of `B` are totally
ramified) forces `m ∣ [B(u) : B]`, hence `B(u) = L`.

This is Lemma `lem:tame-kummer` of the blueprint (Kedlaya 2001a, proof of Lemma 3).
-/

@[expose] public section

namespace TrustworthyKedlaya.Ext

open LaurentSeries Polynomial IntermediateField
open scoped Valued

variable {K : Type*} [Field K]

/-- Integer powers of `X` in `K⸨X⸩` are the single-term series `X ^ v = single v 1`. -/
theorem single_one_one_zpow (v : ℤ) :
    (HahnSeries.single 1 1 : K⸨X⸩) ^ v = HahnSeries.single v 1 := by
  have hnat : ∀ n : ℕ, (HahnSeries.single 1 1 : K⸨X⸩) ^ (n : ℤ) = HahnSeries.single (n : ℤ) 1 := by
    intro n
    rw [zpow_natCast, HahnSeries.single_pow, one_pow, nsmul_eq_mul, mul_one]
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg v
  · exact hnat n
  · rw [zpow_neg, hnat n]
    refine inv_eq_of_mul_eq_one_right ?_
    rw [HahnSeries.single_mul_single, add_neg_cancel, one_mul, HahnSeries.single_zero_one]

variable [IsAlgClosed K]
variable {L : Type*} [Field L] [Algebra K⸨X⸩ L] [Module.Finite K⸨X⸩ L]

/-- **Ramification forces divisibility of the degree**: if an element `u` of a finite
extension `L` of `K⸨X⸩` satisfies `u ^ n = X`, then `n` divides `[L : K⸨X⸩]`.  Indeed
`L/K⸨X⸩` is totally ramified, so the spectral norm of `u` is an integer power of that of
a uniformizer `π` with `‖π‖ ^ [L : K⸨X⸩] = ‖X‖`; comparing exponents in
`‖u‖ ^ n = ‖X‖ = ‖π‖ ^ [L : K⸨X⸩]` gives the divisibility. -/
theorem dvd_finrank_of_pow_eq_X {u : L} {n : ℕ} (hn : 0 < n)
    (hu : u ^ n = algebraMap K⸨X⸩ L (HahnSeries.single 1 1)) :
    n ∣ Module.finrank K⸨X⸩ L := by
  obtain ⟨π, hπd, hall⟩ := exists_spectralNorm_uniformizer_pow_finrank (K := K) (L := L)
  let _ : NormedField L := spectralNorm.normedField K⸨X⸩ L
  have hnorm : ∀ y : L, ‖y‖ = spectralNorm K⸨X⸩ L y := fun _ => rfl
  rw [← hnorm] at hπd
  set d := Module.finrank K⸨X⸩ L with hd
  set q : ℝ := ‖(HahnSeries.single 1 1 : K⸨X⸩)‖ with hq
  have hq0 : 0 < q := norm_X_pos
  have hq1 : q < 1 := norm_X_lt_one
  have hd0 : 0 < d := Module.finrank_pos
  -- `0 < ‖π‖` and `‖π‖ ≠ 1`
  have hπ0 : 0 < ‖π‖ := by
    rcases (norm_nonneg π).lt_or_eq with h | h
    · exact h
    · exact absurd (hπd.symm.trans (by rw [← h, zero_pow hd0.ne'])) hq0.ne'
  have hπ1 : ‖π‖ ≠ 1 := by
    intro h
    rw [h, one_pow] at hπd
    exact absurd hπd.symm hq1.ne
  -- `u ≠ 0`
  have hX0 : (HahnSeries.single (1 : ℤ) (1 : K) : K⸨X⸩) ≠ 0 :=
    HahnSeries.single_ne_zero one_ne_zero
  have hu0 : u ≠ 0 := by
    rintro rfl
    rw [zero_pow hn.ne'] at hu
    exact hX0 ((map_eq_zero _).mp hu.symm)
  -- compare exponents in `‖u‖ ^ n = q = ‖π‖ ^ d`
  obtain ⟨j, hj⟩ := hall u hu0
  rw [← hnorm, ← hnorm] at hj
  have hun : (‖π‖ ^ j) ^ (n : ℤ) = ‖π‖ ^ (d : ℤ) := by
    rw [← hj, zpow_natCast, ← norm_pow, hu, hnorm, spectralNorm_extends, ← hq, ← hπd,
      zpow_natCast]
  have hjn : j * (n : ℤ) = (d : ℤ) := by
    rw [← zpow_mul] at hun
    exact zpow_right_injective₀ hπ0 hπ1 hun
  have hdvd : (n : ℤ) ∣ (d : ℤ) := ⟨j, by rw [← hjn]; ring⟩
  exact_mod_cast hdvd

/-- **Tame cyclic extensions of `K⸨X⸩` are `X^{1/m}`-extensions** (Kedlaya 2001a, proof of
Lemma 3): if `K` is algebraically closed and `L/K⸨X⸩` is a finite Galois extension, cyclic
of degree `m := [L : K⸨X⸩]` invertible in `K`, then `L = K⸨X⸩(u)` for an element `u` with
`u ^ m = X`. -/
theorem exists_pow_finrank_eq_X_adjoin_eq_top_of_isCyclic
    [IsGalois K⸨X⸩ L] [IsCyclic (L ≃ₐ[K⸨X⸩] L)]
    (hm : ((Module.finrank K⸨X⸩ L : K)) ≠ 0) :
    ∃ u : L, u ^ Module.finrank K⸨X⸩ L = algebraMap K⸨X⸩ L (HahnSeries.single 1 1) ∧
      IntermediateField.adjoin K⸨X⸩ {u} = ⊤ := by
  have hX0 : (HahnSeries.single (1 : ℤ) (1 : K) : K⸨X⸩) ≠ 0 :=
    HahnSeries.single_ne_zero one_ne_zero
  -- a generalized abbreviation `m` for the degree (kept abstract so rewrites stay syntactic)
  obtain ⟨m, hmdef⟩ : ∃ m, Module.finrank K⸨X⸩ L = m := ⟨_, rfl⟩
  rw [hmdef] at hm ⊢
  have hm0 : 0 < m := hmdef ▸ Module.finrank_pos
  -- the trivial extension: `u = X` works
  rcases eq_or_ne m 1 with hm1 | hm1
  · refine ⟨algebraMap K⸨X⸩ L (HahnSeries.single 1 1), by rw [hm1, pow_one], ?_⟩
    have hbt : (⊥ : IntermediateField K⸨X⸩ L) = ⊤ :=
      IntermediateField.bot_eq_top_iff_finrank_eq_one.mpr (hmdef.trans hm1)
    exact eq_top_iff.mpr (hbt ▸ bot_le)
  -- a primitive `m`-th root of unity in `K`, pushed into `K⸨X⸩`
  have : NeZero (m : K) := ⟨hm⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K m
  have hζB : IsPrimitiveRoot (HahnSeries.C ζ : K⸨X⸩) m :=
    hζ.map_of_injective (f := (HahnSeries.C : K →+* K⸨X⸩)) (RingHom.injective _)
  have hK : (primitiveRoots (Module.finrank K⸨X⸩ L) K⸨X⸩).Nonempty := by
    rw [hmdef]
    exact ⟨HahnSeries.C ζ, (mem_primitiveRoots hm0).mpr hζB⟩
  -- Kummer theory: `L = B(α)` with `x := α ^ m ∈ B`
  obtain ⟨α, ⟨x, hx⟩, hα⟩ := exists_root_adjoin_eq_top_of_isCyclic K⸨X⸩ L hK
  rw [hmdef] at hx
  have hα0 : α ≠ 0 := by
    rintro rfl
    rw [IntermediateField.adjoin_zero] at hα
    exact hm1 (hmdef.symm.trans (IntermediateField.bot_eq_top_iff_finrank_eq_one.mp hα))
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [map_zero] at hx
    exact hα0 (pow_eq_zero_iff hm0.ne' |>.mp hx.symm)
  -- normalize the Kummer generator: `β ^ m = X ^ v` with `v = ord x`
  obtain ⟨y, hy0, hxy⟩ := exists_single_order_mul_pow (K := K) m hm hx0
  set v := x.order with hv
  set yL := algebraMap K⸨X⸩ L y with hyL
  have hyL0 : yL ≠ 0 := fun h => hy0 ((map_eq_zero _).mp h)
  set β := α / yL with hβ
  have hβ0 : β ≠ 0 := div_ne_zero hα0 hyL0
  have hβm : β ^ m = algebraMap K⸨X⸩ L (HahnSeries.single v 1) := by
    rw [hβ, div_pow, ← hx, hxy, map_mul, map_pow, ← hyL,
      mul_div_cancel_right₀ _ (pow_ne_zero m hyL0)]
  have hβtop : IntermediateField.adjoin K⸨X⸩ {β} = ⊤ := by
    rw [eq_top_iff, ← hα]
    refine IntermediateField.adjoin_simple_le_iff.mpr ?_
    have hαβ : α = β * yL := by rw [hβ, div_mul_cancel₀ _ hyL0]
    rw [hαβ, hyL]
    exact mul_mem (IntermediateField.mem_adjoin_simple_self _ β)
      (IntermediateField.algebraMap_mem _ y)
  -- the exponent `v` is coprime to `m`
  have hgcd : Int.gcd v (m : ℤ) = 1 := by
    by_contra hd1
    set d := Int.gcd v (m : ℤ) with hddef
    have hdm : d ∣ m := Int.natCast_dvd_natCast.mp (Int.gcd_dvd_right v (m : ℤ))
    have hdv : (d : ℤ) ∣ v := Int.gcd_dvd_left v (m : ℤ)
    have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdm hm0
    obtain ⟨m', hm'⟩ := hdm
    obtain ⟨v', hv'⟩ := hdv
    have hm'0 : 0 < m' := by
      rcases Nat.eq_zero_or_pos m' with rfl | h
      · rw [Nat.mul_zero] at hm'
        omega
      · exact h
    have hm'm : m' < m := by
      have hd2 : 2 ≤ d := by omega
      calc m' < 2 * m' := by omega
        _ ≤ d * m' := Nat.mul_le_mul_right _ hd2
        _ = m := hm'.symm
    -- `β ^ m'` over `X ^ v'` is a `d`-th root of unity, hence in the image of `K`
    have hXv'0 : (HahnSeries.single v' 1 : K⸨X⸩) ≠ 0 := HahnSeries.single_ne_zero one_ne_zero
    have hXv'L0 : algebraMap K⸨X⸩ L (HahnSeries.single v' 1) ≠ 0 :=
      fun h => hXv'0 ((map_eq_zero _).mp h)
    have hζd_pow : (β ^ m' / algebraMap K⸨X⸩ L (HahnSeries.single v' 1)) ^ d = 1 := by
      have hnum : (β ^ m') ^ d = (algebraMap K⸨X⸩ L (HahnSeries.single v' 1)) ^ d := by
        rw [← pow_mul, mul_comm m' d, ← hm', hβm, ← map_pow, HahnSeries.single_pow, one_pow,
          nsmul_eq_mul, ← hv']
      rw [div_pow, hnum, div_self (pow_ne_zero d hXv'L0)]
    have : NeZero d := ⟨hd0.ne'⟩
    have hζdprim : IsPrimitiveRoot (algebraMap K⸨X⸩ L (HahnSeries.C (ζ ^ m'))) d := by
      have hstep : IsPrimitiveRoot (ζ ^ m') d :=
        hζ.pow hm0 (by rw [hm']; exact Nat.mul_comm d m')
      exact (hstep.map_of_injective (f := (HahnSeries.C : K →+* K⸨X⸩))
        (RingHom.injective _)).map_of_injective (f := algebraMap K⸨X⸩ L)
        (RingHom.injective _)
    obtain ⟨i, -, hi⟩ := hζdprim.eq_pow_of_pow_eq_one hζd_pow
    -- so `β ^ m'` lies in the image of `K⸨X⸩`, contradicting `[B(β) : B] = m > m'`
    have hβm' : β ^ m' =
        algebraMap K⸨X⸩ L (HahnSeries.C (ζ ^ m') ^ i * HahnSeries.single v' 1) := by
      rw [map_mul, map_pow (algebraMap K⸨X⸩ L) (HahnSeries.C (ζ ^ m') : K⸨X⸩) i, hi,
        div_mul_cancel₀ _ hXv'L0]
    have hβint : IsIntegral K⸨X⸩ β := Algebra.IsIntegral.isIntegral β
    have hdeg : (minpoly K⸨X⸩ β).natDegree = m := by
      have h1 := IntermediateField.adjoin.finrank hβint
      rw [hβtop, IntermediateField.finrank_top', hmdef] at h1
      exact h1.symm
    have hroot : Polynomial.aeval β ((Polynomial.X ^ m' -
        Polynomial.C (HahnSeries.C (ζ ^ m') ^ i * HahnSeries.single v' 1) :
          Polynomial K⸨X⸩)) = 0 := by
      rw [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, hβm', sub_self]
    have hle := Polynomial.natDegree_le_of_dvd (minpoly.dvd K⸨X⸩ β hroot)
      (Polynomial.X_pow_sub_C_ne_zero hm'0 _)
    rw [hdeg, Polynomial.natDegree_X_pow_sub_C] at hle
    omega
  -- Bézout: `u = β ^ A * X ^ B` satisfies `u ^ m = X`
  obtain ⟨A, B, hbez⟩ : ∃ A B : ℤ, v * A + (m : ℤ) * B = 1 := by
    refine ⟨Int.gcdA v (m : ℤ), Int.gcdB v (m : ℤ), ?_⟩
    have h := Int.gcd_eq_gcd_ab v (m : ℤ)
    rw [hgcd] at h
    exact_mod_cast h.symm
  set tL := algebraMap K⸨X⸩ L (HahnSeries.single 1 1) with htL
  have htL0 : tL ≠ 0 := fun h => hX0 ((map_eq_zero _).mp h)
  have hβz : β ^ ((m : ℕ) : ℤ) = tL ^ v := by
    rw [zpow_natCast, hβm, ← single_one_one_zpow, map_zpow₀, ← htL]
  have hum : (β ^ A * tL ^ B) ^ m = tL := by
    rw [← zpow_natCast (β ^ A * tL ^ B) m, mul_zpow, ← zpow_mul, ← zpow_mul,
      mul_comm A, mul_comm B, zpow_mul, zpow_mul, hβz, ← zpow_mul, ← zpow_mul,
      ← zpow_add₀ htL0, hbez, zpow_one]
  refine ⟨β ^ A * tL ^ B, hum, ?_⟩
  -- the value-group argument: `m ∣ [B(u) : B] ∣ m` forces `B(u) = L`
  set E := IntermediateField.adjoin K⸨X⸩ {β ^ A * tL ^ B} with hE
  have huE : β ^ A * tL ^ B ∈ E := IntermediateField.mem_adjoin_simple_self _ _
  have huEm : (⟨β ^ A * tL ^ B, huE⟩ : E) ^ m = algebraMap K⸨X⸩ E (HahnSeries.single 1 1) := by
    apply Subtype.ext
    change (β ^ A * tL ^ B) ^ m = _
    rw [hum, htL]
    rfl
  have hmdvd : m ∣ Module.finrank K⸨X⸩ E := dvd_finrank_of_pow_eq_X hm0 huEm
  have hEdvd : Module.finrank K⸨X⸩ E ∣ m := by
    rw [← hmdef]
    exact ⟨Module.finrank E L, (Module.finrank_mul_finrank K⸨X⸩ E L).symm⟩
  have hEm : Module.finrank K⸨X⸩ E = m := Nat.dvd_antisymm hEdvd hmdvd
  have h1 : Module.finrank E L = 1 := by
    have h2 := Module.finrank_mul_finrank K⸨X⸩ E L
    rw [hEm, hmdef] at h2
    exact Nat.eq_of_mul_eq_mul_left hm0 (by rw [Nat.mul_one]; exact h2)
  exact IntermediateField.finrank_eq_one_iff_eq_top.mp h1

end TrustworthyKedlaya.Ext
