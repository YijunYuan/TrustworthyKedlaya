/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import TrustworthyKedlaya.Lp.Miscellaneous
public import Mathlib.Analysis.Normed.Field.WithAbs
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.RingTheory.AdicCompletion.Topology
public import Mathlib.RingTheory.DedekindDomain.AdicValuation
public import Mathlib.RingTheory.Valuation.Discrete.Basic
public import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
public import Mathlib.RingTheory.Valuation.Discrete.RankOne
public import Mathlib.RingTheory.WittVector.Compare
public import Mathlib.RingTheory.WittVector.Complete
public import Mathlib.RingTheory.WittVector.DiscreteValuationRing
public import Mathlib.RingTheory.WittVector.Teichmuller
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import Mathlib.Topology.Algebra.Valued.WithVal

/-!
# Completed maximal unramified extension of ℚ_[p]

This file contains our implementation of the completed maximal unramified extension of `ℚ_[p]`,
denoted `ℚᶜᵘⁿ_[p]`. Since the ramification theory in mathlib is not yet developed, we use the Witt
vector construction:

- the algebraic closure of `𝔽ₚ` is `𝔽ᵃ_[p]`;
- `ℤᶜᵘⁿ_[p]` is the ring of Witt vectors over `𝔽ᵃ_[p]`, i.e. the ring of integers of the maximal
  unramified extension of `ℚ_[p]`;
- `ℚᶜᵘⁿ_[p]` is the fraction field of `ℤᶜᵘⁿ_[p]`, equipped with the topology induced by the
  valuation corresponding to the unique maximal ideal of `ℤᶜᵘⁿ_[p]`.

## Main definitions

- `TrustworthyKedlaya.Fpbar` (`𝔽ᵃ_[p]`): the algebraic closure of `𝔽ₚ`.
- `TrustworthyKedlaya.OQpCUn` (`ℤᶜᵘⁿ_[p]`): the Witt vectors over `𝔽ᵃ_[p]`.
- `TrustworthyKedlaya.QpCUn` (`ℚᶜᵘⁿ_[p]`): the fraction field of `ℤᶜᵘⁿ_[p]` with its
  valuation topology.
- `TrustworthyKedlaya.QpCUn.Qp_embd`: the valuation-preserving embedding `ℚ_[p] → ℚᶜᵘⁿ_[p]`.

## Main statements

- `TrustworthyKedlaya.injective_teichmuller`: the Teichmüller lift `𝔽ᵃ_[p] → ℤᶜᵘⁿ_[p]`
  is injective.
- `TrustworthyKedlaya.QpCUn.Qp_embd_keep_val`, `TrustworthyKedlaya.QpCUn.norm_Qp_embd`: the
  embedding `ℚ_[p] → ℚᶜᵘⁿ_[p]` preserves the valuation, hence is isometric.
- The valuation on `ℚᶜᵘⁿ_[p]` is rank-one discrete, making `ℚᶜᵘⁿ_[p]` a complete nontrivially normed
  field, with `‖a‖ = p ^ (log (Valued.v a))` (`TrustworthyKedlaya.QpCUn.norm_eq_zpow_log_valued`).
  These are standard facts of algebraic number theory, so the proofs are only lightly commented.

## Notation

- `𝔽ᵃ_[p]`, `ℤᶜᵘⁿ_[p]`, `ℚᶜᵘⁿ_[p]` for the three objects above.

## Tags

p-adic, Witt vector, unramified extension, valuation
-/

@[expose] public section

namespace TrustworthyKedlaya

open WittVector

/-- The algebraic closure `𝔽ᵃ_[p]` of the finite field `𝔽ₚ`. -/
abbrev Fpbar (p : ℕ) [Fact (Nat.Prime p)] := AlgebraicClosure (ZMod p)
@[inherit_doc] notation "𝔽ᵃ_[" p "]" => Fpbar p

/-- The ring of integers `ℤᶜᵘⁿ_[p]` of the completed maximal unramified extension of `ℚ_[p]`,
realized as the Witt vectors `W(𝔽ᵃ_[p])`. -/
abbrev OQpCUn (p : ℕ) [Fact (Nat.Prime p)] := WittVector p (Fpbar p)
@[inherit_doc] notation "ℤᶜᵘⁿ_[" p "]" => OQpCUn p

/-- The completed maximal unramified extension `ℚᶜᵘⁿ_[p]` of `ℚ_[p]`, defined as the fraction field
of `ℤᶜᵘⁿ_[p]` equipped with the topology induced by the valuation of its maximal ideal. -/
abbrev QpCUn (p : ℕ) [Fact (Nat.Prime p)] :=
  WithVal ((IsDiscreteValuationRing.maximalIdeal (ℤᶜᵘⁿ_[p])).valuation ((FractionRing (ℤᶜᵘⁿ_[p]))))
@[inherit_doc] notation "ℚᶜᵘⁿ_[" p "]" => QpCUn p

/-- The Teichmüller lift `𝔽ᵃ_[p] → ℤᶜᵘⁿ_[p]` is injective. -/
theorem injective_teichmuller (p : ℕ) [Fact (Nat.Prime p)] :
    Function.Injective (teichmuller p : 𝔽ᵃ_[p] → ℤᶜᵘⁿ_[p]) := by
  intro a b hab
  simp only [teichmuller, MonoidHom.coe_mk, OneHom.coe_mk, teichmullerFun, mk'.injEq] at hab
  apply_fun (fun x => x 0) at hab
  simpa

namespace QpCUn

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsDiscreteValuationRing

noncomputable instance (p : ℕ) [Fact (Nat.Prime p)] :
  Valued (ℚᶜᵘⁿ_[p]) (WithZero (Multiplicative ℤ)) := inferInstance

/-- The valuation `Valued.v` of the image of `r : ℤᶜᵘⁿ_[p]` in `ℚᶜᵘⁿ_[p]` equals the `intValuation`
of `r`. Since `WithVal` is a structure in this mathlib version, `Valued.v` is the `comap` of the
base valuation along `WithVal.equiv`; this lemma packages that bridge once for all proofs below. -/
theorem valued_algebraMap (p : ℕ) [Fact (Nat.Prime p)] (r : ℤᶜᵘⁿ_[p]) :
    Valued.v (algebraMap (ℤᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p]) r) =
      (IsDiscreteValuationRing.maximalIdeal (ℤᶜᵘⁿ_[p])).intValuation r := by
  rw [WithVal.algebraMap_right_apply, WithVal.valued_toVal,
    (IsDiscreteValuationRing.maximalIdeal (ℤᶜᵘⁿ_[p])).valuation_of_algebraMap]

-- The valuation on `ℚᶜᵘⁿ_[p]` is rank-one discrete (transferred from the adic valuation on
-- `FractionRing ℤᶜᵘⁿ_[p]` via the value-group equality for `WithVal`).
noncomputable instance (p : ℕ) [Fact (Nat.Prime p)] :
    (Valued.v : Valuation ℚᶜᵘⁿ_[p] (WithZero (Multiplicative ℤ))).IsRankOneDiscrete where
  exists_generator_lt_one' := by
    have h : ((IsDiscreteValuationRing.maximalIdeal (ℤᶜᵘⁿ_[p])).valuation
        (FractionRing (ℤᶜᵘⁿ_[p]))).IsRankOneDiscrete := inferInstance
    obtain ⟨γ, hγ, hγ1⟩ := h.exists_generator_lt_one'
    exact ⟨γ, by rw [WithVal.valueGroup_eq]; exact hγ, hγ1⟩

-- The valuation on `ℚᶜᵘⁿ_[p]` has rank one, with associated absolute value `p ^ (-v)`.
noncomputable instance (p : ℕ) [Fact (Nat.Prime p)] : Valuation.RankOne
    (Valued.v : Valuation ℚᶜᵘⁿ_[p] (WithZero (Multiplicative ℤ))) :=
  Valuation.IsRankOneDiscrete.rankOne
    (v := (Valued.v : Valuation ℚᶜᵘⁿ_[p] (WithZero (Multiplicative ℤ))))
    (by exact_mod_cast (Fact.out : Nat.Prime p).one_lt : (1 : NNReal) < (p : NNReal))

-- The normed field structure on `ℚᶜᵘⁿ_[p]` induced by the rank-one valuation.
noncomputable instance (p : ℕ) [Fact (Nat.Prime p)] : NormedField ℚᶜᵘⁿ_[p] :=
  Valued.toNormedField (ℚᶜᵘⁿ_[p]) (WithZero (Multiplicative ℤ))

-- ℚᶜᵘⁿ_[p] is complete with respect to the valuation topology.
instance (p : ℕ) [Fact (Nat.Prime p)] : CompleteSpace (ℚᶜᵘⁿ_[p]) := by
  -- Strategy: reduce `CompleteSpace ℚᶜᵘⁿ_[p]` to `IsComplete (Valued.v.integer)`, then
  -- use that this integer subring is isomorphic to the IsAdicComplete `ℤᶜᵘⁿ_[p]`.

  -- Step 1: use `Valued.toNormedField` so that the NormedField's UniformSpace coincides
  -- with the Valued one (avoids the clash with the file-level `WithAbs.normedField (abs p)`).
  let nfd : NormedField (ℚᶜᵘⁿ_[p]) :=
    Valued.toNormedField (ℚᶜᵘⁿ_[p]) (WithZero (Multiplicative ℤ))
  -- Step 2: by `NormedField.completeSpace_iff_isComplete_closedBall`, it suffices to show the
  -- unit closed ball is complete.
  refine NormedField.completeSpace_iff_isComplete_closedBall.mpr ?_
  -- Step 3: the unit closed ball is exactly the valuation-integer subring (as a set).
  rw [← Valued.toNormedField.setOfPred_mem_integer_eq_closedBall]
  -- Step 4: show that `{x | x ∈ Valued.v.integer}` is complete.
  -- Equip `ℤᶜᵘⁿ_[p]` with the `(Ideal.span {p})`-adic topology/uniformity via `WithIdeal`.
  let _ : WithIdeal (ℤᶜᵘⁿ_[p]) := ⟨Ideal.span {(p : ℤᶜᵘⁿ_[p])}⟩
  have hadic : IsAdic (WithIdeal.i (R := ℤᶜᵘⁿ_[p])) := rfl
  -- `WittVector.isAdicCompleteIdealSpanP` + `IsAdic.isAdicComplete_iff` gives `CompleteSpace`.
  have : CompleteSpace (ℤᶜᵘⁿ_[p]) :=
    (hadic.isAdicComplete_iff.mp WittVector.isAdicCompleteIdealSpanP).1
  -- Show `algebraMap ℤᶜᵘⁿ_[p] ℚᶜᵘⁿ_[p]` is uniform inducing: pulling back the valuation
  -- uniformity from `ℚᶜᵘⁿ_[p]` recovers the `(Ideal.span {p})`-adic uniformity on `ℤᶜᵘⁿ_[p]`.
  have hUI : IsUniformInducing (algebraMap (ℤᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p])) := by
    have hsrc : (uniformity (ℤᶜᵘⁿ_[p])).HasBasis (fun _ : ℕ => True)
        (fun n => {x : ℤᶜᵘⁿ_[p] × ℤᶜᵘⁿ_[p] | x.2 - x.1 ∈ (Ideal.span {(p : ℤᶜᵘⁿ_[p])}) ^ n}) :=
      Filter.HasBasis.uniformity_of_nhds_zero hadic.hasBasis_nhds_zero
    -- In v4.31 the valued uniformity basis is indexed by the value group `ValueGroup₀`,
    -- with the restricted valuation `Valued.v.restrict`.
    have htgt := Valued.hasBasis_uniformity (ℚᶜᵘⁿ_[p]) (WithZero (Multiplicative ℤ))
    rw [hsrc.isUniformInducing_iff htgt]
    set v := (IsDiscreteValuationRing.maximalIdeal (ℤᶜᵘⁿ_[p]))
    have hmax : v.asIdeal = Ideal.span {(p : ℤᶜᵘⁿ_[p])} :=
      (WittVector.irreducible p).maximalIdeal_eq
    refine ⟨?_, ?_⟩
    · -- For any target basis γ, find a source basis n s.t. `r ∈ I^n → v(algebraMap r) < γ`.
      intro γ _
      set g : WithZero (Multiplicative ℤ) := MonoidWithZeroHom.ValueGroup₀.embedding γ.1 with hg
      have hg0 : g ≠ 0 := MonoidWithZeroHom.ValueGroup₀.embedding_unit_ne_zero γ
      refine ⟨(1 - g.log).toNat, trivial, ?_⟩
      intro x y h
      simp only [Set.mem_ofPred_eq] at h ⊢
      rw [Valuation.restrict_lt_iff_lt_embedding, ← map_sub, ← hg, valued_algebraMap]
      rw [← hmax] at h
      have h1 : v.intValuation (y - x) ≤ WithZero.exp (-((1 - g.log).toNat : ℤ)) :=
        (IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem v (y - x) _).mpr h
      refine lt_of_le_of_lt h1 ?_
      rw [(WithZero.lt_log_iff_exp_lt hg0).symm]
      by_cases hpos : 1 - g.log ≥ 0
      · rw [Int.toNat_of_nonneg hpos]; omega
      · rw [Int.toNat_of_nonpos (le_of_lt (by omega))]; push_cast; omega
    · -- For any source basis n, find a target basis γ s.t. `v(algebraMap r) < γ → r ∈ I^n`.
      -- Take `γ` to be the value-group class of `algebraMap (p^n)`, whose valuation is `exp(-n)`.
      intro n _
      set a : ℚᶜᵘⁿ_[p] := algebraMap (ℤᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p]) ((p : ℤᶜᵘⁿ_[p]) ^ n) with ha
      have hva : Valued.v a = WithZero.exp (-(n : ℤ)) := by
        rw [ha, valued_algebraMap, map_pow,
          v.intValuation_singleton (WittVector.p_nonzero p _) hmax, ← WithZero.exp_nsmul]
        congr 1
        simp
      have hane : Valued.v.restrict a ≠ 0 := by
        rw [ne_eq, Valuation.restrict_eq_zero_iff, hva]; exact WithZero.exp_ne_zero
      refine ⟨Units.mk0 (Valued.v.restrict a) hane, trivial, ?_⟩
      intro x y h
      simp only [Set.mem_ofPred_eq] at h ⊢
      rw [← hmax, ← IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem v (y - x) n]
      rw [Valuation.restrict_lt_iff_lt_embedding, ← map_sub, valued_algebraMap, Units.val_mk0,
        Valuation.embedding_restrict, hva] at h
      exact le_of_lt h
  -- Transport completeness: the image of a complete space under a uniform inducing map is complete.
  have hRange : IsComplete (Set.range (algebraMap (ℤᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p]))) := hUI.isComplete_range
  -- Identify the image with `Valued.v.integer`
  -- (both equal `{x | v(x) ≤ 1}` since `ℤᶜᵘⁿ_[p]` is a DVR).
  have hSet : Set.range (algebraMap (ℤᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p])) =
      {x : ℚᶜᵘⁿ_[p] | x ∈ Valued.v.integer} := by
    ext x
    refine ⟨?_, ?_⟩
    · rintro ⟨r, rfl⟩
      change Valued.v (algebraMap (ℤᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p]) r) ≤ 1
      rw [valued_algebraMap]
      exact (IsDiscreteValuationRing.maximalIdeal (ℤᶜᵘⁿ_[p])).intValuation_le_one r
    · intro hx
      obtain ⟨r, hr⟩ := IsDiscreteValuationRing.exists_lift_of_le_one
        (A := ℤᶜᵘⁿ_[p]) (K := FractionRing (ℤᶜᵘⁿ_[p]))
        (x := WithVal.equiv _ x) (by rw [WithVal.val_apply_equiv]; exact hx)
      refine ⟨r, ?_⟩
      rw [WithVal.algebraMap_right_apply, hr]
      rfl
  rw [hSet] at hRange
  exact hRange

-- The embedding from ℚ_[p] to ℚᶜᵘⁿ_[p].
/-- The canonical ring embedding `ℚ_[p] → ℚᶜᵘⁿ_[p]`, induced by the Teichmüller-style map
`ℤ_[p] → ℤᶜᵘⁿ_[p]` on rings of integers and extended to fraction fields. -/
noncomputable def Qp_embd {p : ℕ} [Fact (Nat.Prime p)] : ℚ_[p] →+* ℚᶜᵘⁿ_[p] :=
  @IsFractionRing.map ℤ_[p] ℤᶜᵘⁿ_[p] ℚ_[p] ℚᶜᵘⁿ_[p] _ _ _ _ _ _ _ _ _
    ((WittVector.map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p)))).comp
      (WittVector.fromPadicInt p)) (by
  simp only [RingHom.coe_comp]
  refine Function.Injective.comp ?_ ?_
  · exact WittVector.map_injective _ (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))).injective
  · refine Function.injective_iff_hasLeftInverse.mpr ?_
    use (WittVector.toPadicInt p)
    rw [Function.leftInverse_iff_comp]; ext r
    have := toPadicInt_comp_fromPadicInt_ext p r
    simpa
  )

-- The embedding from ℚ_[p] to ℚᶜᵘⁿ_[p] keeps the valuation.
/-- The embedding `Qp_embd : ℚ_[p] → ℚᶜᵘⁿ_[p]` preserves the valuation: the multiplicative `p`-adic
valuation of `x` agrees with the valuation of its image. -/
lemma Qp_embd_keep_val (p : ℕ) [Fact (Nat.Prime p)] :
    ∀ x : ℚ_[p], Padic.mulValuation x = Valued.v (Qp_embd x) := by
  intro x
  by_cases hx : x = 0
  · simp [hx, Qp_embd, map_zero]
  · rw [Padic.mulValuation_toFun, if_neg hx]
    have hp_ne : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : Nat.Prime p).ne_zero
    have hp_norm : ‖(p : ℚ_[p])‖ = (p : ℝ)^(-(1 : ℤ)) := by
      rw [show ((p : ℚ_[p])) = ((p : ℚ_[p]))^(1 : ℕ) by simp]
      rw [Padic.norm_p_pow]; push_cast; rfl
    set y := x * (p : ℚ_[p])^(-x.valuation) with hy_def
    have hy_norm : ‖y‖ = 1 := by
      rw [hy_def, norm_mul, norm_zpow, Padic.norm_eq_zpow_neg_valuation hx, hp_norm]
      rw [← zpow_mul]
      rw [show (-(1 : ℤ)) * (-x.valuation) = x.valuation from by ring]
      rw [← zpow_add₀ (by exact_mod_cast (Fact.out : Nat.Prime p).pos.ne' : (p : ℝ) ≠ 0)]
      simp
    obtain ⟨u, hu_eq⟩ : ∃ u : ℤ_[p]ˣ, x = (u : ℚ_[p]) * (p : ℚ_[p])^x.valuation := by
      refine ⟨PadicInt.mkUnits hy_norm, ?_⟩
      have h1 : (PadicInt.mkUnits hy_norm : ℚ_[p]) = y := by
        rw [PadicInt.val_mkUnits]
      rw [h1, hy_def, mul_assoc, ← zpow_add₀ hp_ne]; simp
    set vx := x.valuation with hvx
    change ((Multiplicative.ofAdd (-vx : ℤ) : Multiplicative ℤ) :
        WithZero (Multiplicative ℤ)) = _
    rw [hu_eq, map_mul, map_zpow₀, Valuation.map_mul, map_zpow₀]
    have hQp : Qp_embd ((p : ℚ_[p])) = ((p : ℕ) : ℚᶜᵘⁿ_[p]) := by simp [Qp_embd]
    rw [hQp]
    have hp_val : Valued.v ((p : ℚᶜᵘⁿ_[p])) =
        ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) :
          WithZero (Multiplicative ℤ)) := by
      rw [show ((p : ℚᶜᵘⁿ_[p])) = algebraMap (ℤᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p]) (p : ℤᶜᵘⁿ_[p]) from by
        push_cast; rfl]
      rw [valued_algebraMap]
      have hirr : Irreducible (p : ℤᶜᵘⁿ_[p]) := WittVector.irreducible p
      have hpe : (IsDiscreteValuationRing.maximalIdeal (ℤᶜᵘⁿ_[p])).asIdeal =
          Ideal.span {(p : ℤᶜᵘⁿ_[p])} := hirr.maximalIdeal_eq
      rw [IsDedekindDomain.HeightOneSpectrum.intValuation_singleton _
        (WittVector.p_nonzero p _) hpe]
      rfl
    rw [hp_val]
    have hu_val : Valued.v (Qp_embd ((u : ℤ_[p]) : ℚ_[p])) = 1 := by
      have hQpu : Qp_embd ((u : ℤ_[p]) : ℚ_[p]) =
          (algebraMap (ℤᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p]))
            (((WittVector.map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p)))).comp
              (WittVector.fromPadicInt p)) (u : ℤ_[p])) := by
        change (Qp_embd : ℚ_[p] →+* ℚᶜᵘⁿ_[p]) ((algebraMap ℤ_[p] ℚ_[p]) (u : ℤ_[p])) = _
        change (IsFractionRing.map _ : ℚ_[p] →+* ℚᶜᵘⁿ_[p])
          ((algebraMap ℤ_[p] ℚ_[p]) (u : ℤ_[p])) = _
        rw [IsFractionRing.map]
        rw [IsLocalization.map_eq]
      rw [hQpu]
      rw [valued_algebraMap]
      refine (IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff).mpr ?_
      intro hmem
      have hu_unit : IsUnit
          (((WittVector.map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p)))).comp
            (WittVector.fromPadicInt p)) (u : ℤ_[p])) :=
        ((WittVector.map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p)))).comp
          (WittVector.fromPadicInt p)).isUnit_map u.isUnit
      rw [show (IsDiscreteValuationRing.maximalIdeal (ℤᶜᵘⁿ_[p])).asIdeal =
          IsLocalRing.maximalIdeal (ℤᶜᵘⁿ_[p]) from rfl] at hmem
      exact (IsLocalRing.notMem_maximalIdeal.mpr hu_unit) hmem
    rw [hu_val, one_mul]
    rw [← WithZero.coe_zpow]
    congr 1
    rw [← ofAdd_zsmul vx (-1 : ℤ)]
    congr 1; ring

noncomputable instance (p : ℕ) [Fact (Nat.Prime p)] : NontriviallyNormedField ℚᶜᵘⁿ_[p] :=
  Valued.toNontriviallyNormedField (ℚᶜᵘⁿ_[p]) (WithZero (Multiplicative ℤ))

-- View ℚᶜᵘⁿ_[p] as an algebra over ℚ_[p] via the embedding defined above.
noncomputable instance (p : ℕ) [Fact (Nat.Prime p)] : Algebra ℚ_[p] (ℚᶜᵘⁿ_[p]) :=
  (Qp_embd).toAlgebra

theorem algebraMap_Qp_apply {p : ℕ} [Fact (Nat.Prime p)] (x : ℚ_[p]) :
    algebraMap ℚ_[p] ℚᶜᵘⁿ_[p] x = Qp_embd x :=
  rfl

/-! ### The norm on `ℚᶜᵘⁿ_[p]` -/

/-- The norm on `ℚᶜᵘⁿ_[p]` agrees with `WithZeroMulInt.toNNReal` applied to its valuation. In
v4.31 the `Valued.toNormedField` norm is `RankOne.hom (Valued.v.restrict ·)` rather than being
defeq to `toNNReal (Valued.v ·)`, so this requires the rank-one `hom` bridge plus surjectivity of
`Valued.v` (it used to hold by `rfl`). -/
lemma norm_eq_toNNReal_valued {p : ℕ} [Fact (Nat.Prime p)] (a : ℚᶜᵘⁿ_[p]) :
    ‖a‖ = ((WithZeroMulInt.toNNReal (p_ne_zero p) (Valued.v a) : NNReal) : ℝ) := by
  have hsurj : Function.Surjective (Valued.v : ℚᶜᵘⁿ_[p] → WithZero (Multiplicative ℤ)) := by
    intro x
    obtain ⟨y, hy⟩ := (IsDiscreteValuationRing.maximalIdeal (ℤᶜᵘⁿ_[p])).valuation_surjective
      (FractionRing (ℤᶜᵘⁿ_[p])) x
    exact ⟨WithVal.toVal _ y, by rw [WithVal.valued_toVal]; exact hy⟩
  rw [Valued.toNormedField.norm_def]
  norm_cast
  rw [show (Valuation.RankOne.hom (Valued.v : Valuation ℚᶜᵘⁿ_[p] _)) (Valued.v.restrict a)
        = WithZeroMulInt.toNNReal (p_ne_zero p)
            ((Valuation.IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt
              (v := (Valued.v : Valuation ℚᶜᵘⁿ_[p] _))) (Valued.v.restrict a)) from rfl,
     Valuation.IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt_restrict_apply_of_surjective
       hsurj a]

/-- The norm of a nonzero `a : ℚᶜᵘⁿ_[p]` is `p ^ (log (Valued.v a))`. -/
lemma norm_eq_zpow_log_valued {p : ℕ} [Fact (Nat.Prime p)] {a : ℚᶜᵘⁿ_[p]} (ha : a ≠ 0) :
    ‖a‖ = (p : ℝ) ^ (WithZero.log (Valued.v a)) := by
  rw [norm_eq_toNNReal_valued, WithZeroMulInt.toNNReal_neg_apply _ ((Valued.v).ne_zero_iff.mpr ha),
    WithZero.toAdd_unzero_eq_log, NNReal.coe_zpow, NNReal.coe_natCast]

/-- **The embedding `ℚ_[p] → ℚᶜᵘⁿ_[p]` is isometric.** -/
theorem norm_Qp_embd {p : ℕ} [Fact (Nat.Prime p)] (x : ℚ_[p]) : ‖Qp_embd x‖ = ‖x‖ := by
  by_cases hx : x = 0
  · rw [hx, map_zero, norm_zero, norm_zero]
  · rw [norm_eq_zpow_log_valued ((map_ne_zero_iff _ Qp_embd.injective).mpr hx), ← Qp_embd_keep_val,
      Padic.mulValuation_toFun, if_neg hx, WithZero.log_exp, Padic.norm_eq_zpow_neg_valuation hx]

theorem norm_algebraMap_Qp {p : ℕ} [Fact (Nat.Prime p)] (x : ℚ_[p]) :
    ‖algebraMap ℚ_[p] ℚᶜᵘⁿ_[p] x‖ = ‖x‖ :=
  norm_Qp_embd x

end QpCUn

end TrustworthyKedlaya
