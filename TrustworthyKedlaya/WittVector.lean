/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import TrustworthyKedlaya.Miscellaneous
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
denoted `ℚᵘⁿ_[p]`. Since the ramification theory in mathlib is not yet developed, we use the Witt
vector construction:

- the algebraic closure of `𝔽ₚ` is `𝔽ᵃ_[p]`;
- `ℤᵘⁿ_[p]` is the ring of Witt vectors over `𝔽ᵃ_[p]`, i.e. the ring of integers of the maximal
  unramified extension of `ℚ_[p]`;
- `ℚᵘⁿ_[p]` is the fraction field of `ℤᵘⁿ_[p]`, equipped with the topology induced by the valuation
  corresponding to the unique maximal ideal of `ℤᵘⁿ_[p]`.

## Main definitions

- `TrustworthyKedlaya.Fpbar` (`𝔽ᵃ_[p]`): the algebraic closure of `𝔽ₚ`.
- `TrustworthyKedlaya.OQpUn` (`ℤᵘⁿ_[p]`): the Witt vectors over `𝔽ᵃ_[p]`.
- `TrustworthyKedlaya.QpUn` (`ℚᵘⁿ_[p]`): the fraction field of `ℤᵘⁿ_[p]` with its
  valuation topology.
- `TrustworthyKedlaya.QpUn.Qp_embd`: the valuation-preserving embedding `ℚ_[p] → ℚᵘⁿ_[p]`.

## Main statements

- `TrustworthyKedlaya.injective_teichmuller`: the Teichmüller lift `𝔽ᵃ_[p] → ℤᵘⁿ_[p]`
  is injective.
- `TrustworthyKedlaya.QpUn.Qp_embd_keep_val`: the embedding `ℚ_[p] → ℚᵘⁿ_[p]`
  preserves the valuation.
- The valuation on `ℚᵘⁿ_[p]` is rank-one discrete, making `ℚᵘⁿ_[p]` a complete nontrivially normed
  field. These are standard facts of algebraic number theory, so the proofs are only lightly
  commented.

## Notation

- `𝔽ᵃ_[p]`, `ℤᵘⁿ_[p]`, `ℚᵘⁿ_[p]` for the three objects above.

## Tags

p-adic, Witt vector, unramified extension, valuation
-/

@[expose] public section

namespace TrustworthyKedlaya

open WittVector

/-- The algebraic closure `𝔽ᵃ_[p]` of the finite field `𝔽ₚ`. -/
abbrev Fpbar (p : ℕ) [Fact (Nat.Prime p)] := AlgebraicClosure (ZMod p)
@[inherit_doc] notation "𝔽ᵃ_[" p "]" => Fpbar p

/-- The ring of integers `ℤᵘⁿ_[p]` of the completed maximal unramified extension of `ℚ_[p]`,
realized as the Witt vectors `W(𝔽ᵃ_[p])`. -/
abbrev OQpUn (p : ℕ) [Fact (Nat.Prime p)] := WittVector p (Fpbar p)
@[inherit_doc] notation "ℤᵘⁿ_[" p "]" => OQpUn p

/-- The completed maximal unramified extension `ℚᵘⁿ_[p]` of `ℚ_[p]`, defined as the fraction field
of `ℤᵘⁿ_[p]` equipped with the topology induced by the valuation of its maximal ideal. -/
abbrev QpUn (p : ℕ) [Fact (Nat.Prime p)] :=
  WithVal ((IsDiscreteValuationRing.maximalIdeal (ℤᵘⁿ_[p])).valuation ((FractionRing (ℤᵘⁿ_[p]))))
@[inherit_doc] notation "ℚᵘⁿ_[" p "]" => QpUn p

/-- The Teichmüller lift `𝔽ᵃ_[p] → ℤᵘⁿ_[p]` is injective. -/
theorem injective_teichmuller (p : ℕ) [Fact (Nat.Prime p)] :
    Function.Injective (teichmuller p : 𝔽ᵃ_[p] → ℤᵘⁿ_[p]) := by
  intro a b hab
  simp only [teichmuller, MonoidHom.coe_mk, OneHom.coe_mk, teichmullerFun, mk'.injEq] at hab
  apply_fun (fun x => x 0) at hab
  simpa

namespace QpUn

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsDiscreteValuationRing

noncomputable instance (p : ℕ) [Fact (Nat.Prime p)] :
  Valued (ℚᵘⁿ_[p]) (WithZero (Multiplicative ℤ)) := inferInstance

/-- The valuation `Valued.v` of the image of `r : ℤᵘⁿ_[p]` in `ℚᵘⁿ_[p]` equals the `intValuation`
of `r`. Since `WithVal` is a structure in this mathlib version, `Valued.v` is the `comap` of the
base valuation along `WithVal.equiv`; this lemma packages that bridge once for all proofs below. -/
theorem valued_algebraMap (p : ℕ) [Fact (Nat.Prime p)] (r : ℤᵘⁿ_[p]) :
    Valued.v (algebraMap (ℤᵘⁿ_[p]) (ℚᵘⁿ_[p]) r) =
      (IsDiscreteValuationRing.maximalIdeal (ℤᵘⁿ_[p])).intValuation r := by
  rw [WithVal.algebraMap_right_apply, WithVal.valued_toVal,
    (IsDiscreteValuationRing.maximalIdeal (ℤᵘⁿ_[p])).valuation_of_algebraMap]

-- The valuation on `ℚᵘⁿ_[p]` is rank-one discrete (transferred from the adic valuation on
-- `FractionRing ℤᵘⁿ_[p]` via the value-group equality for `WithVal`).
noncomputable instance (p : ℕ) [Fact (Nat.Prime p)] :
    (Valued.v : Valuation ℚᵘⁿ_[p] (WithZero (Multiplicative ℤ))).IsRankOneDiscrete where
  exists_generator_lt_one' := by
    have h : ((IsDiscreteValuationRing.maximalIdeal (ℤᵘⁿ_[p])).valuation
        (FractionRing (ℤᵘⁿ_[p]))).IsRankOneDiscrete := inferInstance
    obtain ⟨γ, hγ, hγ1⟩ := h.exists_generator_lt_one'
    exact ⟨γ, by rw [WithVal.valueGroup_eq]; exact hγ, hγ1⟩

-- The valuation on `ℚᵘⁿ_[p]` has rank one, with associated absolute value `p ^ (-v)`.
noncomputable instance (p : ℕ) [Fact (Nat.Prime p)] : Valuation.RankOne
    (Valued.v : Valuation ℚᵘⁿ_[p] (WithZero (Multiplicative ℤ))) :=
  Valuation.IsRankOneDiscrete.rankOne
    (v := (Valued.v : Valuation ℚᵘⁿ_[p] (WithZero (Multiplicative ℤ))))
    (by exact_mod_cast (Fact.out : Nat.Prime p).one_lt : (1 : NNReal) < (p : NNReal))

-- The normed field structure on `ℚᵘⁿ_[p]` induced by the rank-one valuation.
noncomputable instance (p : ℕ) [Fact (Nat.Prime p)] : NormedField ℚᵘⁿ_[p] :=
  Valued.toNormedField (ℚᵘⁿ_[p]) (WithZero (Multiplicative ℤ))

-- ℚᵘⁿ_[p] is complete with respect to the valuation topology.
instance (p : ℕ) [Fact (Nat.Prime p)] : CompleteSpace (ℚᵘⁿ_[p]) := by
  -- Strategy: reduce `CompleteSpace ℚᵘⁿ_[p]` to `IsComplete (Valued.v.integer)`, then
  -- use that this integer subring is isomorphic to the IsAdicComplete `ℤᵘⁿ_[p]`.

  -- Step 1: use `Valued.toNormedField` so that the NormedField's UniformSpace coincides
  -- with the Valued one (avoids the clash with the file-level `WithAbs.normedField (abs p)`).
  let nfd : NormedField (ℚᵘⁿ_[p]) :=
    Valued.toNormedField (ℚᵘⁿ_[p]) (WithZero (Multiplicative ℤ))
  -- Step 2: by `NormedField.completeSpace_iff_isComplete_closedBall`, it suffices to show the
  -- unit closed ball is complete.
  refine NormedField.completeSpace_iff_isComplete_closedBall.mpr ?_
  -- Step 3: the unit closed ball is exactly the valuation-integer subring (as a set).
  rw [← Valued.toNormedField.setOfPred_mem_integer_eq_closedBall]
  -- Step 4: show that `{x | x ∈ Valued.v.integer}` is complete.
  -- Equip `ℤᵘⁿ_[p]` with the `(Ideal.span {p})`-adic topology/uniformity via `WithIdeal`.
  let _ : WithIdeal (ℤᵘⁿ_[p]) := ⟨Ideal.span {(p : ℤᵘⁿ_[p])}⟩
  have hadic : IsAdic (WithIdeal.i (R := ℤᵘⁿ_[p])) := rfl
  -- `WittVector.isAdicCompleteIdealSpanP` + `IsAdic.isAdicComplete_iff` gives `CompleteSpace`.
  have : CompleteSpace (ℤᵘⁿ_[p]) :=
    (hadic.isAdicComplete_iff.mp WittVector.isAdicCompleteIdealSpanP).1
  -- Show `algebraMap ℤᵘⁿ_[p] ℚᵘⁿ_[p]` is uniform inducing: pulling back the valuation
  -- uniformity from `ℚᵘⁿ_[p]` recovers the `(Ideal.span {p})`-adic uniformity on `ℤᵘⁿ_[p]`.
  have hUI : IsUniformInducing (algebraMap (ℤᵘⁿ_[p]) (ℚᵘⁿ_[p])) := by
    have hsrc : (uniformity (ℤᵘⁿ_[p])).HasBasis (fun _ : ℕ => True)
        (fun n => {x : ℤᵘⁿ_[p] × ℤᵘⁿ_[p] | x.2 - x.1 ∈ (Ideal.span {(p : ℤᵘⁿ_[p])}) ^ n}) :=
      Filter.HasBasis.uniformity_of_nhds_zero hadic.hasBasis_nhds_zero
    -- In v4.31 the valued uniformity basis is indexed by the value group `ValueGroup₀`,
    -- with the restricted valuation `Valued.v.restrict`.
    have htgt := Valued.hasBasis_uniformity (ℚᵘⁿ_[p]) (WithZero (Multiplicative ℤ))
    rw [hsrc.isUniformInducing_iff htgt]
    set v := (IsDiscreteValuationRing.maximalIdeal (ℤᵘⁿ_[p]))
    have hmax : v.asIdeal = Ideal.span {(p : ℤᵘⁿ_[p])} :=
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
      set a : ℚᵘⁿ_[p] := algebraMap (ℤᵘⁿ_[p]) (ℚᵘⁿ_[p]) ((p : ℤᵘⁿ_[p]) ^ n) with ha
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
  have hRange : IsComplete (Set.range (algebraMap (ℤᵘⁿ_[p]) (ℚᵘⁿ_[p]))) := hUI.isComplete_range
  -- Identify the image with `Valued.v.integer`
  -- (both equal `{x | v(x) ≤ 1}` since `ℤᵘⁿ_[p]` is a DVR).
  have hSet : Set.range (algebraMap (ℤᵘⁿ_[p]) (ℚᵘⁿ_[p])) =
      {x : ℚᵘⁿ_[p] | x ∈ Valued.v.integer} := by
    ext x
    refine ⟨?_, ?_⟩
    · rintro ⟨r, rfl⟩
      change Valued.v (algebraMap (ℤᵘⁿ_[p]) (ℚᵘⁿ_[p]) r) ≤ 1
      rw [valued_algebraMap]
      exact (IsDiscreteValuationRing.maximalIdeal (ℤᵘⁿ_[p])).intValuation_le_one r
    · intro hx
      obtain ⟨r, hr⟩ := IsDiscreteValuationRing.exists_lift_of_le_one
        (A := ℤᵘⁿ_[p]) (K := FractionRing (ℤᵘⁿ_[p]))
        (x := WithVal.equiv _ x) (by rw [WithVal.val_apply_equiv]; exact hx)
      refine ⟨r, ?_⟩
      rw [WithVal.algebraMap_right_apply, hr]
      rfl
  rw [hSet] at hRange
  exact hRange

-- The embedding from ℚ_[p] to ℚᵘⁿ_[p].
/-- The canonical ring embedding `ℚ_[p] → ℚᵘⁿ_[p]`, induced by the Teichmüller-style map
`ℤ_[p] → ℤᵘⁿ_[p]` on rings of integers and extended to fraction fields. -/
noncomputable def Qp_embd {p : ℕ} [Fact (Nat.Prime p)] : ℚ_[p] →+* ℚᵘⁿ_[p] :=
  @IsFractionRing.map ℤ_[p] ℤᵘⁿ_[p] ℚ_[p] ℚᵘⁿ_[p] _ _ _ _ _ _ _ _ _
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

-- The embedding from ℚ_[p] to ℚᵘⁿ_[p] keeps the valuation.
/-- The embedding `Qp_embd : ℚ_[p] → ℚᵘⁿ_[p]` preserves the valuation: the multiplicative `p`-adic
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
    have hQp : Qp_embd ((p : ℚ_[p])) = ((p : ℕ) : ℚᵘⁿ_[p]) := by simp [Qp_embd]
    rw [hQp]
    have hp_val : Valued.v ((p : ℚᵘⁿ_[p])) =
        ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) :
          WithZero (Multiplicative ℤ)) := by
      rw [show ((p : ℚᵘⁿ_[p])) = algebraMap (ℤᵘⁿ_[p]) (ℚᵘⁿ_[p]) (p : ℤᵘⁿ_[p]) from by
        push_cast; rfl]
      rw [valued_algebraMap]
      have hirr : Irreducible (p : ℤᵘⁿ_[p]) := WittVector.irreducible p
      have hpe : (IsDiscreteValuationRing.maximalIdeal (ℤᵘⁿ_[p])).asIdeal =
          Ideal.span {(p : ℤᵘⁿ_[p])} := hirr.maximalIdeal_eq
      rw [IsDedekindDomain.HeightOneSpectrum.intValuation_singleton _
        (WittVector.p_nonzero p _) hpe]
      rfl
    rw [hp_val]
    have hu_val : Valued.v (Qp_embd ((u : ℤ_[p]) : ℚ_[p])) = 1 := by
      have hQpu : Qp_embd ((u : ℤ_[p]) : ℚ_[p]) =
          (algebraMap (ℤᵘⁿ_[p]) (ℚᵘⁿ_[p]))
            (((WittVector.map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p)))).comp
              (WittVector.fromPadicInt p)) (u : ℤ_[p])) := by
        change (Qp_embd : ℚ_[p] →+* ℚᵘⁿ_[p]) ((algebraMap ℤ_[p] ℚ_[p]) (u : ℤ_[p])) = _
        change (IsFractionRing.map _ : ℚ_[p] →+* ℚᵘⁿ_[p])
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
      rw [show (IsDiscreteValuationRing.maximalIdeal (ℤᵘⁿ_[p])).asIdeal =
          IsLocalRing.maximalIdeal (ℤᵘⁿ_[p]) from rfl] at hmem
      exact (IsLocalRing.notMem_maximalIdeal.mpr hu_unit) hmem
    rw [hu_val, one_mul]
    rw [← WithZero.coe_zpow]
    congr 1
    rw [← ofAdd_zsmul vx (-1 : ℤ)]
    congr 1; ring

noncomputable instance (p : ℕ) [Fact (Nat.Prime p)] : NontriviallyNormedField ℚᵘⁿ_[p] :=
  Valued.toNontriviallyNormedField (ℚᵘⁿ_[p]) (WithZero (Multiplicative ℤ))

-- View ℚᵘⁿ_[p] as an algebra over ℚ_[p] via the embedding defined above.
noncomputable instance (p : ℕ) [Fact (Nat.Prime p)] : Algebra ℚ_[p] (ℚᵘⁿ_[p]) := (Qp_embd).toAlgebra

end QpUn

end TrustworthyKedlaya
