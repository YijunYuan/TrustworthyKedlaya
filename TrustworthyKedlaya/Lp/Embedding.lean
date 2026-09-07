/-
Copyright (c) 2026 Shanwen Wang, Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import TrustworthyKedlaya.Lp.Valued
public import TrustworthyKedlaya.Lp.AlgClosed
public import TrustworthyKedlaya.Lp.QpUnEmbedding

/-!
# Embedding `ℂ_p` into `𝕃_p`

Since `𝕃_[p]` is algebraically closed (`AlgClosed.lean`) and a `ℚᵘⁿ_[p]`-algebra (through
`ℚᵘⁿ_[p] ⊆ ℚᶜᵘⁿ_[p] → 𝕃_[p]`), the algebraic closure `PadicAlgCl p` of `ℚ_[p]` (which is a
`ℚᵘⁿ_[p]`-algebra through the embedding `QpUn.algClEmbd` of `QpUnEmbedding.lean`) embeds into it
**over `ℚᵘⁿ_[p]`**.  The embedding is
**isometric**: the composite `ℚ_[p] → 𝕃_[p]` preserves the valuation, and by the uniqueness of
the extension of the `p`-adic norm to an algebraic extension of the complete field `ℚ_[p]`
(`spectralNorm_unique_field_norm_ext`) the pulled-back norm `‖·‖ ∘ embd` must be the spectral
norm of `PadicAlgCl p`.  As `𝕃_[p]` is complete (`Valued.lean`), the embedding extends
continuously to the completion `ℂ_[p]` of `PadicAlgCl p`, again isometrically.

Lifting over `ℚᵘⁿ_[p]` rather than over `ℚ_[p]` is what makes the embedding `ℂ_[p] → 𝕃_[p]`
**compatible with the structure map `ℚᶜᵘⁿ_[p] → 𝕃_[p]`** of `𝕃_[p]`: the two maps
`ℚᶜᵘⁿ_[p] → ℂ_[p] → 𝕃_[p]` and `ℚᶜᵘⁿ_[p] → 𝕃_[p]` are continuous and agree on the dense
subfield `ℚᵘⁿ_[p]`, hence everywhere.  Thus `ℂ_[p] → 𝕃_[p]` is a `ℚᶜᵘⁿ_[p]`-algebra
homomorphism, and the whole tower

`ℚ_[p] ⊆ ℚᵘⁿ_[p] ⊆ ℚᶜᵘⁿ_[p] ⊆ ℂ_[p] ⊆ 𝕃_[p]`, `ℚᵘⁿ_[p] → PadicAlgCl p ⊆ ℂ_[p] ⊆ 𝕃_[p]`

commutes (`IsScalarTower ℚᶜᵘⁿ_[p] ℂ_[p] 𝕃_[p]`, `IsScalarTower ℚ_[p] ℂ_[p] 𝕃_[p]`, `coe_coe`,
`coe_algebraMap_QpCUn`, ...).

## Main declarations

- `TrustworthyKedlaya.pAdicHahnSeries.val_algebraMap_Qp`,
  `TrustworthyKedlaya.pAdicHahnSeries.norm_algebraMap_QpCUn`: the structure maps
  `ℚ_[p] → 𝕃_[p]` and `ℚᶜᵘⁿ_[p] → 𝕃_[p]` preserve the valuation / are isometric;
- `TrustworthyKedlaya.pAdicHahnSeries.algClEmbd`: the embedding
  `PadicAlgCl p →ₐ[ℚ_[p]] 𝕃_[p]`, obtained by restricting scalars from the `ℚᵘⁿ_[p]`-linear
  lift `algClEmbdQpUn`; `norm_algClEmbd : ‖algClEmbd p x‖ = ‖x‖` and
  `algClEmbd_coe : algClEmbd p (x : PadicAlgCl p) = algebraMap ℚᵘⁿ_[p] 𝕃_[p] x`;
- `TrustworthyKedlaya.pAdicHahnSeries.complexEmbd`: the continuous extension
  `ℂ_[p] →ₐ[ℚᶜᵘⁿ_[p]] 𝕃_[p]` of `algClEmbd p`, as a bundled `ℚᶜᵘⁿ_[p]`-algebra homomorphism,
  and the instance `Algebra ℂ_[p] 𝕃_[p]` it defines, with the towers
  `IsScalarTower ℚᶜᵘⁿ_[p] ℂ_[p] 𝕃_[p]`, `IsScalarTower ℚᵘⁿ_[p] ℂ_[p] 𝕃_[p]` and
  `IsScalarTower ℚ_[p] ℂ_[p] 𝕃_[p]`;
- `TrustworthyKedlaya.pAdicHahnSeries.ofPadicComplex`: the same map as a plain function,
  registered as the coercion `ℂ_[p] → 𝕃_[p]`.  This is the **user-facing API** and the only
  map into `𝕃_[p]` defined in this file: one writes `(x : 𝕃_[p])` for `x : ℂ_[p]`, and `simp`
  normalises `complexEmbd p x` and `algebraMap ℂ_[p] 𝕃_[p] x` to `↑x`.  The `simp`/`norm_cast`
  lemmas `coe_add`, `coe_mul`, `coe_inj`, `coe_smul`, ... and `norm_coe : ‖(x : 𝕃_[p])‖ = ‖x‖`,
  `coe_coe` (it extends `algClEmbd`), `coe_algebraMap_QpCUn` (it extends the structure map of
  `ℚᶜᵘⁿ_[p]`), `continuous_coe`, `isometry_coe`, `coe_injective` transfer the properties of the
  embedding to this notation.
-/

@[expose] public section

namespace TrustworthyKedlaya.pAdicHahnSeries

open WittVector Filter Topology

open scoped NNReal

variable {p : ℕ} [hp : Fact (Nat.Prime p)]

/-! ### The valuation on the base field

The structure map `ℚ_[p] → 𝕃_[p]` factors through `ℚᶜᵘⁿ_[p]`, and `ℚᶜᵘⁿ_[p]` is the fraction
field of the discrete valuation ring `ℤᶜᵘⁿ_[p]` with uniformiser `p`.  A unit of
`ℤᶜᵘⁿ_[p]` maps to a series with a unit leading coefficient at position `0`, so it has
valuation `0`, and `p` has valuation `1` (`val_p_eq_one`). -/

/-- The multiplicativity of `valQ` on nonzero elements. -/
theorem valQ_mul {x y : 𝕃_[p]} (hx : x ≠ 0) (hy : y ≠ 0) : valQ (x * y) = valQ x + valQ y := by
  have h := (val p).map_mul x y
  rw [← coe_valQ (mul_ne_zero hx hy), ← coe_valQ hx, ← coe_valQ hy, ← WithTop.coe_add] at h
  exact_mod_cast h

/-- The image of a unit of `ℤᶜᵘⁿ_[p]` has valuation `0`. -/
theorem val_ZpUn_embd_unit (u : (ℤᶜᵘⁿ_[p])ˣ) : val p (ZpUn_embd (u : ℤᶜᵘⁿ_[p])) = 0 := by
  change val p (Ideal.Quotient.mk (NullSeriesIdeal p)
    (HahnSeries.single (0 : ℚ) (u : ℤᶜᵘⁿ_[p]))) = 0
  have h := val_mkLp_eq_of_isUnit_leading (p := p)
    (Δ := HahnSeries.single (0 : ℚ) (u : ℤᶜᵘⁿ_[p])) (q₀ := 0) ?_ ?_
  · rw [h]; rfl
  · rw [HahnSeries.coeff_single, if_pos rfl]
    exact u.isUnit
  · intro q hq
    rw [HahnSeries.coeff_single, if_neg hq.ne]

/-- The image of `p ^ n` has valuation `n`. -/
theorem val_ZpUn_embd_p_pow (n : ℕ) :
    val p (ZpUn_embd ((p : ℤᶜᵘⁿ_[p]) ^ n)) = ((n : ℚ) : WithTop ℚ) := by
  rw [map_pow, map_natCast, AddValuation.map_pow, val_p_eq_one, ← WithTop.coe_nsmul,
    nsmul_eq_mul, mul_one]

/-- The valuation of the image of a nonzero Witt vector is the exponent of `p` in it, i.e.
minus the logarithm of its `intValuation`. -/
theorem val_ZpUn_embd {a : ℤᶜᵘⁿ_[p]} (ha : a ≠ 0) :
    val p (ZpUn_embd a) = ((-WithZero.log
      ((IsDiscreteValuationRing.maximalIdeal (ℤᶜᵘⁿ_[p])).intValuation a) : ℤ) : ℚ) := by
  obtain ⟨n, u, rfl⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha (WittVector.irreducible p)
  have hmax : (IsDiscreteValuationRing.maximalIdeal (ℤᶜᵘⁿ_[p])).asIdeal
      = Ideal.span {(p : ℤᶜᵘⁿ_[p])} := (WittVector.irreducible p).maximalIdeal_eq
  have hu : (IsDiscreteValuationRing.maximalIdeal (ℤᶜᵘⁿ_[p])).intValuation (u : ℤᶜᵘⁿ_[p]) = 1 := by
    rw [IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff]
    rw [show (IsDiscreteValuationRing.maximalIdeal (ℤᶜᵘⁿ_[p])).asIdeal =
      IsLocalRing.maximalIdeal (ℤᶜᵘⁿ_[p]) from rfl]
    exact IsLocalRing.notMem_maximalIdeal.mpr u.isUnit
  rw [map_mul, AddValuation.map_mul, val_ZpUn_embd_unit, val_ZpUn_embd_p_pow, zero_add,
    Valuation.map_mul, Valuation.map_pow, hu, one_mul,
    (IsDiscreteValuationRing.maximalIdeal (ℤᶜᵘⁿ_[p])).intValuation_singleton
      (WittVector.p_nonzero p _) hmax,
    ← WithZero.exp_nsmul, WithZero.log_exp]
  congr 2
  simp

/-- The structure map `ℤᶜᵘⁿ_[p] → ℚᶜᵘⁿ_[p] → 𝕃_[p]` is `ZpUn_embd`. -/
theorem algebraMap_QpCUn_algebraMap (a : ℤᶜᵘⁿ_[p]) :
    algebraMap ℚᶜᵘⁿ_[p] 𝕃_[p] (algebraMap ℤᶜᵘⁿ_[p] ℚᶜᵘⁿ_[p] a) = ZpUn_embd a := by
  change QpCUn_embd (algebraMap ℤᶜᵘⁿ_[p] ℚᶜᵘⁿ_[p] a) = ZpUn_embd a
  unfold QpCUn_embd
  exact IsFractionRing.lift_algebraMap (g := ZpUn_embd) ZpUn_embd_injective a

/-- **The structure map `ℚᶜᵘⁿ_[p] → 𝕃_[p]` preserves the valuation**: the valuation of the
image of a nonzero `y` is minus the logarithm of the (multiplicative, `p ↦ p⁻¹`) valuation
of `y`. -/
theorem val_algebraMap_QpCUn {y : ℚᶜᵘⁿ_[p]} (hy : y ≠ 0) :
    val p (algebraMap ℚᶜᵘⁿ_[p] 𝕃_[p] y) = ((-WithZero.log (Valued.v y) : ℤ) : ℚ) := by
  obtain ⟨a, b, hb, hy_eq⟩ := IsFractionRing.div_surjective (A := ℤᶜᵘⁿ_[p]) y
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hbK : algebraMap ℤᶜᵘⁿ_[p] ℚᶜᵘⁿ_[p] b ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective ℤᶜᵘⁿ_[p] ℚᶜᵘⁿ_[p])).mpr hb0
  have hmul : y * algebraMap ℤᶜᵘⁿ_[p] ℚᶜᵘⁿ_[p] b = algebraMap ℤᶜᵘⁿ_[p] ℚᶜᵘⁿ_[p] a := by
    rw [← hy_eq, div_mul_cancel₀ _ hbK]
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero, mul_eq_zero] at hmul
    exact hmul.elim hy hbK
  have hinj : Function.Injective (algebraMap ℚᶜᵘⁿ_[p] 𝕃_[p]) :=
    (algebraMap ℚᶜᵘⁿ_[p] 𝕃_[p]).injective
  have hyL : algebraMap ℚᶜᵘⁿ_[p] 𝕃_[p] y ≠ 0 := (map_ne_zero_iff _ hinj).mpr hy
  have hbL : ZpUn_embd b ≠ 0 := (map_ne_zero_iff _ ZpUn_embd_injective).mpr hb0
  have haL : ZpUn_embd a ≠ 0 := (map_ne_zero_iff _ ZpUn_embd_injective).mpr ha0
  -- the valuations of the images in `𝕃_[p]`
  have h1 := congrArg (fun z => valQ (algebraMap ℚᶜᵘⁿ_[p] 𝕃_[p] z)) hmul
  simp only [map_mul, algebraMap_QpCUn_algebraMap] at h1
  rw [valQ_mul hyL hbL] at h1
  have hva : valQ (ZpUn_embd a) = ((-WithZero.log
      ((IsDiscreteValuationRing.maximalIdeal (ℤᶜᵘⁿ_[p])).intValuation a) : ℤ) : ℚ) := by
    have := val_ZpUn_embd ha0
    rw [← coe_valQ haL] at this
    exact_mod_cast this
  have hvb : valQ (ZpUn_embd b) = ((-WithZero.log
      ((IsDiscreteValuationRing.maximalIdeal (ℤᶜᵘⁿ_[p])).intValuation b) : ℤ) : ℚ) := by
    have := val_ZpUn_embd hb0
    rw [← coe_valQ hbL] at this
    exact_mod_cast this
  -- the valuations in `ℚᶜᵘⁿ_[p]`
  have h2 := congrArg (fun z => WithZero.log (Valued.v z)) hmul
  simp only [Valuation.map_mul] at h2
  rw [WithZero.log_mul ((Valued.v).ne_zero_iff.mpr hy) ((Valued.v).ne_zero_iff.mpr hbK),
    QpCUn.valued_algebraMap, QpCUn.valued_algebraMap] at h2
  rw [← coe_valQ hyL]
  congr 1
  rw [hva, hvb] at h1
  have h2' : ((WithZero.log (Valued.v y) : ℤ) : ℚ)
      + ((WithZero.log ((IsDiscreteValuationRing.maximalIdeal (ℤᶜᵘⁿ_[p])).intValuation b) : ℤ) : ℚ)
      = ((WithZero.log ((IsDiscreteValuationRing.maximalIdeal (ℤᶜᵘⁿ_[p])).intValuation a)
        : ℤ) : ℚ) := by
    exact_mod_cast h2
  push_cast at h1 h2' ⊢
  linarith

/-- The structure map `ℚ_[p] → 𝕃_[p]` factors through `ℚᶜᵘⁿ_[p]`. -/
theorem algebraMap_Qp_eq (x : ℚ_[p]) :
    algebraMap ℚ_[p] 𝕃_[p] x = algebraMap ℚᶜᵘⁿ_[p] 𝕃_[p] (QpCUn.Qp_embd x) := rfl

/-- **The structure map `ℚ_[p] → 𝕃_[p]` preserves the valuation.** -/
theorem val_algebraMap_Qp {x : ℚ_[p]} (hx : x ≠ 0) :
    val p (algebraMap ℚ_[p] 𝕃_[p] x) = ((x.valuation : ℚ) : WithTop ℚ) := by
  have hx' : QpCUn.Qp_embd x ≠ 0 :=
    (map_ne_zero_iff _ (QpCUn.Qp_embd (p := p)).injective).mpr hx
  rw [algebraMap_Qp_eq, val_algebraMap_QpCUn hx', ← QpCUn.Qp_embd_keep_val,
    Padic.mulValuation_toFun, if_neg hx, WithZero.log_exp, neg_neg]

theorem valQ_algebraMap_Qp {x : ℚ_[p]} (hx : x ≠ 0) :
    valQ (algebraMap ℚ_[p] 𝕃_[p] x) = (x.valuation : ℚ) := by
  have hxL : algebraMap ℚ_[p] 𝕃_[p] x ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap ℚ_[p] 𝕃_[p]).injective).mpr hx
  have := val_algebraMap_Qp hx
  rw [← coe_valQ hxL] at this
  exact_mod_cast this

/-- **The structure map `ℚ_[p] → 𝕃_[p]` is isometric.** -/
@[simp] theorem norm_algebraMap_Qp (x : ℚ_[p]) : ‖algebraMap ℚ_[p] 𝕃_[p] x‖ = ‖x‖ := by
  by_cases hx : x = 0
  · rw [hx, map_zero, norm_zero, norm_zero]
  · have hxL : algebraMap ℚ_[p] 𝕃_[p] x ≠ 0 :=
      (map_ne_zero_iff _ (algebraMap ℚ_[p] 𝕃_[p]).injective).mpr hx
    rw [norm_eq_of_ne_zero hxL, valQ_algebraMap_Qp hx, Padic.norm_eq_zpow_neg_valuation hx,
      ← Real.rpow_intCast]
    push_cast
    rfl

/-- **The structure map `ℚᶜᵘⁿ_[p] → 𝕃_[p]` is isometric.** -/
@[simp] theorem norm_algebraMap_QpCUn (y : ℚᶜᵘⁿ_[p]) : ‖algebraMap ℚᶜᵘⁿ_[p] 𝕃_[p] y‖ = ‖y‖ := by
  by_cases hy : y = 0
  · rw [hy, map_zero, norm_zero, norm_zero]
  · have hyL : algebraMap ℚᶜᵘⁿ_[p] 𝕃_[p] y ≠ 0 :=
      (map_ne_zero_iff _ (algebraMap ℚᶜᵘⁿ_[p] 𝕃_[p]).injective).mpr hy
    have hv : valQ (algebraMap ℚᶜᵘⁿ_[p] 𝕃_[p] y) = ((-WithZero.log (Valued.v y) : ℤ) : ℚ) := by
      have := val_algebraMap_QpCUn hy
      rw [← coe_valQ hyL] at this
      exact_mod_cast this
    rw [norm_eq_of_ne_zero hyL, hv, QpCUn.norm_eq_zpow_log_valued hy, ← Real.rpow_intCast]
    push_cast
    ring_nf

theorem isometry_algebraMap_QpCUn : Isometry (algebraMap ℚᶜᵘⁿ_[p] 𝕃_[p]) :=
  AddMonoidHomClass.isometry_of_norm _ norm_algebraMap_QpCUn

theorem continuous_algebraMap_QpCUn : Continuous (algebraMap ℚᶜᵘⁿ_[p] 𝕃_[p]) :=
  isometry_algebraMap_QpCUn.continuous

/-! ### `ℚᵘⁿ_[p]` inside `𝕃_[p]`

`𝕃_[p]` is a `ℚᵘⁿ_[p]`-algebra through the restriction of the structure map `ℚᶜᵘⁿ_[p] → 𝕃_[p]`
to `ℚᵘⁿ_[p] ⊆ ℚᶜᵘⁿ_[p]`; `IsScalarTower ℚᵘⁿ_[p] ℚᶜᵘⁿ_[p] 𝕃_[p]` holds definitionally.  (Since
`ℚᵘⁿ_[p]` is a type synonym and not a subtype, this instance has to be declared by hand; see
`TrustworthyKedlaya.Lp.QpUn`.) -/

/-- `𝕃_[p]` as a `ℚᵘⁿ_[p]`-algebra, through `ℚᵘⁿ_[p] ⊆ ℚᶜᵘⁿ_[p] → 𝕃_[p]`. -/
noncomputable instance : Algebra ℚᵘⁿ_[p] 𝕃_[p] :=
  ((algebraMap ℚᶜᵘⁿ_[p] 𝕃_[p]).comp (algebraMap ℚᵘⁿ_[p] ℚᶜᵘⁿ_[p])).toAlgebra

/-- `simp` normal form: the image of `x : ℚᵘⁿ_[p]` in `𝕃_[p]` is that of `(x : ℚᶜᵘⁿ_[p])`. -/
@[simp] theorem algebraMap_QpUn_apply (x : ℚᵘⁿ_[p]) :
    algebraMap ℚᵘⁿ_[p] 𝕃_[p] x = algebraMap ℚᶜᵘⁿ_[p] 𝕃_[p] (x : ℚᶜᵘⁿ_[p]) :=
  rfl

instance : IsScalarTower ℚᵘⁿ_[p] ℚᶜᵘⁿ_[p] 𝕃_[p] :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

instance : IsScalarTower ℚ_[p] ℚᵘⁿ_[p] 𝕃_[p] :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

theorem norm_algebraMap_QpUn (x : ℚᵘⁿ_[p]) : ‖algebraMap ℚᵘⁿ_[p] 𝕃_[p] x‖ = ‖x‖ := by
  rw [algebraMap_QpUn_apply, norm_algebraMap_QpCUn, QpUn.norm_coe]

/-! ### The embedding of the algebraic closure of `ℚ_[p]`

`PadicAlgCl p` is a `ℚᵘⁿ_[p]`-algebra (through `QpUn.algClEmbd`, see `QpUnEmbedding.lean`) and
algebraic over `ℚᵘⁿ_[p]`; so it embeds into the algebraically closed `ℚᵘⁿ_[p]`-algebra `𝕃_[p]`
over `ℚᵘⁿ_[p]`.  We export the `ℚ_[p]`-algebra homomorphism `algClEmbd` together with the
`ℚᵘⁿ_[p]`-linearity `algClEmbd_coe`. -/

/-- An embedding of the algebraic closure `PadicAlgCl p` of `ℚ_[p]` into `𝕃_[p]` over
`ℚᵘⁿ_[p]`, provided by the algebraic closedness of `𝕃_[p]`.  (Any two such embeddings differ
by a `ℚᵘⁿ_[p]`-automorphism of `PadicAlgCl p`.) -/
noncomputable def algClEmbdQpUn (p : ℕ) [Fact (Nat.Prime p)] :
    PadicAlgCl p →ₐ[ℚᵘⁿ_[p]] 𝕃_[p] :=
  IsAlgClosed.lift

/-- The embedding `PadicAlgCl p → 𝕃_[p]`, as a `ℚ_[p]`-algebra homomorphism: the restriction
of scalars of the `ℚᵘⁿ_[p]`-linear `algClEmbdQpUn`. -/
noncomputable def algClEmbd (p : ℕ) [Fact (Nat.Prime p)] : PadicAlgCl p →ₐ[ℚ_[p]] 𝕃_[p] :=
  (algClEmbdQpUn p).restrictScalars ℚ_[p]

theorem algClEmbd_apply (x : PadicAlgCl p) : algClEmbd p x = algClEmbdQpUn p x := rfl

/-- **The embedding `PadicAlgCl p → 𝕃_[p]` is `ℚᵘⁿ_[p]`-linear**: on `ℚᵘⁿ_[p] ⊆ PadicAlgCl p`
it is the structure map `ℚᵘⁿ_[p] → 𝕃_[p]`. -/
@[simp] theorem algClEmbd_coe (x : ℚᵘⁿ_[p]) :
    algClEmbd p (x : PadicAlgCl p) = algebraMap ℚᵘⁿ_[p] 𝕃_[p] x :=
  (algClEmbdQpUn p).commutes x

theorem algClEmbd_injective : Function.Injective (algClEmbd p) :=
  (algClEmbd p : PadicAlgCl p →+* 𝕃_[p]).injective

theorem algClEmbd_algebraMap (x : ℚ_[p]) :
    algClEmbd p (algebraMap ℚ_[p] (PadicAlgCl p) x) = algebraMap ℚ_[p] 𝕃_[p] x :=
  (algClEmbd p).commutes x

/-- **The embedding `PadicAlgCl p → 𝕃_[p]` is isometric** (hence preserves the valuation):
the norm pulled back from `𝕃_[p]` is a multiplicative norm on `PadicAlgCl p` extending the
`p`-adic norm of `ℚ_[p]`, and such a norm is unique
(`spectralNorm_unique_field_norm_ext`). -/
theorem norm_algClEmbd (x : PadicAlgCl p) : ‖algClEmbd p x‖ = ‖x‖ := by
  let f : AbsoluteValue (PadicAlgCl p) ℝ :=
    { toFun := fun y => ‖algClEmbd p y‖
      map_mul' := fun a b => by simp only [map_mul, norm_mul]
      nonneg' := fun a => norm_nonneg _
      eq_zero' := fun a => by
        simp only [norm_eq_zero]
        exact map_eq_zero_iff _ algClEmbd_injective
      add_le' := fun a b => by
        simp only [map_add]
        exact norm_add_le _ _ }
  have hext : ∀ k : ℚ_[p], f (algebraMap ℚ_[p] (PadicAlgCl p) k) = ‖k‖ := fun k => by
    change ‖algClEmbd p (algebraMap ℚ_[p] (PadicAlgCl p) k)‖ = ‖k‖
    rw [algClEmbd_algebraMap, norm_algebraMap_Qp]
  have h := spectralNorm_unique_field_norm_ext (K := ℚ_[p]) (L := PadicAlgCl p) hext x
  rw [PadicAlgCl.spectralNorm_eq] at h
  exact h

theorem nnnorm_algClEmbd (x : PadicAlgCl p) : ‖algClEmbd p x‖₊ = ‖x‖₊ := by
  ext
  exact norm_algClEmbd x

/-- The valuation of `PadicAlgCl p` (the `ℝ≥0`-valued `p`-adic norm) is `p^(-val)` of the
image in `𝕃_[p]`. -/
theorem valued_v_algClEmbd (x : PadicAlgCl p) :
    (Valued.v x : ℝ≥0) = expNNReal p (val p (algClEmbd p x)) := by
  rw [PadicAlgCl.valuation_def, ← nnnorm_algClEmbd]
  ext
  exact norm_eq _

/-- The image of a nonzero element has finite valuation `val`, with `‖x‖ = p^(-val)`. -/
theorem norm_eq_rpow_neg_valQ_algClEmbd {x : PadicAlgCl p} (hx : x ≠ 0) :
    ‖x‖ = (p : ℝ) ^ (-(valQ (algClEmbd p x) : ℝ)) := by
  rw [← norm_algClEmbd, norm_eq_of_ne_zero ((map_ne_zero_iff _ algClEmbd_injective).mpr hx)]

theorem isometry_algClEmbd : Isometry (algClEmbd p) :=
  AddMonoidHomClass.isometry_of_norm _ norm_algClEmbd

theorem continuous_algClEmbd : Continuous (algClEmbd p) :=
  isometry_algClEmbd.continuous

/-! ### The extension to `ℂ_[p]`

`ℂ_[p]` is the completion of `PadicAlgCl p`, and `𝕃_[p]` is complete, so the continuous
ring homomorphism `algClEmbd p` extends uniquely to a continuous ring homomorphism
`ℂ_[p] → 𝕃_[p]`.  It is `ℚᶜᵘⁿ_[p]`-linear, because it is `ℚᵘⁿ_[p]`-linear (`algClEmbd_coe`)
and `ℚᵘⁿ_[p]` is dense in `ℚᶜᵘⁿ_[p]`. -/

/-- The continuous extension of `algClEmbd p` to the `p`-adic complex numbers, as a ring
homomorphism. -/
noncomputable def complexEmbdRingHom (p : ℕ) [Fact (Nat.Prime p)] : ℂ_[p] →+* 𝕃_[p] :=
  UniformSpace.Completion.extensionHom (algClEmbd p : PadicAlgCl p →+* 𝕃_[p])
    continuous_algClEmbd

theorem complexEmbdRingHom_coe (x : PadicAlgCl p) :
    complexEmbdRingHom p (x : ℂ_[p]) = algClEmbd p x :=
  UniformSpace.Completion.extensionHom_coe _ _ x

theorem continuous_complexEmbdRingHom : Continuous (complexEmbdRingHom p) :=
  UniformSpace.Completion.continuous_extension

/-- **The embedding `ℂ_[p] → 𝕃_[p]` is `ℚᶜᵘⁿ_[p]`-linear**: composed with the embedding
`ℚᶜᵘⁿ_[p] → ℂ_[p]` it is the structure map `ℚᶜᵘⁿ_[p] → 𝕃_[p]`.  Both sides are continuous and
agree on the dense subfield `ℚᵘⁿ_[p]` by `algClEmbd_coe`. -/
theorem complexEmbdRingHom_algebraMap_QpCUn (y : ℚᶜᵘⁿ_[p]) :
    complexEmbdRingHom p (algebraMap ℚᶜᵘⁿ_[p] ℂ_[p] y) = algebraMap ℚᶜᵘⁿ_[p] 𝕃_[p] y := by
  refine (QpUn.denseRange_algebraMap p).induction_on y ?_ ?_
  · exact isClosed_eq (continuous_complexEmbdRingHom.comp QpCUn.continuous_algebraMap_complex)
      continuous_algebraMap_QpCUn
  · intro x
    rw [QpUn.algebraMap_QpCUn_apply, QpCUn.algebraMap_complex_coe, complexEmbdRingHom_coe,
      algClEmbd_coe, algebraMap_QpUn_apply]

/-- The continuous extension of `algClEmbd p` to the `p`-adic complex numbers, as a
`ℚᶜᵘⁿ_[p]`-algebra homomorphism `ℂ_[p] →ₐ[ℚᶜᵘⁿ_[p]] 𝕃_[p]`.

This is the bundled form of the embedding; it carries the ring/algebra structure and is what
one should use to build further algebra homomorphisms (`AlgHom.comp`, `AlgHom.range`, ...).
For computations with elements, use the coercion `(x : 𝕃_[p])` (`ofPadicComplex`) instead:
`simp` rewrites `complexEmbd p x` to `↑x` via `complexEmbd_apply_eq_coe`. -/
noncomputable def complexEmbd (p : ℕ) [Fact (Nat.Prime p)] : ℂ_[p] →ₐ[ℚᶜᵘⁿ_[p]] 𝕃_[p] :=
  { complexEmbdRingHom p with commutes' := complexEmbdRingHom_algebraMap_QpCUn }

theorem complexEmbd_apply (x : ℂ_[p]) : complexEmbd p x = complexEmbdRingHom p x := rfl

theorem complexEmbd_injective : Function.Injective (complexEmbd p) :=
  (complexEmbd p : ℂ_[p] →+* 𝕃_[p]).injective

/-! ### The coercion `ℂ_[p] → 𝕃_[p]`

We register the embedding `complexEmbd p` as a coercion, so that a `p`-adic complex number
`x : ℂ_[p]` can be written `(x : 𝕃_[p])`.  The function `ofPadicComplex` is a thin wrapper
around `complexEmbd p` (definitionally equal to it, see `coe_eq`) whose only purpose is to
carry the `@[coe]` attribute, so that it is displayed as `↑x` and understood by `norm_cast`.

The coercion is the canonical way to refer to elements of `ℂ_[p]` inside `𝕃_[p]`: the `simp`
lemmas `complexEmbd_apply_eq_coe`, `complexEmbdRingHom_apply_eq_coe` and
`algebraMap_complex_apply_eq_coe` normalise the applications of the bundled homomorphisms and
of `algebraMap ℂ_[p] 𝕃_[p]` to `↑x`, and all the properties of the embedding (it is an
isometric, continuous, injective `ℚᶜᵘⁿ_[p]`-algebra map extending `algClEmbd p`) are stated
below in terms of `↑`. -/

/-- The embedding `ℂ_[p] → 𝕃_[p]` as a plain function, registered as a coercion. -/
@[coe] noncomputable def ofPadicComplex (x : ℂ_[p]) : 𝕃_[p] := complexEmbd p x

noncomputable instance : Coe ℂ_[p] 𝕃_[p] := ⟨ofPadicComplex⟩

theorem coe_eq (x : ℂ_[p]) : (x : 𝕃_[p]) = complexEmbd p x := rfl

theorem coe_def : ((↑) : ℂ_[p] → 𝕃_[p]) = complexEmbd p := rfl

/-- `simp` normal form: the bundled algebra homomorphism applied to `x` is the coercion. -/
@[simp] theorem complexEmbd_apply_eq_coe (x : ℂ_[p]) : complexEmbd p x = (x : 𝕃_[p]) := rfl

/-- `simp` normal form: the bundled ring homomorphism applied to `x` is the coercion. -/
@[simp] theorem complexEmbdRingHom_apply_eq_coe (x : ℂ_[p]) :
    complexEmbdRingHom p x = (x : 𝕃_[p]) := rfl

@[simp, norm_cast] theorem coe_zero : ((0 : ℂ_[p]) : 𝕃_[p]) = 0 := map_zero (complexEmbd p)

@[simp, norm_cast] theorem coe_one : ((1 : ℂ_[p]) : 𝕃_[p]) = 1 := map_one (complexEmbd p)

@[simp, norm_cast] theorem coe_add (x y : ℂ_[p]) : ((x + y : ℂ_[p]) : 𝕃_[p]) = x + y :=
  map_add (complexEmbd p) x y

@[simp, norm_cast] theorem coe_mul (x y : ℂ_[p]) : ((x * y : ℂ_[p]) : 𝕃_[p]) = x * y :=
  map_mul (complexEmbd p) x y

@[simp, norm_cast] theorem coe_neg (x : ℂ_[p]) : ((-x : ℂ_[p]) : 𝕃_[p]) = -x :=
  map_neg (complexEmbd p) x

@[simp, norm_cast] theorem coe_sub (x y : ℂ_[p]) : ((x - y : ℂ_[p]) : 𝕃_[p]) = x - y :=
  map_sub (complexEmbd p) x y

@[simp, norm_cast] theorem coe_inv (x : ℂ_[p]) : ((x⁻¹ : ℂ_[p]) : 𝕃_[p]) = (x : 𝕃_[p])⁻¹ :=
  map_inv₀ (complexEmbd p) x

@[simp, norm_cast] theorem coe_div (x y : ℂ_[p]) : ((x / y : ℂ_[p]) : 𝕃_[p]) = x / y :=
  map_div₀ (complexEmbd p) x y

@[simp, norm_cast] theorem coe_pow (x : ℂ_[p]) (n : ℕ) :
    ((x ^ n : ℂ_[p]) : 𝕃_[p]) = (x : 𝕃_[p]) ^ n :=
  map_pow (complexEmbd p) x n

@[simp, norm_cast] theorem coe_zpow (x : ℂ_[p]) (n : ℤ) :
    ((x ^ n : ℂ_[p]) : 𝕃_[p]) = (x : 𝕃_[p]) ^ n :=
  map_zpow₀ (complexEmbd p) x n

@[simp, norm_cast] theorem coe_natCast (n : ℕ) : ((n : ℂ_[p]) : 𝕃_[p]) = n :=
  map_natCast (complexEmbd p) n

@[simp, norm_cast] theorem coe_intCast (n : ℤ) : ((n : ℂ_[p]) : 𝕃_[p]) = n :=
  map_intCast (complexEmbd p) n

@[simp, norm_cast] theorem coe_ratCast (q : ℚ) : ((q : ℂ_[p]) : 𝕃_[p]) = q :=
  map_ratCast (complexEmbd p) q

theorem coe_injective : Function.Injective ((↑) : ℂ_[p] → 𝕃_[p]) := complexEmbd_injective

@[simp, norm_cast] theorem coe_inj {x y : ℂ_[p]} : (x : 𝕃_[p]) = y ↔ x = y :=
  coe_injective.eq_iff

@[simp, norm_cast] theorem coe_eq_zero {x : ℂ_[p]} : (x : 𝕃_[p]) = 0 ↔ x = 0 :=
  map_eq_zero_iff _ complexEmbd_injective

theorem coe_ne_zero {x : ℂ_[p]} : (x : 𝕃_[p]) ≠ 0 ↔ x ≠ 0 := coe_eq_zero.not

/-! #### Compatibility with the subfields of `ℂ_[p]` -/

/-- The embedding of `ℂ_[p]` extends the embedding of `PadicAlgCl p`: on
`PadicAlgCl p ⊆ ℂ_[p]` the coercion is `algClEmbd p`. -/
@[simp] theorem coe_coe (x : PadicAlgCl p) : ((x : ℂ_[p]) : 𝕃_[p]) = algClEmbd p x :=
  complexEmbdRingHom_coe x

/-- **The embedding `ℂ_[p] → 𝕃_[p]` extends the structure map `ℚᶜᵘⁿ_[p] → 𝕃_[p]`.** -/
@[simp] theorem coe_algebraMap_QpCUn (y : ℚᶜᵘⁿ_[p]) :
    ((algebraMap ℚᶜᵘⁿ_[p] ℂ_[p] y : ℂ_[p]) : 𝕃_[p]) = algebraMap ℚᶜᵘⁿ_[p] 𝕃_[p] y :=
  (complexEmbd p).commutes y

/-- On `ℚᵘⁿ_[p] ⊆ PadicAlgCl p ⊆ ℂ_[p]` the coercion is the structure map `ℚᵘⁿ_[p] → 𝕃_[p]`
(which is also the image of `x` through `ℚᵘⁿ_[p] ⊆ ℚᶜᵘⁿ_[p] → ℂ_[p]`, by
`QpCUn.algebraMap_complex_coe`). -/
@[simp] theorem coe_coe_toAlgCl (x : ℚᵘⁿ_[p]) :
    (((x : PadicAlgCl p) : ℂ_[p]) : 𝕃_[p]) = algebraMap ℚᵘⁿ_[p] 𝕃_[p] x := by
  rw [coe_coe, algClEmbd_coe]

theorem coe_algebraMap_QpUn (x : ℚᵘⁿ_[p]) :
    ((algebraMap ℚᵘⁿ_[p] ℂ_[p] x : ℂ_[p]) : 𝕃_[p]) = algebraMap ℚᵘⁿ_[p] 𝕃_[p] x :=
  coe_coe_toAlgCl x

/-- On `ℚ_[p] ⊆ ℂ_[p]` the coercion is the structure map `ℚ_[p] → 𝕃_[p]`. -/
@[simp] theorem coe_algebraMap (x : ℚ_[p]) :
    ((algebraMap ℚ_[p] ℂ_[p] x : ℂ_[p]) : 𝕃_[p]) = algebraMap ℚ_[p] 𝕃_[p] x := by
  rw [IsScalarTower.algebraMap_apply ℚ_[p] ℚᶜᵘⁿ_[p] ℂ_[p], coe_algebraMap_QpCUn,
    ← IsScalarTower.algebraMap_apply]

/-- The coercion is `ℚᶜᵘⁿ_[p]`-linear. -/
@[simp, norm_cast] theorem coe_smul_QpCUn (c : ℚᶜᵘⁿ_[p]) (x : ℂ_[p]) :
    ((c • x : ℂ_[p]) : 𝕃_[p]) = c • (x : 𝕃_[p]) :=
  map_smul (complexEmbd p) c x

/-- The coercion is `ℚ_[p]`-linear. -/
@[simp, norm_cast] theorem coe_smul (k : ℚ_[p]) (x : ℂ_[p]) :
    ((k • x : ℂ_[p]) : 𝕃_[p]) = k • (x : 𝕃_[p]) := by
  rw [← IsScalarTower.algebraMap_smul ℚᶜᵘⁿ_[p] k x, coe_smul_QpCUn,
    IsScalarTower.algebraMap_smul]

/-! #### `𝕃_[p]` as a `ℂ_[p]`-algebra -/

/-- `𝕃_[p]` as a `ℂ_[p]`-algebra, through the coercion. -/
noncomputable instance : Algebra ℂ_[p] 𝕃_[p] := (complexEmbd p : ℂ_[p] →+* 𝕃_[p]).toAlgebra

/-- `simp` normal form: the structure map `ℂ_[p] → 𝕃_[p]` is the coercion. -/
@[simp] theorem algebraMap_complex_apply_eq_coe (x : ℂ_[p]) :
    algebraMap ℂ_[p] 𝕃_[p] x = (x : 𝕃_[p]) :=
  rfl

/-- **The tower `ℚᶜᵘⁿ_[p] ⊆ ℂ_[p] ⊆ 𝕃_[p]` commutes.** -/
instance : IsScalarTower ℚᶜᵘⁿ_[p] ℂ_[p] 𝕃_[p] :=
  IsScalarTower.of_algebraMap_eq fun c => (coe_algebraMap_QpCUn c).symm

/-- **The tower `ℚ_[p] ⊆ ℂ_[p] ⊆ 𝕃_[p]` commutes.** -/
instance : IsScalarTower ℚ_[p] ℂ_[p] 𝕃_[p] :=
  IsScalarTower.of_algebraMap_eq fun k => (coe_algebraMap k).symm

/-- **The tower `ℚᵘⁿ_[p] ⊆ ℂ_[p] ⊆ 𝕃_[p]` commutes**: the `ℚᵘⁿ_[p]`-linearity of the lift
`PadicAlgCl p → 𝕃_[p]`. -/
instance : IsScalarTower ℚᵘⁿ_[p] ℂ_[p] 𝕃_[p] :=
  IsScalarTower.of_algebraMap_eq fun x => (coe_algebraMap_QpUn x).symm

/-! #### Metric properties -/

theorem continuous_coe : Continuous ((↑) : ℂ_[p] → 𝕃_[p]) := continuous_complexEmbdRingHom

/-- **The embedding `ℂ_[p] → 𝕃_[p]` is isometric.** -/
@[simp, norm_cast] theorem norm_coe (x : ℂ_[p]) : ‖(x : 𝕃_[p])‖ = ‖x‖ := by
  refine UniformSpace.Completion.induction_on x ?_ ?_
  · exact isClosed_eq (continuous_norm.comp continuous_coe) continuous_norm
  · intro a
    rw [coe_coe, norm_algClEmbd, PadicComplex.norm_extends]

@[simp, norm_cast] theorem nnnorm_coe (x : ℂ_[p]) : ‖(x : 𝕃_[p])‖₊ = ‖x‖₊ := by
  ext
  exact norm_coe x

theorem isometry_coe : Isometry ((↑) : ℂ_[p] → 𝕃_[p]) :=
  AddMonoidHomClass.isometry_of_norm (complexEmbd p) norm_coe

/-- `𝕃_[p]` is a normed `ℂ_[p]`-algebra. -/
noncomputable instance : NormedAlgebra ℂ_[p] 𝕃_[p] where
  norm_smul_le c x := by rw [Algebra.smul_def, norm_mul, algebraMap_complex_apply_eq_coe, norm_coe]

/-- **The embedding `ℂ_[p] → 𝕃_[p]` preserves the valuation**: the valuation of `ℂ_[p]`
(the `ℝ≥0`-valued `p`-adic norm) is `p^(-val)` of the image in `𝕃_[p]`. -/
theorem valued_v_coe (x : ℂ_[p]) : (Valued.v x : ℝ≥0) = expNNReal p (val p (x : 𝕃_[p])) := by
  have h : ((Valued.v x : ℝ≥0) : ℝ) = ‖x‖ := by
    rw [PadicComplex.norm_eq_norm, Valuation.norm_def, PadicComplex.RankOne.hom_eq_embedding,
      Valuation.embedding_restrict]
  ext
  rw [h, ← norm_coe, norm_eq]

/-- The image of a nonzero `p`-adic complex number has finite valuation `val`, with
`‖x‖ = p^(-val)`. -/
theorem norm_eq_rpow_neg_valQ_coe {x : ℂ_[p]} (hx : x ≠ 0) :
    ‖x‖ = (p : ℝ) ^ (-(valQ (x : 𝕃_[p]) : ℝ)) := by
  rw [← norm_coe, norm_eq_of_ne_zero (coe_ne_zero.mpr hx)]

/-- The valuation of the image is `⊤` exactly for `x = 0`. -/
@[simp] theorem val_coe_eq_top_iff {x : ℂ_[p]} : val p (x : 𝕃_[p]) = ⊤ ↔ x = 0 := by
  rw [val_eq_top_iff, coe_eq_zero]

end TrustworthyKedlaya.pAdicHahnSeries
