/-
Copyright (c) 2026 Shanwen Wang, Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import TrustworthyKedlaya.Lp.LpValued
public import TrustworthyKedlaya.Lp.LpAlgClosed
public import TrustworthyKedlaya.Kedlaya.ShadowCalculus
public import Mathlib.NumberTheory.Padics.Complex

/-!
# Embedding `ℂ_p` into `𝕃_p`

Since `𝕃_[p]` is algebraically closed (`LpAlgClosed.lean`) and a `ℚ_[p]`-algebra, the
algebraic closure `PadicAlgCl p` of `ℚ_[p]` embeds into it over `ℚ_[p]`.  The embedding is
**isometric**: the composite `ℚ_[p] → 𝕃_[p]` preserves the valuation, and by the uniqueness of
the extension of the `p`-adic norm to an algebraic extension of the complete field `ℚ_[p]`
(`spectralNorm_unique_field_norm_ext`) the pulled-back norm `‖·‖ ∘ embd` must be the spectral
norm of `PadicAlgCl p`.  As `𝕃_[p]` is complete (`LpValued.lean`), the embedding extends
continuously to the completion `ℂ_[p]` of `PadicAlgCl p`, again isometrically.

## Main declarations

- `TrustworthyKedlaya.pAdicHahnSeries.val_algebraMap_Qp`: the structure map
  `ℚ_[p] → 𝕃_[p]` preserves the valuation;
- `TrustworthyKedlaya.pAdicHahnSeries.algClEmbd`: the embedding
  `PadicAlgCl p →ₐ[ℚ_[p]] 𝕃_[p]`, with `norm_algClEmbd : ‖algClEmbd p x‖ = ‖x‖`;
- `TrustworthyKedlaya.pAdicHahnSeries.complexEmbd`: the continuous extension
  `ℂ_[p] →ₐ[ℚ_[p]] 𝕃_[p]`, with `norm_complexEmbd : ‖complexEmbd p x‖ = ‖x‖`,
  `complexEmbd_coe` (it extends `algClEmbd`), `continuous_complexEmbd`,
  `isometry_complexEmbd` and `complexEmbd_injective`.
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
theorem norm_algebraMap_Qp (x : ℚ_[p]) : ‖algebraMap ℚ_[p] 𝕃_[p] x‖ = ‖x‖ := by
  by_cases hx : x = 0
  · rw [hx, map_zero, norm_zero, norm_zero]
  · have hxL : algebraMap ℚ_[p] 𝕃_[p] x ≠ 0 :=
      (map_ne_zero_iff _ (algebraMap ℚ_[p] 𝕃_[p]).injective).mpr hx
    rw [norm_eq_of_ne_zero hxL, valQ_algebraMap_Qp hx, Padic.norm_eq_zpow_neg_valuation hx,
      ← Real.rpow_intCast]
    push_cast
    rfl

/-! ### The embedding of the algebraic closure of `ℚ_[p]` -/

/-- An embedding of the algebraic closure `PadicAlgCl p` of `ℚ_[p]` into `𝕃_[p]` over
`ℚ_[p]`, provided by the algebraic closedness of `𝕃_[p]`.  (Any two such embeddings differ
by an automorphism of `PadicAlgCl p`.) -/
noncomputable def algClEmbd (p : ℕ) [Fact (Nat.Prime p)] : PadicAlgCl p →ₐ[ℚ_[p]] 𝕃_[p] :=
  IsAlgClosed.lift

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
`ℂ_[p] → 𝕃_[p]`. -/

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

/-- **The embedding `ℂ_[p] → 𝕃_[p]` is isometric.** -/
theorem norm_complexEmbdRingHom (x : ℂ_[p]) : ‖complexEmbdRingHom p x‖ = ‖x‖ := by
  refine UniformSpace.Completion.induction_on x ?_ ?_
  · exact isClosed_eq (continuous_norm.comp continuous_complexEmbdRingHom) continuous_norm
  · intro a
    rw [complexEmbdRingHom_coe, norm_algClEmbd, PadicComplex.norm_extends]

/-- The continuous extension of `algClEmbd p` to the `p`-adic complex numbers, as a
`ℚ_[p]`-algebra homomorphism `ℂ_[p] →ₐ[ℚ_[p]] 𝕃_[p]`. -/
noncomputable def complexEmbd (p : ℕ) [Fact (Nat.Prime p)] : ℂ_[p] →ₐ[ℚ_[p]] 𝕃_[p] :=
  { complexEmbdRingHom p with
    commutes' := fun k => by
      change complexEmbdRingHom p (algebraMap ℚ_[p] ℂ_[p] k) = algebraMap ℚ_[p] 𝕃_[p] k
      rw [IsScalarTower.algebraMap_apply ℚ_[p] (PadicAlgCl p) ℂ_[p], ← PadicComplex.coe_eq,
        complexEmbdRingHom_coe, algClEmbd_algebraMap] }

theorem complexEmbd_apply (x : ℂ_[p]) : complexEmbd p x = complexEmbdRingHom p x := rfl

/-- The embedding of `ℂ_[p]` extends the embedding of `PadicAlgCl p`. -/
theorem complexEmbd_coe (x : PadicAlgCl p) : complexEmbd p (x : ℂ_[p]) = algClEmbd p x :=
  complexEmbdRingHom_coe x

theorem complexEmbd_algebraMap (x : ℚ_[p]) :
    complexEmbd p (algebraMap ℚ_[p] ℂ_[p] x) = algebraMap ℚ_[p] 𝕃_[p] x :=
  (complexEmbd p).commutes x

theorem continuous_complexEmbd : Continuous (complexEmbd p) :=
  continuous_complexEmbdRingHom

/-- **The embedding `ℂ_[p] → 𝕃_[p]` is isometric.** -/
theorem norm_complexEmbd (x : ℂ_[p]) : ‖complexEmbd p x‖ = ‖x‖ :=
  norm_complexEmbdRingHom x

theorem nnnorm_complexEmbd (x : ℂ_[p]) : ‖complexEmbd p x‖₊ = ‖x‖₊ := by
  ext
  exact norm_complexEmbd x

theorem isometry_complexEmbd : Isometry (complexEmbd p) :=
  AddMonoidHomClass.isometry_of_norm _ norm_complexEmbd

theorem complexEmbd_injective : Function.Injective (complexEmbd p) :=
  (complexEmbd p : ℂ_[p] →+* 𝕃_[p]).injective

/-- **The embedding `ℂ_[p] → 𝕃_[p]` preserves the valuation**: the valuation of `ℂ_[p]`
(the `ℝ≥0`-valued `p`-adic norm) is `p^(-val)` of the image in `𝕃_[p]`. -/
theorem valued_v_complexEmbd (x : ℂ_[p]) :
    (Valued.v x : ℝ≥0) = expNNReal p (val p (complexEmbd p x)) := by
  have h : ((Valued.v x : ℝ≥0) : ℝ) = ‖x‖ := by
    rw [PadicComplex.norm_eq_norm, Valuation.norm_def, PadicComplex.RankOne.hom_eq_embedding,
      Valuation.embedding_restrict]
  ext
  rw [h, ← norm_complexEmbd, norm_eq]

/-- The image of a nonzero `p`-adic complex number has finite valuation `val`, with
`‖x‖ = p^(-val)`. -/
theorem norm_eq_rpow_neg_valQ_complexEmbd {x : ℂ_[p]} (hx : x ≠ 0) :
    ‖x‖ = (p : ℝ) ^ (-(valQ (complexEmbd p x) : ℝ)) := by
  rw [← norm_complexEmbd, norm_eq_of_ne_zero ((map_ne_zero_iff _ complexEmbd_injective).mpr hx)]

/-- The valuation of the image is `⊤` exactly for `x = 0`. -/
theorem val_complexEmbd_eq_top_iff {x : ℂ_[p]} : val p (complexEmbd p x) = ⊤ ↔ x = 0 := by
  rw [val_eq_top_iff, map_eq_zero_iff _ complexEmbd_injective]

end TrustworthyKedlaya.pAdicHahnSeries
