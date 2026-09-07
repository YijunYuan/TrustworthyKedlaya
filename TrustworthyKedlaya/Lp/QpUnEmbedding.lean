/-
Copyright (c) 2026 Shanwen Wang, Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import TrustworthyKedlaya.Lp.QpUn
public import Mathlib.NumberTheory.Padics.Complex

/-!
# Embedding `ℚᵘⁿ_[p]` and `ℚᶜᵘⁿ_[p]` into `ℂ_[p]`

This file organises the tower

`ℚ_[p] ⊆ ℚᵘⁿ_[p] ⊆ ℚᶜᵘⁿ_[p] ⊆ ℂ_[p]` and `ℚ_[p] ⊆ ℚᵘⁿ_[p] → PadicAlgCl p ⊆ ℂ_[p]`

inside `ℂ_[p]`, without reference to `𝕃_[p]`.  Everything is derived from a **single choice**, a
`ℚ_[p]`-embedding `QpUn.algClEmbd : ℚᵘⁿ_[p] →ₐ[ℚ_[p]] PadicAlgCl p` (which exists since
`ℚᵘⁿ_[p]` is algebraic over `ℚ_[p]` and `PadicAlgCl p` is algebraically closed; it is unique up
to `Gal(ℚᵘⁿ_[p]/ℚ_[p])`):

- `ℚᵘⁿ_[p] → PadicAlgCl p` is `QpUn.algClEmbd`.  It is isometric, by the uniqueness of the
  extension of the `p`-adic norm to the algebraic extension `ℚᵘⁿ_[p]` of the complete field
  `ℚ_[p]` (`spectralNorm_unique_field_norm_ext`);
- `ℚᵘⁿ_[p] → ℂ_[p]` (`QpUn.complexEmbd`) is its composite with the completion map
  `PadicAlgCl p → ℂ_[p]`;
- `ℚᶜᵘⁿ_[p] → ℂ_[p]` (`QpCUn.complexEmbd`) is the continuous extension of the previous map
  along the dense inclusion `ℚᵘⁿ_[p] ⊆ ℚᶜᵘⁿ_[p]` (`IsDenseInducing.extendRingHom`).

The last map is installed as the instance `Algebra ℚᶜᵘⁿ_[p] ℂ_[p]`.  Since `ℚᵘⁿ_[p]` is a
subfield of `ℚᶜᵘⁿ_[p]`, Mathlib then derives `Algebra ℚᵘⁿ_[p] ℂ_[p]` by restriction
(`Algebra.ofSubsemiring`), so that `IsScalarTower ℚᵘⁿ_[p] ℚᶜᵘⁿ_[p] ℂ_[p]` holds definitionally.
The compatibility of the two ways of embedding `ℚᵘⁿ_[p]` into `ℂ_[p]` (through `ℚᶜᵘⁿ_[p]` and
through `PadicAlgCl p`) is then the theorem `QpCUn.coe_algClEmbd`, which is
`IsDenseInducing.extend_eq`.

## Implementation notes

The chosen maps are exposed only through `Algebra` instances and `algebraMap` (never as
coercions); the canonical inclusions `ℚᵘⁿ_[p] ⊆ ℚᶜᵘⁿ_[p]` and `PadicAlgCl p ⊆ ℂ_[p]` keep
their `↑` notation.  The `simp` normal form of the image in `ℂ_[p]` of `x : ℚᵘⁿ_[p]`, whichever
way it is written, is `algebraMap ℚᶜᵘⁿ_[p] ℂ_[p] ↑x`.

**No `Algebra ℚᵘⁿ_[p] (PadicAlgCl p)` instance is installed**, although `QpUn.algClEmbd` would
provide one.  Such an instance would make Mathlib produce a second, non-definitionally-equal
action of `ℚᵘⁿ_[p]` on `ℂ_[p] = Completion (PadicAlgCl p)` through
`UniformSpace.Completion.instSMul`, competing with the restriction of the action of `ℚᶜᵘⁿ_[p]`;
the two agree only propositionally (by `QpCUn.coe_algClEmbd`).  Files which need `PadicAlgCl p`
as a `ℚᵘⁿ_[p]`-algebra (to lift over `ℚᵘⁿ_[p]`) should use a *local* instance built from
`QpUn.algClEmbd`, as `TrustworthyKedlaya.Lp.Embedding` does.

## Main declarations

- `TrustworthyKedlaya.QpUn.instIsAlgebraic`: `ℚᵘⁿ_[p]` is algebraic over `ℚ_[p]`;
- `TrustworthyKedlaya.QpUn.algClEmbd`: the embedding `ℚᵘⁿ_[p] →ₐ[ℚ_[p]] PadicAlgCl p`, with
  `QpUn.norm_algClEmbd` (it is isometric); its image `QpUn.algClRange`, an intermediate field
  of `PadicAlgCl p / ℚ_[p]` of which `PadicAlgCl p` is an algebraic closure, and the isomorphism
  `QpUn.algClEquiv : ℚᵘⁿ_[p] ≃ₐ[ℚ_[p]] QpUn.algClRange p`;
- `TrustworthyKedlaya.QpCUn.complexEmbd`: the embedding `ℚᶜᵘⁿ_[p] →ₐ[ℚ_[p]] ℂ_[p]`, with
  `QpCUn.norm_complexEmbd` (it is isometric), and the instances `Algebra ℚᶜᵘⁿ_[p] ℂ_[p]`,
  `NormedAlgebra ℚᶜᵘⁿ_[p] ℂ_[p]`, `IsScalarTower ℚ_[p] ℚᶜᵘⁿ_[p] ℂ_[p]`;
- `TrustworthyKedlaya.QpCUn.coe_algClEmbd`: the compatibility
  `((QpUn.algClEmbd p x : PadicAlgCl p) : ℂ_[p]) = algebraMap ℚᶜᵘⁿ_[p] ℂ_[p] ↑x`.
-/

@[expose] public section

namespace TrustworthyKedlaya

open scoped NNReal

variable {p : ℕ} [Fact (Nat.Prime p)]

/-! ### `ℚᵘⁿ_[p]` is algebraic over `ℚ_[p]` -/

namespace QpUn

@[simp] theorem algebraMap_QpCUn_apply (x : ℚᵘⁿ_[p]) : algebraMap ℚᵘⁿ_[p] ℚᶜᵘⁿ_[p] x = x := rfl

theorem algebraMap_QpCUn_injective : Function.Injective (algebraMap ℚᵘⁿ_[p] ℚᶜᵘⁿ_[p]) :=
  Subtype.val_injective

/-- Elements of `ℤᵘⁿ_[p]` are integral over `ℤ_[p]`: each lies in a layer `W(𝔽_{p^r})`, which is
a finite `ℤ_[p]`-module. -/
theorem isIntegral_of_mem_OQpUn {a : ℤᶜᵘⁿ_[p]} (ha : a ∈ ℤᵘⁿ_[p]) : IsIntegral ℤ_[p] a := by
  obtain ⟨K, hK, haK⟩ := ha
  have hmem : a ∈ wittSubring p K := (mem_wittSubring_iff p).2 haK
  have h : IsIntegral ℤ_[p] (⟨a, hmem⟩ : wittSubring p K) := Algebra.IsIntegral.isIntegral _
  exact h.algebraMap

theorem isAlgebraic_algebraMap_of_mem_OQpUn {a : ℤᶜᵘⁿ_[p]} (ha : a ∈ ℤᵘⁿ_[p]) :
    IsAlgebraic ℚ_[p] (algebraMap ℤᶜᵘⁿ_[p] ℚᶜᵘⁿ_[p] a) :=
  ((isIntegral_of_mem_OQpUn ha).algebraMap.tower_top (A := ℚ_[p])).isAlgebraic

/-- Every element of `ℚᵘⁿ_[p]` is algebraic over `ℚ_[p]` (as an element of `ℚᶜᵘⁿ_[p]`). -/
theorem isAlgebraic_coe (x : ℚᵘⁿ_[p]) : IsAlgebraic ℚ_[p] (x : ℚᶜᵘⁿ_[p]) := by
  obtain ⟨a, ha, b, hb, hx⟩ := (mem_iff p).1 x.2
  rw [← hx, div_eq_mul_inv]
  exact (isAlgebraic_algebraMap_of_mem_OQpUn ha).mul (isAlgebraic_algebraMap_of_mem_OQpUn hb).inv

/-- **`ℚᵘⁿ_[p]` is an algebraic extension of `ℚ_[p]`.** -/
instance instIsAlgebraic : Algebra.IsAlgebraic ℚ_[p] ℚᵘⁿ_[p] :=
  ⟨fun x => (isAlgebraic_algebraMap_iff algebraMap_QpCUn_injective).1 (isAlgebraic_coe x)⟩

/-! ### The embedding `ℚᵘⁿ_[p] → PadicAlgCl p` -/

/-- A `ℚ_[p]`-embedding of `ℚᵘⁿ_[p]` into the algebraic closure `PadicAlgCl p` of `ℚ_[p]`.
This is the **only choice** made in the whole tower `ℚᵘⁿ_[p] ⊆ ℚᶜᵘⁿ_[p] ⊆ ℂ_[p]`; any two such
embeddings differ by an automorphism of `ℚᵘⁿ_[p]`.

It is deliberately *not* made into an `Algebra ℚᵘⁿ_[p] (PadicAlgCl p)` instance; see the
implementation notes of this file. -/
noncomputable def algClEmbd (p : ℕ) [Fact (Nat.Prime p)] : ℚᵘⁿ_[p] →ₐ[ℚ_[p]] PadicAlgCl p :=
  IsAlgClosed.lift

theorem algClEmbd_injective : Function.Injective (algClEmbd p) :=
  (algClEmbd p : ℚᵘⁿ_[p] →+* PadicAlgCl p).injective

theorem algClEmbd_algebraMap (k : ℚ_[p]) :
    algClEmbd p (algebraMap ℚ_[p] ℚᵘⁿ_[p] k) = algebraMap ℚ_[p] (PadicAlgCl p) k :=
  (algClEmbd p).commutes k

/-- **The embedding `ℚᵘⁿ_[p] → PadicAlgCl p` is isometric**: both the norm of `ℚᵘⁿ_[p]`
(restricted from `ℚᶜᵘⁿ_[p]`) and the norm pulled back from `PadicAlgCl p` are absolute values on
`ℚᵘⁿ_[p]` extending the `p`-adic norm of `ℚ_[p]`, and such an absolute value is unique
(`spectralNorm_unique_field_norm_ext`). -/
theorem norm_algClEmbd (x : ℚᵘⁿ_[p]) : ‖algClEmbd p x‖ = ‖x‖ := by
  let f : AbsoluteValue ℚᵘⁿ_[p] ℝ :=
    { toFun := fun y => ‖algClEmbd p y‖
      map_mul' := fun a b => by simp only [map_mul, norm_mul]
      nonneg' := fun a => norm_nonneg _
      eq_zero' := fun a => by
        simp only [norm_eq_zero]
        exact map_eq_zero_iff _ algClEmbd_injective
      add_le' := fun a b => by
        simp only [map_add]
        exact norm_add_le _ _ }
  let g : AbsoluteValue ℚᵘⁿ_[p] ℝ :=
    { toFun := fun y => ‖y‖
      map_mul' := fun a b => norm_mul a b
      nonneg' := fun a => norm_nonneg _
      eq_zero' := fun a => norm_eq_zero
      add_le' := fun a b => norm_add_le a b }
  have hf : ∀ k : ℚ_[p], f (algebraMap ℚ_[p] ℚᵘⁿ_[p] k) = ‖k‖ := fun k => by
    change ‖algClEmbd p (algebraMap ℚ_[p] ℚᵘⁿ_[p] k)‖ = ‖k‖
    rw [algClEmbd_algebraMap, PadicAlgCl.norm_extends]
  have hg : ∀ k : ℚ_[p], g (algebraMap ℚ_[p] ℚᵘⁿ_[p] k) = ‖k‖ := fun k => by
    change ‖(algebraMap ℚ_[p] ℚᵘⁿ_[p] k : ℚᶜᵘⁿ_[p])‖ = ‖k‖
    exact QpCUn.norm_Qp_embd k
  exact (spectralNorm_unique_field_norm_ext (K := ℚ_[p]) hf x).trans
    (spectralNorm_unique_field_norm_ext (K := ℚ_[p]) hg x).symm

theorem isometry_algClEmbd : Isometry (algClEmbd p) :=
  AddMonoidHomClass.isometry_of_norm _ norm_algClEmbd

/-! ### The image of `ℚᵘⁿ_[p]` in `PadicAlgCl p`

To work with extensions of `ℚᵘⁿ_[p]` *inside* `PadicAlgCl p` (for instance `ℚᵘⁿ_[p](a)` for
some `a : PadicAlgCl p`), use the image `algClRange` of `ℚᵘⁿ_[p]`, an intermediate field of
`PadicAlgCl p / ℚ_[p]`: Mathlib then provides the `Algebra`, `IsScalarTower`, ... instances
automatically, `ℚᵘⁿ_[p](a)` is `(algClRange p)⟮a⟯`, an intermediate field of
`PadicAlgCl p / algClRange p`, and `PadicAlgCl p` is an algebraic closure of `algClRange p`.
The isomorphism `algClEquiv` transports back to the Witt-vector model `ℚᵘⁿ_[p] ⊆ ℚᶜᵘⁿ_[p]`. -/

/-- The image of `ℚᵘⁿ_[p]` in `PadicAlgCl p`, as an intermediate field over `ℚ_[p]`. -/
noncomputable def algClRange (p : ℕ) [Fact (Nat.Prime p)] :
    IntermediateField ℚ_[p] (PadicAlgCl p) :=
  (algClEmbd p).fieldRange

theorem mem_algClRange {y : PadicAlgCl p} : y ∈ algClRange p ↔ ∃ x, algClEmbd p x = y :=
  AlgHom.mem_fieldRange

theorem algClEmbd_mem_algClRange (x : ℚᵘⁿ_[p]) : algClEmbd p x ∈ algClRange p := ⟨x, rfl⟩

/-- `ℚᵘⁿ_[p]` is isomorphic to its image `algClRange p` in `PadicAlgCl p`. -/
noncomputable def algClEquiv (p : ℕ) [Fact (Nat.Prime p)] : ℚᵘⁿ_[p] ≃ₐ[ℚ_[p]] algClRange p :=
  (algClEmbd p).equivFieldRange

@[simp] theorem coe_algClEquiv_apply (x : ℚᵘⁿ_[p]) :
    (algClEquiv p x : PadicAlgCl p) = algClEmbd p x :=
  rfl

theorem algClEmbd_algClEquiv_symm (y : algClRange p) :
    algClEmbd p ((algClEquiv p).symm y) = y := by
  rw [← coe_algClEquiv_apply, AlgEquiv.apply_symm_apply]

/-- `PadicAlgCl p` is algebraic over the image of `ℚᵘⁿ_[p]`. -/
instance : Algebra.IsAlgebraic (algClRange p) (PadicAlgCl p) :=
  Algebra.IsAlgebraic.tower_top (K := ℚ_[p]) (algClRange p)

/-- `PadicAlgCl p` is an algebraic closure of the image of `ℚᵘⁿ_[p]`. -/
instance : IsAlgClosure (algClRange p) (PadicAlgCl p) :=
  ⟨inferInstance, inferInstance⟩

/-! ### The embedding `ℚᵘⁿ_[p] → ℂ_[p]` -/

/-- The embedding `ℚᵘⁿ_[p] → PadicAlgCl p → ℂ_[p]`, as a `ℚ_[p]`-algebra homomorphism. -/
noncomputable def complexEmbd (p : ℕ) [Fact (Nat.Prime p)] : ℚᵘⁿ_[p] →ₐ[ℚ_[p]] ℂ_[p] :=
  (IsScalarTower.toAlgHom ℚ_[p] (PadicAlgCl p) ℂ_[p]).comp (algClEmbd p)

theorem complexEmbd_apply (x : ℚᵘⁿ_[p]) : complexEmbd p x = (algClEmbd p x : ℂ_[p]) := rfl

theorem norm_complexEmbd (x : ℚᵘⁿ_[p]) : ‖complexEmbd p x‖ = ‖x‖ := by
  rw [complexEmbd_apply, PadicComplex.norm_extends, norm_algClEmbd]

theorem isometry_complexEmbd : Isometry (complexEmbd p) :=
  AddMonoidHomClass.isometry_of_norm _ norm_complexEmbd

theorem continuous_complexEmbd : Continuous (complexEmbd p) :=
  isometry_complexEmbd.continuous

end QpUn

/-! ### The embedding `ℚᶜᵘⁿ_[p] → ℂ_[p]`

`ℚᵘⁿ_[p]` is dense in `ℚᶜᵘⁿ_[p]` and `ℂ_[p]` is complete, so the isometric ring homomorphism
`ℚᵘⁿ_[p] → ℂ_[p]` extends uniquely to a continuous ring homomorphism `ℚᶜᵘⁿ_[p] → ℂ_[p]`. -/

namespace QpCUn

theorem isUniformInducing_QpUn_subtype : IsUniformInducing (ℚᵘⁿ_[p]).subtype :=
  isUniformEmbedding_subtype_val.isUniformInducing

theorem isDenseInducing_QpUn_subtype : IsDenseInducing (ℚᵘⁿ_[p]).subtype :=
  isUniformInducing_QpUn_subtype.isDenseInducing (QpUn.denseRange_subtype p)

/-- The continuous extension of `ℚᵘⁿ_[p] → ℂ_[p]` to `ℚᶜᵘⁿ_[p]`, as a ring homomorphism. -/
noncomputable def complexEmbdRingHom (p : ℕ) [Fact (Nat.Prime p)] : ℚᶜᵘⁿ_[p] →+* ℂ_[p] :=
  IsDenseInducing.extendRingHom (i := (ℚᵘⁿ_[p]).subtype)
    (f := (QpUn.complexEmbd p : ℚᵘⁿ_[p] →+* ℂ_[p]))
    isUniformInducing_QpUn_subtype (QpUn.denseRange_subtype p)
    QpUn.isometry_complexEmbd.uniformContinuous

/-- The embedding of `ℚᶜᵘⁿ_[p]` extends the embedding of `ℚᵘⁿ_[p]`. -/
theorem complexEmbdRingHom_coe (x : ℚᵘⁿ_[p]) :
    complexEmbdRingHom p (x : ℚᶜᵘⁿ_[p]) = QpUn.complexEmbd p x :=
  IsDenseInducing.extend_eq isDenseInducing_QpUn_subtype QpUn.continuous_complexEmbd x

theorem uniformContinuous_complexEmbdRingHom : UniformContinuous (complexEmbdRingHom p) :=
  uniformContinuous_uniformly_extend isUniformInducing_QpUn_subtype (QpUn.denseRange_subtype p)
    QpUn.isometry_complexEmbd.uniformContinuous

theorem continuous_complexEmbdRingHom : Continuous (complexEmbdRingHom p) :=
  uniformContinuous_complexEmbdRingHom.continuous

/-- **The embedding `ℚᶜᵘⁿ_[p] → ℂ_[p]` is isometric.** -/
theorem norm_complexEmbdRingHom (x : ℚᶜᵘⁿ_[p]) : ‖complexEmbdRingHom p x‖ = ‖x‖ := by
  refine (QpUn.denseRange_subtype p).induction_on x ?_ ?_
  · exact isClosed_eq (continuous_norm.comp continuous_complexEmbdRingHom) continuous_norm
  · intro a
    change ‖complexEmbdRingHom p (a : ℚᶜᵘⁿ_[p])‖ = ‖(a : ℚᶜᵘⁿ_[p])‖
    rw [complexEmbdRingHom_coe, QpUn.norm_complexEmbd]
    rfl

/-- The embedding `ℚᶜᵘⁿ_[p] → ℂ_[p]` is `ℚ_[p]`-linear. -/
theorem complexEmbdRingHom_algebraMap (k : ℚ_[p]) :
    complexEmbdRingHom p (algebraMap ℚ_[p] ℚᶜᵘⁿ_[p] k) = algebraMap ℚ_[p] ℂ_[p] k := by
  rw [IsScalarTower.algebraMap_apply ℚ_[p] ℚᵘⁿ_[p] ℚᶜᵘⁿ_[p], QpUn.algebraMap_QpCUn_apply,
    complexEmbdRingHom_coe, (QpUn.complexEmbd p).commutes]

/-- The continuous extension of `ℚᵘⁿ_[p] → ℂ_[p]` to `ℚᶜᵘⁿ_[p]`, as a `ℚ_[p]`-algebra
homomorphism. -/
noncomputable def complexEmbd (p : ℕ) [Fact (Nat.Prime p)] : ℚᶜᵘⁿ_[p] →ₐ[ℚ_[p]] ℂ_[p] :=
  { complexEmbdRingHom p with commutes' := complexEmbdRingHom_algebraMap }

theorem complexEmbd_apply (x : ℚᶜᵘⁿ_[p]) : complexEmbd p x = complexEmbdRingHom p x := rfl

theorem complexEmbd_injective : Function.Injective (complexEmbd p) :=
  (complexEmbd p : ℚᶜᵘⁿ_[p] →+* ℂ_[p]).injective

theorem norm_complexEmbd (x : ℚᶜᵘⁿ_[p]) : ‖complexEmbd p x‖ = ‖x‖ :=
  norm_complexEmbdRingHom x

theorem isometry_complexEmbd : Isometry (complexEmbd p) :=
  AddMonoidHomClass.isometry_of_norm _ norm_complexEmbd

theorem continuous_complexEmbd : Continuous (complexEmbd p) :=
  continuous_complexEmbdRingHom

/-! ### `ℂ_[p]` as a `ℚᶜᵘⁿ_[p]`-algebra -/

/-- `ℂ_[p]` as a `ℚᶜᵘⁿ_[p]`-algebra, via `complexEmbd`. -/
noncomputable instance : Algebra ℚᶜᵘⁿ_[p] ℂ_[p] := (complexEmbd p).toAlgebra

theorem algebraMap_complex_apply (x : ℚᶜᵘⁿ_[p]) :
    algebraMap ℚᶜᵘⁿ_[p] ℂ_[p] x = complexEmbd p x :=
  rfl

theorem norm_algebraMap_complex (x : ℚᶜᵘⁿ_[p]) : ‖algebraMap ℚᶜᵘⁿ_[p] ℂ_[p] x‖ = ‖x‖ :=
  norm_complexEmbd x

theorem isometry_algebraMap_complex : Isometry (algebraMap ℚᶜᵘⁿ_[p] ℂ_[p]) :=
  isometry_complexEmbd

theorem continuous_algebraMap_complex : Continuous (algebraMap ℚᶜᵘⁿ_[p] ℂ_[p]) :=
  continuous_complexEmbd

/-- `ℂ_[p]` is a normed `ℚᶜᵘⁿ_[p]`-algebra. -/
noncomputable instance : NormedAlgebra ℚᶜᵘⁿ_[p] ℂ_[p] where
  norm_smul_le r x := by rw [Algebra.smul_def, norm_mul, norm_algebraMap_complex]

instance : IsScalarTower ℚ_[p] ℚᶜᵘⁿ_[p] ℂ_[p] :=
  IsScalarTower.of_algebraMap_eq fun k => (complexEmbdRingHom_algebraMap k).symm

/-! ### `simp` normal forms

The image in `ℂ_[p]` of `x : ℚᵘⁿ_[p]`, whichever way it is written, is normalised to
`algebraMap ℚᶜᵘⁿ_[p] ℂ_[p] ↑x`.  (The instance `Algebra ℚᵘⁿ_[p] ℂ_[p]` is the restriction of
`Algebra ℚᶜᵘⁿ_[p] ℂ_[p]`, provided by Mathlib, and `IsScalarTower ℚᵘⁿ_[p] ℚᶜᵘⁿ_[p] ℂ_[p]` holds
definitionally.) -/

@[simp] theorem algebraMap_complex_QpUn_apply (x : ℚᵘⁿ_[p]) :
    algebraMap ℚᵘⁿ_[p] ℂ_[p] x = algebraMap ℚᶜᵘⁿ_[p] ℂ_[p] (x : ℚᶜᵘⁿ_[p]) :=
  rfl

/-- **The two embeddings of `ℚᵘⁿ_[p]` into `ℂ_[p]` agree**: through `PadicAlgCl p` and through
`ℚᶜᵘⁿ_[p]`. -/
@[simp] theorem coe_algClEmbd (x : ℚᵘⁿ_[p]) :
    ((QpUn.algClEmbd p x : PadicAlgCl p) : ℂ_[p]) = algebraMap ℚᶜᵘⁿ_[p] ℂ_[p] (x : ℚᶜᵘⁿ_[p]) :=
  (complexEmbdRingHom_coe x).symm

@[simp] theorem QpUn_complexEmbd_apply_eq_algebraMap (x : ℚᵘⁿ_[p]) :
    QpUn.complexEmbd p x = algebraMap ℚᶜᵘⁿ_[p] ℂ_[p] (x : ℚᶜᵘⁿ_[p]) :=
  (complexEmbdRingHom_coe x).symm

@[simp] theorem complexEmbd_apply_eq_algebraMap (x : ℚᶜᵘⁿ_[p]) :
    complexEmbd p x = algebraMap ℚᶜᵘⁿ_[p] ℂ_[p] x :=
  rfl

@[simp] theorem complexEmbdRingHom_apply_eq_algebraMap (x : ℚᶜᵘⁿ_[p]) :
    complexEmbdRingHom p x = algebraMap ℚᶜᵘⁿ_[p] ℂ_[p] x :=
  rfl

@[simp] theorem algebraMap_complex_algebraMap_Qp (k : ℚ_[p]) :
    algebraMap ℚᶜᵘⁿ_[p] ℂ_[p] (algebraMap ℚ_[p] ℚᶜᵘⁿ_[p] k) = algebraMap ℚ_[p] ℂ_[p] k :=
  complexEmbdRingHom_algebraMap k

instance : IsScalarTower ℚ_[p] ℚᵘⁿ_[p] ℂ_[p] :=
  IsScalarTower.of_algebraMap_eq fun k => (complexEmbdRingHom_algebraMap k).symm

/-- `IsScalarTower ℚᵘⁿ_[p] ℚᶜᵘⁿ_[p] ℂ_[p]` is found by Mathlib, since `Algebra ℚᵘⁿ_[p] ℂ_[p]` is
the restriction of `Algebra ℚᶜᵘⁿ_[p] ℂ_[p]`. -/
example : IsScalarTower ℚᵘⁿ_[p] ℚᶜᵘⁿ_[p] ℂ_[p] := inferInstance

end QpCUn

namespace QpUn

/-- An element of the image `algClRange p` of `ℚᵘⁿ_[p]` in `PadicAlgCl p`, viewed in `ℂ_[p]`,
is the image of the corresponding element of `ℚᵘⁿ_[p] ⊆ ℚᶜᵘⁿ_[p]`. -/
theorem coe_coe_algClRange (y : algClRange p) :
    ((y : PadicAlgCl p) : ℂ_[p]) =
      algebraMap ℚᶜᵘⁿ_[p] ℂ_[p] (((algClEquiv p).symm y : ℚᵘⁿ_[p]) : ℚᶜᵘⁿ_[p]) := by
  rw [← algClEmbd_algClEquiv_symm y, QpCUn.coe_algClEmbd]

end QpUn

end TrustworthyKedlaya
