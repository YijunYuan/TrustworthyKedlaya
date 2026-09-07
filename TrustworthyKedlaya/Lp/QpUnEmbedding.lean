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

`ℚ_[p] ⊆ ℚᵘⁿ_[p] ⊆ ℚᶜᵘⁿ_[p] ⊆ ℂ_[p]` and `ℚ_[p] ⊆ ℚᵘⁿ_[p] ⊆ PadicAlgCl p ⊆ ℂ_[p]`

inside `ℂ_[p]`, without reference to `𝕃_[p]`.  Everything is derived from a **single choice**, a
`ℚ_[p]`-embedding `QpUn.algClEmbd : ℚᵘⁿ_[p] →ₐ[ℚ_[p]] PadicAlgCl p` (which exists since
`ℚᵘⁿ_[p]` is algebraic over `ℚ_[p]` and `PadicAlgCl p` is algebraically closed; it is unique up
to `Gal(ℚᵘⁿ_[p]/ℚ_[p])`):

- `ℚᵘⁿ_[p] → PadicAlgCl p` is `QpUn.algClEmbd`.  It is isometric, by the uniqueness of the
  extension of the `p`-adic norm to the algebraic extension `ℚᵘⁿ_[p]` of the complete field
  `ℚ_[p]` (`spectralNorm_unique_field_norm_ext`).  It is installed as the instance
  `Algebra ℚᵘⁿ_[p] (PadicAlgCl p)` and as the coercion `(x : PadicAlgCl p)`; in particular
  `PadicAlgCl p` is an algebraic closure of `ℚᵘⁿ_[p]` (`IsAlgClosure ℚᵘⁿ_[p] (PadicAlgCl p)`),
  and `ℚᵘⁿ_[p](a)` for `a : PadicAlgCl p` is simply `ℚᵘⁿ_[p]⟮a⟯`;
- `ℚᵘⁿ_[p] → ℂ_[p]` is its composite with the completion map `PadicAlgCl p → ℂ_[p]`.  This is
  the instance `Algebra ℚᵘⁿ_[p] ℂ_[p]` provided by Mathlib's `UniformSpace.Completion.algebra`
  (so `IsScalarTower ℚᵘⁿ_[p] (PadicAlgCl p) ℂ_[p]` and `IsScalarTower ℚ_[p] ℚᵘⁿ_[p] ℂ_[p]` are
  automatic), and the chained coercion `((x : PadicAlgCl p) : ℂ_[p])`;
- `ℚᶜᵘⁿ_[p] → ℂ_[p]` (`QpCUn.complexEmbd`) is the continuous extension of the previous map
  along the dense inclusion `ℚᵘⁿ_[p] ⊆ ℚᶜᵘⁿ_[p]` (`IsDenseInducing.extendRingHom`), installed
  as the instance `Algebra ℚᶜᵘⁿ_[p] ℂ_[p]`.

The compatibility of the two ways of embedding `ℚᵘⁿ_[p]` into `ℂ_[p]` (through `ℚᶜᵘⁿ_[p]` and
through `PadicAlgCl p`) is the instance `IsScalarTower ℚᵘⁿ_[p] ℚᶜᵘⁿ_[p] ℂ_[p]`, which is
`IsDenseInducing.extend_eq`.

## Implementation notes

Since `ℚᵘⁿ_[p]` is a type synonym and not a subtype of `ℚᶜᵘⁿ_[p]` (see the implementation notes
of `TrustworthyKedlaya.Lp.QpUn`), no action of `ℚᵘⁿ_[p]` is derived automatically from an action
of `ℚᶜᵘⁿ_[p]`; the `ℚᵘⁿ_[p]`-algebra structures on `PadicAlgCl p` and `ℂ_[p]` are installed
here, exactly once each, through `PadicAlgCl p`.

The chosen maps `ℚᵘⁿ_[p] → PadicAlgCl p` and `ℚᶜᵘⁿ_[p] → ℂ_[p]` are exposed through `Algebra`
instances and `algebraMap`.  The first one, being *the* embedding fixed once and for all, is
also a coercion (`QpUn.toAlgCl`, displayed `↑x`), as `ℚ_[p] → PadicAlgCl p` is in Mathlib; the
second one is not (it would chain with `ℂ_[p] → 𝕃_[p]` and produce a second name for the
structure map `ℚᶜᵘⁿ_[p] → 𝕃_[p]`).  The `simp` normal form of the image in `ℂ_[p]` of
`x : ℚᵘⁿ_[p]`, whichever way it is written, is `((x : PadicAlgCl p) : ℂ_[p])`.

## Main declarations

- `TrustworthyKedlaya.QpUn.instIsAlgebraic`: `ℚᵘⁿ_[p]` is algebraic over `ℚ_[p]`;
- `TrustworthyKedlaya.QpUn.algClEmbd`: the embedding `ℚᵘⁿ_[p] →ₐ[ℚ_[p]] PadicAlgCl p`, the
  coercion `QpUn.toAlgCl` and the instances `Algebra ℚᵘⁿ_[p] (PadicAlgCl p)`,
  `NormedAlgebra ℚᵘⁿ_[p] (PadicAlgCl p)`, `IsAlgClosure ℚᵘⁿ_[p] (PadicAlgCl p)`, with
  `QpUn.norm_toAlgCl` (it is isometric);
- `TrustworthyKedlaya.QpCUn.complexEmbd`: the embedding `ℚᶜᵘⁿ_[p] →ₐ[ℚ_[p]] ℂ_[p]`, with
  `QpCUn.norm_complexEmbd` (it is isometric), and the instances `Algebra ℚᶜᵘⁿ_[p] ℂ_[p]`,
  `NormedAlgebra ℚᶜᵘⁿ_[p] ℂ_[p]`, `IsScalarTower ℚ_[p] ℚᶜᵘⁿ_[p] ℂ_[p]`,
  `IsScalarTower ℚᵘⁿ_[p] ℚᶜᵘⁿ_[p] ℂ_[p]`.
-/

@[expose] public section

namespace TrustworthyKedlaya

open scoped NNReal

variable {p : ℕ} [Fact (Nat.Prime p)]

/-! ### `ℚᵘⁿ_[p]` is algebraic over `ℚ_[p]` -/

namespace QpUn

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
  obtain ⟨a, ha, b, hb, hx⟩ := (mem_iff p).1 (coe_mem x)
  rw [← hx, div_eq_mul_inv]
  exact (isAlgebraic_algebraMap_of_mem_OQpUn ha).mul (isAlgebraic_algebraMap_of_mem_OQpUn hb).inv

/-- **`ℚᵘⁿ_[p]` is an algebraic extension of `ℚ_[p]`.** -/
instance instIsAlgebraic : Algebra.IsAlgebraic ℚ_[p] ℚᵘⁿ_[p] :=
  ⟨fun x => (isAlgebraic_algebraMap_iff algebraMap_QpCUn_injective).1 (isAlgebraic_coe x)⟩

/-! ### The embedding `ℚᵘⁿ_[p] → PadicAlgCl p` -/

/-- A `ℚ_[p]`-embedding of `ℚᵘⁿ_[p]` into the algebraic closure `PadicAlgCl p` of `ℚ_[p]`.
This is the **only choice** made in the whole tower `ℚᵘⁿ_[p] ⊆ ℚᶜᵘⁿ_[p] ⊆ ℂ_[p]`; any two such
embeddings differ by an automorphism of `ℚᵘⁿ_[p]`.  It is installed below as the
`Algebra ℚᵘⁿ_[p] (PadicAlgCl p)` instance and as the coercion `(x : PadicAlgCl p)`. -/
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
    change ‖algebraMap ℚ_[p] ℚᵘⁿ_[p] k‖ = ‖k‖
    rw [← norm_coe, coe_algebraMap_Qp]
    exact QpCUn.norm_Qp_embd k
  exact (spectralNorm_unique_field_norm_ext (K := ℚ_[p]) hf x).trans
    (spectralNorm_unique_field_norm_ext (K := ℚ_[p]) hg x).symm

theorem isometry_algClEmbd : Isometry (algClEmbd p) :=
  AddMonoidHomClass.isometry_of_norm _ norm_algClEmbd

/-! ### `PadicAlgCl p` as a `ℚᵘⁿ_[p]`-algebra, and the coercion `ℚᵘⁿ_[p] → PadicAlgCl p` -/

/-- `PadicAlgCl p` as a `ℚᵘⁿ_[p]`-algebra, through `algClEmbd`. -/
noncomputable instance : Algebra ℚᵘⁿ_[p] (PadicAlgCl p) := (algClEmbd p).toAlgebra

/-- The embedding `ℚᵘⁿ_[p] → PadicAlgCl p` as a plain function, registered as a coercion.  It is
definitionally `algebraMap ℚᵘⁿ_[p] (PadicAlgCl p)` and `algClEmbd p`; the `simp` normal form is
the coercion `↑x`. -/
@[coe] noncomputable def toAlgCl (x : ℚᵘⁿ_[p]) : PadicAlgCl p :=
  algebraMap ℚᵘⁿ_[p] (PadicAlgCl p) x

noncomputable instance : Coe ℚᵘⁿ_[p] (PadicAlgCl p) := ⟨toAlgCl⟩

@[simp] theorem algebraMap_algCl_apply_eq_coe (x : ℚᵘⁿ_[p]) :
    algebraMap ℚᵘⁿ_[p] (PadicAlgCl p) x = (x : PadicAlgCl p) :=
  rfl

@[simp] theorem algClEmbd_apply_eq_coe (x : ℚᵘⁿ_[p]) : algClEmbd p x = (x : PadicAlgCl p) := rfl

theorem toAlgCl_injective : Function.Injective ((↑) : ℚᵘⁿ_[p] → PadicAlgCl p) :=
  algClEmbd_injective

@[simp, norm_cast] theorem toAlgCl_inj {x y : ℚᵘⁿ_[p]} :
    (x : PadicAlgCl p) = y ↔ x = y :=
  toAlgCl_injective.eq_iff

@[simp, norm_cast] theorem toAlgCl_zero : ((0 : ℚᵘⁿ_[p]) : PadicAlgCl p) = 0 :=
  map_zero (algClEmbd p)

@[simp, norm_cast] theorem toAlgCl_one : ((1 : ℚᵘⁿ_[p]) : PadicAlgCl p) = 1 :=
  map_one (algClEmbd p)

@[simp, norm_cast] theorem toAlgCl_add (x y : ℚᵘⁿ_[p]) :
    ((x + y : ℚᵘⁿ_[p]) : PadicAlgCl p) = x + y :=
  map_add (algClEmbd p) x y

@[simp, norm_cast] theorem toAlgCl_mul (x y : ℚᵘⁿ_[p]) :
    ((x * y : ℚᵘⁿ_[p]) : PadicAlgCl p) = x * y :=
  map_mul (algClEmbd p) x y

@[simp, norm_cast] theorem toAlgCl_neg (x : ℚᵘⁿ_[p]) : ((-x : ℚᵘⁿ_[p]) : PadicAlgCl p) = -x :=
  map_neg (algClEmbd p) x

@[simp, norm_cast] theorem toAlgCl_sub (x y : ℚᵘⁿ_[p]) :
    ((x - y : ℚᵘⁿ_[p]) : PadicAlgCl p) = x - y :=
  map_sub (algClEmbd p) x y

@[simp, norm_cast] theorem toAlgCl_inv (x : ℚᵘⁿ_[p]) :
    ((x⁻¹ : ℚᵘⁿ_[p]) : PadicAlgCl p) = (x : PadicAlgCl p)⁻¹ :=
  map_inv₀ (algClEmbd p) x

@[simp, norm_cast] theorem toAlgCl_div (x y : ℚᵘⁿ_[p]) :
    ((x / y : ℚᵘⁿ_[p]) : PadicAlgCl p) = x / y :=
  map_div₀ (algClEmbd p) x y

@[simp, norm_cast] theorem toAlgCl_pow (x : ℚᵘⁿ_[p]) (n : ℕ) :
    ((x ^ n : ℚᵘⁿ_[p]) : PadicAlgCl p) = (x : PadicAlgCl p) ^ n :=
  map_pow (algClEmbd p) x n

@[simp, norm_cast] theorem toAlgCl_natCast (n : ℕ) : ((n : ℚᵘⁿ_[p]) : PadicAlgCl p) = n :=
  map_natCast (algClEmbd p) n

@[simp, norm_cast] theorem toAlgCl_intCast (n : ℤ) : ((n : ℚᵘⁿ_[p]) : PadicAlgCl p) = n :=
  map_intCast (algClEmbd p) n

@[simp, norm_cast] theorem toAlgCl_eq_zero {x : ℚᵘⁿ_[p]} : (x : PadicAlgCl p) = 0 ↔ x = 0 :=
  map_eq_zero_iff _ algClEmbd_injective

/-- On `ℚ_[p] ⊆ ℚᵘⁿ_[p]` the coercion is the structure map `ℚ_[p] → PadicAlgCl p`. -/
@[simp] theorem toAlgCl_algebraMap (k : ℚ_[p]) :
    ((algebraMap ℚ_[p] ℚᵘⁿ_[p] k : ℚᵘⁿ_[p]) : PadicAlgCl p) = algebraMap ℚ_[p] (PadicAlgCl p) k :=
  algClEmbd_algebraMap k

instance : IsScalarTower ℚ_[p] ℚᵘⁿ_[p] (PadicAlgCl p) :=
  IsScalarTower.of_algebraMap_eq fun k => (algClEmbd_algebraMap k).symm

/-- `PadicAlgCl p` is algebraic over `ℚᵘⁿ_[p]`. -/
instance : Algebra.IsAlgebraic ℚᵘⁿ_[p] (PadicAlgCl p) :=
  Algebra.IsAlgebraic.tower_top (K := ℚ_[p]) ℚᵘⁿ_[p]

/-- **`PadicAlgCl p` is an algebraic closure of `ℚᵘⁿ_[p]`.** -/
instance : IsAlgClosure ℚᵘⁿ_[p] (PadicAlgCl p) := ⟨inferInstance, inferInstance⟩

/-- **The coercion `ℚᵘⁿ_[p] → PadicAlgCl p` is isometric.** -/
@[simp, norm_cast] theorem norm_toAlgCl (x : ℚᵘⁿ_[p]) : ‖(x : PadicAlgCl p)‖ = ‖x‖ :=
  norm_algClEmbd x

@[simp, norm_cast] theorem nnnorm_toAlgCl (x : ℚᵘⁿ_[p]) : ‖(x : PadicAlgCl p)‖₊ = ‖x‖₊ := by
  ext
  exact norm_toAlgCl x

theorem isometry_toAlgCl : Isometry ((↑) : ℚᵘⁿ_[p] → PadicAlgCl p) := isometry_algClEmbd

theorem continuous_toAlgCl : Continuous ((↑) : ℚᵘⁿ_[p] → PadicAlgCl p) :=
  isometry_toAlgCl.continuous

/-- `PadicAlgCl p` is a normed `ℚᵘⁿ_[p]`-algebra.  (This is what makes Mathlib's
`UniformSpace.Completion.algebra` provide the `Algebra ℚᵘⁿ_[p] ℂ_[p]` instance below.) -/
noncomputable instance : NormedAlgebra ℚᵘⁿ_[p] (PadicAlgCl p) where
  norm_smul_le r x := by
    rw [Algebra.smul_def, norm_mul, algebraMap_algCl_apply_eq_coe, norm_toAlgCl]

/-! ### The embedding `ℚᵘⁿ_[p] → ℂ_[p]`

The `Algebra ℚᵘⁿ_[p] ℂ_[p]` instance is `UniformSpace.Completion.algebra`, i.e. the composite
`ℚᵘⁿ_[p] → PadicAlgCl p → ℂ_[p]`, and `(x : ℂ_[p])` elaborates to `((x : PadicAlgCl p) : ℂ_[p])`
by chaining the two coercions.  `IsScalarTower ℚᵘⁿ_[p] (PadicAlgCl p) ℂ_[p]` and
`IsScalarTower ℚ_[p] ℚᵘⁿ_[p] ℂ_[p]` are likewise provided by Mathlib. -/

example : IsScalarTower ℚᵘⁿ_[p] (PadicAlgCl p) ℂ_[p] := inferInstance
example : IsScalarTower ℚ_[p] ℚᵘⁿ_[p] ℂ_[p] := inferInstance

/-- `simp` normal form: the structure map `ℚᵘⁿ_[p] → ℂ_[p]` is the chained coercion. -/
@[simp] theorem algebraMap_complex_apply_eq_coe (x : ℚᵘⁿ_[p]) :
    algebraMap ℚᵘⁿ_[p] ℂ_[p] x = ((x : PadicAlgCl p) : ℂ_[p]) :=
  rfl

theorem norm_algebraMap_complex (x : ℚᵘⁿ_[p]) : ‖algebraMap ℚᵘⁿ_[p] ℂ_[p] x‖ = ‖x‖ := by
  rw [algebraMap_complex_apply_eq_coe, PadicComplex.norm_extends, norm_toAlgCl]

theorem isometry_algebraMap_complex : Isometry (algebraMap ℚᵘⁿ_[p] ℂ_[p]) :=
  AddMonoidHomClass.isometry_of_norm _ norm_algebraMap_complex

theorem continuous_algebraMap_complex : Continuous (algebraMap ℚᵘⁿ_[p] ℂ_[p]) :=
  isometry_algebraMap_complex.continuous

end QpUn

/-! ### The embedding `ℚᶜᵘⁿ_[p] → ℂ_[p]`

`ℚᵘⁿ_[p]` is dense in `ℚᶜᵘⁿ_[p]` and `ℂ_[p]` is complete, so the isometric ring homomorphism
`ℚᵘⁿ_[p] → ℂ_[p]` extends uniquely to a continuous ring homomorphism `ℚᶜᵘⁿ_[p] → ℂ_[p]`. -/

namespace QpCUn

theorem isDenseInducing_QpUn_algebraMap : IsDenseInducing (algebraMap ℚᵘⁿ_[p] ℚᶜᵘⁿ_[p]) :=
  (QpUn.isUniformInducing_algebraMap p).isDenseInducing (QpUn.denseRange_algebraMap p)

/-- The continuous extension of `ℚᵘⁿ_[p] → ℂ_[p]` to `ℚᶜᵘⁿ_[p]`, as a ring homomorphism. -/
noncomputable def complexEmbdRingHom (p : ℕ) [Fact (Nat.Prime p)] : ℚᶜᵘⁿ_[p] →+* ℂ_[p] :=
  IsDenseInducing.extendRingHom (i := algebraMap ℚᵘⁿ_[p] ℚᶜᵘⁿ_[p])
    (f := algebraMap ℚᵘⁿ_[p] ℂ_[p])
    (QpUn.isUniformInducing_algebraMap p) (QpUn.denseRange_algebraMap p)
    QpUn.isometry_algebraMap_complex.uniformContinuous

/-- The embedding of `ℚᶜᵘⁿ_[p]` extends the embedding of `ℚᵘⁿ_[p]`. -/
theorem complexEmbdRingHom_coe (x : ℚᵘⁿ_[p]) :
    complexEmbdRingHom p (x : ℚᶜᵘⁿ_[p]) = ((x : PadicAlgCl p) : ℂ_[p]) :=
  IsDenseInducing.extend_eq isDenseInducing_QpUn_algebraMap QpUn.continuous_algebraMap_complex x

theorem uniformContinuous_complexEmbdRingHom : UniformContinuous (complexEmbdRingHom p) :=
  uniformContinuous_uniformly_extend (QpUn.isUniformInducing_algebraMap p)
    (QpUn.denseRange_algebraMap p) QpUn.isometry_algebraMap_complex.uniformContinuous

theorem continuous_complexEmbdRingHom : Continuous (complexEmbdRingHom p) :=
  uniformContinuous_complexEmbdRingHom.continuous

/-- **The embedding `ℚᶜᵘⁿ_[p] → ℂ_[p]` is isometric.** -/
theorem norm_complexEmbdRingHom (x : ℚᶜᵘⁿ_[p]) : ‖complexEmbdRingHom p x‖ = ‖x‖ := by
  refine (QpUn.denseRange_algebraMap p).induction_on x ?_ ?_
  · exact isClosed_eq (continuous_norm.comp continuous_complexEmbdRingHom) continuous_norm
  · intro a
    rw [QpUn.algebraMap_QpCUn_apply, complexEmbdRingHom_coe, PadicComplex.norm_extends,
      QpUn.norm_toAlgCl, QpUn.norm_coe]

/-- The embedding `ℚᶜᵘⁿ_[p] → ℂ_[p]` is `ℚ_[p]`-linear. -/
theorem complexEmbdRingHom_algebraMap (k : ℚ_[p]) :
    complexEmbdRingHom p (algebraMap ℚ_[p] ℚᶜᵘⁿ_[p] k) = algebraMap ℚ_[p] ℂ_[p] k := by
  rw [IsScalarTower.algebraMap_apply ℚ_[p] ℚᵘⁿ_[p] ℚᶜᵘⁿ_[p], QpUn.algebraMap_QpCUn_apply,
    complexEmbdRingHom_coe, QpUn.toAlgCl_algebraMap, PadicComplex.coe_eq,
    ← IsScalarTower.algebraMap_apply]

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

/-- **The two embeddings of `ℚᵘⁿ_[p]` into `ℂ_[p]` agree**: through `ℚᶜᵘⁿ_[p]` and through
`PadicAlgCl p`. -/
instance : IsScalarTower ℚᵘⁿ_[p] ℚᶜᵘⁿ_[p] ℂ_[p] :=
  IsScalarTower.of_algebraMap_eq fun x => (complexEmbdRingHom_coe x).symm

/-! ### `simp` normal forms

The image in `ℂ_[p]` of `x : ℚᵘⁿ_[p]`, whichever way it is written, is normalised to the chained
coercion `((x : PadicAlgCl p) : ℂ_[p])`. -/

/-- **The two embeddings of `ℚᵘⁿ_[p]` into `ℂ_[p]` agree**, as a `simp` lemma. -/
@[simp] theorem algebraMap_complex_coe (x : ℚᵘⁿ_[p]) :
    algebraMap ℚᶜᵘⁿ_[p] ℂ_[p] (x : ℚᶜᵘⁿ_[p]) = ((x : PadicAlgCl p) : ℂ_[p]) :=
  complexEmbdRingHom_coe x

@[simp] theorem complexEmbd_apply_eq_algebraMap (x : ℚᶜᵘⁿ_[p]) :
    complexEmbd p x = algebraMap ℚᶜᵘⁿ_[p] ℂ_[p] x :=
  rfl

@[simp] theorem complexEmbdRingHom_apply_eq_algebraMap (x : ℚᶜᵘⁿ_[p]) :
    complexEmbdRingHom p x = algebraMap ℚᶜᵘⁿ_[p] ℂ_[p] x :=
  rfl

@[simp] theorem algebraMap_complex_algebraMap_Qp (k : ℚ_[p]) :
    algebraMap ℚᶜᵘⁿ_[p] ℂ_[p] (algebraMap ℚ_[p] ℚᶜᵘⁿ_[p] k) = algebraMap ℚ_[p] ℂ_[p] k :=
  complexEmbdRingHom_algebraMap k

end QpCUn

end TrustworthyKedlaya
