/-
Copyright (c) 2026 Shanwen Wang, Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import TrustworthyKedlaya.FiniteImage
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# The slice span of a family of twist-periodic functions is finite-dimensional

The slice-span decomposition (blueprint `lem:up-slice-span`) writes a UP series
`x` presented on `S_{a,b,c}` as a finite sum `∑ λ_j x_j` with `λ_j` supported in
`(1/a)·ℤ_{≥ -b}` and `x_j` UP with support in `(1/a)(T_c ∪ {0})`.  The engine is the
*span step*, proved here: the width-`a` slice functions `f_m` (`m ≥ -b`), all
`(M, N)`-periodic at level `c`, span a finite-dimensional space of functions on the
level set — because a periodic function's values on the level set are pinned by its
values at the finitely many expansions confined to the digit box
`Finset.range ((c+1)(M+N))` (`exists_confined_rep_forall`, whose confined
representative is function-independent).  Hence finitely many slices `f_{m_1}, …,
f_{m_r}` suffice to express every `f_m` on the level set as an `𝔽̄_p`-linear
combination (`exists_finite_slice_span`).

The level set here always contains `0 = -fracVal 0`, so no separate treatment of
the exponent `0` is needed.

## References

- K. S. Kedlaya, *The algebraic closure of the power series field in positive
  characteristic*, Proc. Amer. Math. Soc. 129 (2001) [Ked01a], proof of Theorem 8.
-/

@[expose] public section

namespace TrustworthyKedlaya.UP

variable {p : ℕ} [hp : Fact (Nat.Prime p)]

/-- Pointwise finite sums of `(M, N)`-periodic functions at level `c` are
`(M, N)`-periodic at level `c` (twist sequences are computed by evaluation, so they
are termwise additive). -/
theorem isTwistPeriodic_finset_sum {ι : Type*} (s : Finset ι) {F : ι → ℚ → 𝔽ᵃ_[p]}
    {c : ℕ} {M N : ℕ+} (hF : ∀ i ∈ s, IsTwistPeriodic p (F i) c M N) :
    IsTwistPeriodic p (fun z => ∑ i ∈ s, F i z) c M N := by
  intro j dig hj hd hs n hn
  have hsum : ∀ n', twistSeq p (fun z => ∑ i ∈ s, F i z) j dig n'
      = ∑ i ∈ s, twistSeq p (F i) j dig n' := fun n' => rfl
  rw [hsum, hsum]
  exact Finset.sum_congr rfl fun i hi => hF i hi j dig hj hd hs n hn

/-- Two `(M, N)`-periodic functions at level `c` agreeing at all expansions confined
to the digit box `Finset.range ((c+1)(M+N))` agree at every canonical expansion of
digit sum `≤ c`: the confined representative of `exists_confined_rep_forall` is the
same for both functions. -/
theorem IsTwistPeriodic.eq_on_levelSet_of_eq_on_confined {f g : ℚ → 𝔽ᵃ_[p]} {c : ℕ}
    {M N : ℕ+} (hf : IsTwistPeriodic p f c M N) (hg : IsTwistPeriodic p g c M N)
    (hfg : ∀ e' : ℕ →₀ ℕ, (∀ i, e' i < p) →
      e'.support ⊆ Finset.range ((c + 1) * ((M : ℕ) + N)) →
      f (-fracVal p e') = g (-fracVal p e'))
    {e : ℕ →₀ ℕ} (he : ∀ i, e i < p) (hsum : (e.sum fun _ v => v) ≤ c) :
    f (-fracVal p e) = g (-fracVal p e) := by
  obtain ⟨e', he', hsum', hbox, hval⟩ := exists_confined_rep_forall c M N he hsum
  rw [← hval f hf, ← hval g hg]
  exact hfg e' he' hbox

/-- **Finite spanning family for the slices** (blueprint `lem:up-slice-span`, span
step): given a family of `(M, N)`-periodic functions at level `c` indexed by the
integers `m ≥ -b`, finitely many members `F (ms 1), …, F (ms r)` with `ms i ≥ -b`
span the family on the level set: every `F m` (`m ≥ -b`) agrees at every canonical
expansion of digit sum `≤ c` (including `0`, the empty expansion) with an
`𝔽̄_p`-linear combination of them, with coefficients `K m` independent of the
expansion. -/
theorem exists_finite_slice_span {b c : ℕ} {M N : ℕ+} (F : ℤ → ℚ → 𝔽ᵃ_[p])
    (hF : ∀ m : ℤ, -(b : ℤ) ≤ m → IsTwistPeriodic p (F m) c M N) :
    ∃ (r : ℕ) (ms : Fin r → ℤ) (K : ℤ → Fin r → 𝔽ᵃ_[p]),
      (∀ i, -(b : ℤ) ≤ ms i) ∧
      ∀ m : ℤ, -(b : ℤ) ≤ m → ∀ e : ℕ →₀ ℕ, (∀ i, e i < p) →
        (e.sum fun _ v => v) ≤ c →
        F m (-fracVal p e) = ∑ i, K m i * F (ms i) (-fracVal p e) := by
  classical
  have hConfFin := finite_neg_fracVal_confined p ((c + 1) * ((M : ℕ) + N))
  set Conf : Finset ℚ := hConfFin.toFinset with hConf
  -- The evaluation of each slice at the confined points.
  set Φ : ℤ → (↥Conf → 𝔽ᵃ_[p]) := fun m z => F m (z : ℚ) with hΦ
  set D : Set ℤ := {m : ℤ | -(b : ℤ) ≤ m} with hD
  -- The span of the evaluations is finitely generated (the ambient space is a
  -- finite-dimensional function space), hence spanned by finitely many members
  -- of the family.
  have hVfg : (Submodule.span (𝔽ᵃ_[p]) (Φ '' D)).FG :=
    Module.Finite.iff_fg.mp inferInstance
  obtain ⟨S, hSspan⟩ := hVfg
  have hSsub : ∀ v ∈ S, ∃ Tv : Finset (↥Conf → 𝔽ᵃ_[p]), ↑Tv ⊆ Φ '' D ∧
      v ∈ Submodule.span (𝔽ᵃ_[p]) (Tv : Set (↥Conf → 𝔽ᵃ_[p])) := by
    intro v hv
    exact Submodule.mem_span_finite_of_mem_span (hSspan ▸ Submodule.subset_span hv)
  choose Tv hTvsub hTvmem using hSsub
  set T : Finset (↥Conf → 𝔽ᵃ_[p]) := S.attach.biUnion (fun v => Tv v.1 v.2) with hT
  have hTsub : ↑T ⊆ Φ '' D := by
    intro t ht
    obtain ⟨v, _, hvt⟩ := Finset.mem_biUnion.mp ht
    exact hTvsub v.1 v.2 hvt
  have hTspan : Submodule.span (𝔽ᵃ_[p]) (Φ '' D)
      ≤ Submodule.span (𝔽ᵃ_[p]) (T : Set (↥Conf → 𝔽ᵃ_[p])) := by
    rw [← hSspan, Submodule.span_le]
    intro v hv
    have hsub : (Tv v hv : Set (↥Conf → 𝔽ᵃ_[p])) ⊆ (T : Set (↥Conf → 𝔽ᵃ_[p])) := by
      intro t ht
      exact Finset.mem_coe.mpr
        (Finset.mem_biUnion.mpr ⟨⟨v, hv⟩, S.mem_attach _, Finset.mem_coe.mp ht⟩)
    exact Submodule.span_mono hsub (hTvmem v hv)
  -- Choose index preimages for the finitely many spanning evaluations.
  have hTpre : ∀ t ∈ T, ∃ m : ℤ, -(b : ℤ) ≤ m ∧ Φ m = t := by
    intro t ht
    obtain ⟨m, hm, hmt⟩ := hTsub ht
    exact ⟨m, hm, hmt⟩
  choose pre hpreD hpreEq using hTpre
  -- Every `Φ m` is a combination of the chosen evaluations.
  have hTsubrange : (T : Set (↥Conf → 𝔽ᵃ_[p]))
      ⊆ Set.range fun i : Fin T.card =>
        Φ (pre (T.equivFin.symm i).1 (T.equivFin.symm i).2) := by
    intro t ht
    refine ⟨T.equivFin ⟨t, ht⟩, ?_⟩
    have h1 : T.equivFin.symm (T.equivFin ⟨t, ht⟩) = ⟨t, ht⟩ := Equiv.symm_apply_apply _ _
    change Φ (pre (T.equivFin.symm (T.equivFin ⟨t, ht⟩)).1
      (T.equivFin.symm (T.equivFin ⟨t, ht⟩)).2) = t
    rw [h1]
    exact hpreEq t ht
  have hrep : ∀ m : ℤ, -(b : ℤ) ≤ m → ∃ K : Fin T.card → 𝔽ᵃ_[p],
      ∑ i, K i • Φ (pre (T.equivFin.symm i).1 (T.equivFin.symm i).2) = Φ m := by
    intro m hm
    refine (Submodule.mem_span_range_iff_exists_fun (𝔽ᵃ_[p])).mp ?_
    exact Submodule.span_mono hTsubrange (hTspan (Submodule.subset_span ⟨m, hm, rfl⟩))
  refine ⟨T.card, fun i => pre (T.equivFin.symm i).1 (T.equivFin.symm i).2,
    fun m => if hm : -(b : ℤ) ≤ m then (hrep m hm).choose else 0,
    fun i => hpreD _ _, ?_⟩
  intro m hm e he hsum
  simp only [dif_pos hm]
  have hKm := (hrep m hm).choose_spec
  -- Compare `F m` with the combination: they agree at the confined points, hence
  -- on the whole level set.
  refine (hF m hm).eq_on_levelSet_of_eq_on_confined
    (isTwistPeriodic_finset_sum Finset.univ fun i _ =>
      (hF _ (hpreD (T.equivFin.symm i).1 (T.equivFin.symm i).2)).comp
        fun v => (hrep m hm).choose i * v)
    (fun e' he' hbox => ?_) he hsum
  have hz : -fracVal p e' ∈ Conf := by
    rw [hConf]
    exact hConfFin.mem_toFinset.mpr ⟨e', he', hbox, rfl⟩
  have hev := congrFun hKm ⟨-fracVal p e', hz⟩
  simp only [hΦ, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hev
  exact hev.symm

end TrustworthyKedlaya.UP
