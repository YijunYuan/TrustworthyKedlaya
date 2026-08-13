/-
Copyright (c) 2026 Shanwen Wang, Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import TrustworthyKedlaya.SupportSets
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.RingTheory.Finiteness.Cardinality

/-!
# Twist-periodic functions have finite image

For an `(M, N)`-periodic function `f : ℚ → 𝔽̄_p` at digit-sum level `c`, the values of
`f` on the *level set* — the negated values of canonical digit expansions of digit sum
at most `c`, i.e. `T_c ∪ {0}` — form a finite set, and consequently lie in a single
finite subfield `𝔽_{p^d} ⊆ 𝔽̄_p`.  This is the finiteness input to the twist-recurrence
orbit argument of Kedlaya (2001a): `eventually_periodic_of_frobenius_affine` needs its
sequences to take values in one finite subfield, and the values in question are values
of twist-periodic slice functions.

The engine is *gap contraction*: a point whose digit string has a run of `M + N` zeros
is a twist evaluation point with a large gap (`gapDig_dropGapDig`), so periodicity
shortens the run by `N` without changing the value of `f`.  A digit string of digit sum
`≤ c` meets at most `c` of the `c + 1` disjoint digit blocks of length `M + N` below
position `(c+1)(M+N)`, so a string reaching past that position has a full free block
below its top; contracting it repeatedly confines the digits to
`Finset.range ((c+1)(M+N))` — finitely many points.

## Main statements

- `TrustworthyKedlaya.UP.exists_confined_rep_forall`: gap contraction into the finite
  digit box, with a representative depending only on the digit string (uniform over
  all `(M, N)`-periodic functions at level `c`).
- `TrustworthyKedlaya.UP.IsTwistPeriodic.exists_confined_rep`: the per-function form.
- `TrustworthyKedlaya.UP.IsTwistPeriodic.finite_image_levelSet`: the image of the level
  set under `f` is finite.
- `TrustworthyKedlaya.UP.IsTwistPeriodic.finite_image_Tc`: `f '' T_c` is finite.
- `TrustworthyKedlaya.UP.IsTwistPeriodic.exists_uniform_subfield`: a single exponent
  `d ≥ 1` with `f(z) ^ (p^d) = f(z)` for every point `z` of the level set.

## References

- K. S. Kedlaya, *The algebraic closure of the power series field in positive
  characteristic*, Proc. Amer. Math. Soc. 129 (2001) [Ked01a], proof of Lemma 4.
-/

@[expose] public section

namespace TrustworthyKedlaya.UP

open IntermediateField

variable (p : ℕ) [hp : Fact (Nat.Prime p)]

/-- Every element of `𝔽̄_p = AlgebraicClosure (ZMod p)` lies in a finite subfield:
`x ^ p ^ d = x` for some `d ≥ 1` (namely `d` the degree of `x` over `𝔽_p`). -/
theorem exists_pow_pow_eq_self (x : 𝔽ᵃ_[p]) : ∃ d : ℕ, 0 < d ∧ x ^ p ^ d = x := by
  have hint : IsIntegral (ZMod p) x := (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  have : FiniteDimensional (ZMod p) (ZMod p)⟮x⟯ :=
    IntermediateField.adjoin.finiteDimensional hint
  have : Finite ((ZMod p)⟮x⟯ : IntermediateField (ZMod p) (𝔽ᵃ_[p])) :=
    Module.finite_of_finite (ZMod p)
  have : Fintype ((ZMod p)⟮x⟯ : IntermediateField (ZMod p) (𝔽ᵃ_[p])) :=
    Fintype.ofFinite _
  refine ⟨Module.finrank (ZMod p) (ZMod p)⟮x⟯, Module.finrank_pos, ?_⟩
  have hcard : Fintype.card ((ZMod p)⟮x⟯ : IntermediateField (ZMod p) (𝔽ᵃ_[p]))
      = p ^ Module.finrank (ZMod p) (ZMod p)⟮x⟯ := by
    rw [Module.card_eq_pow_finrank (K := ZMod p), ZMod.card]
  have hx : (⟨x, mem_adjoin_simple_self (ZMod p) x⟩ : (ZMod p)⟮x⟯)
      ^ p ^ Module.finrank (ZMod p) (ZMod p)⟮x⟯
      = ⟨x, mem_adjoin_simple_self (ZMod p) x⟩ := by
    rw [← hcard]
    exact FiniteField.pow_card _
  have hx2 := congrArg (fun y : (ZMod p)⟮x⟯ => (y : 𝔽ᵃ_[p])) hx
  push_cast at hx2
  exact hx2

variable {p}

/-- **Gap contraction, function-independent form**: every canonical expansion of digit
sum `≤ c` has a *confined representative* — an expansion with digits confined to
`Finset.range ((c+1)(M+N))` — at which **every** `(M, N)`-periodic function at level
`c` takes the same value as at the original expansion.  The contraction (which block
to collapse, and by how much) depends only on the digit string, never on the
function; this uniformity is what makes the slice-span dimension bound work. -/
theorem exists_confined_rep_forall (c : ℕ) (M N : ℕ+) {e : ℕ →₀ ℕ} (he : ∀ i, e i < p)
    (hsum : (e.sum fun _ v => v) ≤ c) :
    ∃ e' : ℕ →₀ ℕ, (∀ i, e' i < p) ∧ (e'.sum fun _ v => v) ≤ c ∧
      e'.support ⊆ Finset.range ((c + 1) * ((M : ℕ) + N)) ∧
      ∀ f : ℚ → 𝔽ᵃ_[p], IsTwistPeriodic p f c M N →
        f (-fracVal p e') = f (-fracVal p e) := by
  obtain ⟨n, hn⟩ := e.support.exists_nat_subset_range
  induction n using Nat.strong_induction_on generalizing e with
  | _ n ih =>
  by_cases hsmall : n ≤ (c + 1) * ((M : ℕ) + N)
  · refine ⟨e, he, hsum, hn.trans fun x hx => ?_, fun _ _ => rfl⟩
    rw [Finset.mem_range] at hx ⊢
    omega
  -- Pigeonhole: one of the `c + 1` blocks `[k(M+N), (k+1)(M+N))` misses the support.
  have hL0 : 0 < (M : ℕ) + N := by positivity
  have hcard : e.support.card ≤ c := by
    have h1 : e.support.card • 1 ≤ e.sum fun _ v => v :=
      Finset.card_nsmul_le_sum e.support _ 1 fun i hi =>
        Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi)
    simpa using h1.trans hsum
  obtain ⟨k₀, hk₀mem, hk₀⟩ : ∃ k₀ ∈ Finset.range (c + 1),
      k₀ ∉ e.support.image (· / ((M : ℕ) + N)) := by
    by_contra hcon
    push Not at hcon
    have hcards := (Finset.card_le_card hcon).trans
      (Finset.card_image_le.trans hcard)
    rw [Finset.card_range] at hcards
    omega
  have hk₀c : k₀ ≤ c := by
    have := Finset.mem_range.mp hk₀mem
    omega
  -- The block `[k₀(M+N), k₀(M+N) + (M+N))` carries no digits of `e`.
  have hgap : ∀ i, k₀ * ((M : ℕ) + N) ≤ i → i < k₀ * ((M : ℕ) + N) + ((M : ℕ) + N) →
      e i = 0 := by
    intro i h1 h2
    by_contra h0
    refine hk₀ (Finset.mem_image.mpr ⟨i, Finsupp.mem_support_iff.mpr h0, ?_⟩)
    have hle : k₀ ≤ i / ((M : ℕ) + N) := (Nat.le_div_iff_mul_le hL0).mpr h1
    have hlt : i / ((M : ℕ) + N) < k₀ + 1 :=
      (Nat.div_lt_iff_lt_mul hL0).mpr (by linarith [h2])
    omega
  set b : ℕ →₀ ℕ := dropGapDig (k₀ * ((M : ℕ) + N)) ((M : ℕ) + N) e with hb
  have hbe : gapDig (k₀ * ((M : ℕ) + N) + 1) ((M : ℕ) + N) b = e := gapDig_dropGapDig hgap
  have hblt : ∀ i, b i < p := fun i => dropGapDig_lt p he _ _ i
  have hbsum : (b.sum fun _ v => v) ≤ c := by
    have hgs := gapDig_sum (k₀ * ((M : ℕ) + N) + 1) ((M : ℕ) + N) b
    rw [hbe] at hgs
    exact hgs ▸ hsum
  -- Periodicity contracts the gap from `M + N` to `M` — for every periodic `f` at once.
  have hstep : ∀ f : ℚ → 𝔽ᵃ_[p], IsTwistPeriodic p f c M N →
      f (-fracVal p (gapDig (k₀ * ((M : ℕ) + N) + 1) (M : ℕ) b))
        = f (-fracVal p e) := by
    intro f hf
    have hper := hf (k₀ * ((M : ℕ) + N) + 1) b (Nat.succ_pos _) hblt hbsum (M : ℕ) le_rfl
    rw [twistSeq_eq_neg_fracVal_gapDig, twistSeq_eq_neg_fracVal_gapDig, hbe] at hper
    exact hper.symm
  -- The contracted string fits below `n - N`; recurse.
  have hsupp' : (gapDig (k₀ * ((M : ℕ) + N) + 1) (M : ℕ) b).support
      ⊆ Finset.range (n - N) := by
    intro i hi
    rw [Finsupp.mem_support_iff, gapDig_apply, Nat.add_sub_cancel] at hi
    rw [Finset.mem_range]
    have hblock : k₀ * ((M : ℕ) + N) + ((M : ℕ) + N) ≤ (c + 1) * ((M : ℕ) + N) := by
      calc k₀ * ((M : ℕ) + N) + ((M : ℕ) + N) = (k₀ + 1) * ((M : ℕ) + N) := by ring
        _ ≤ (c + 1) * ((M : ℕ) + N) := Nat.mul_le_mul_right _ (by omega)
    by_cases h1 : i < k₀ * ((M : ℕ) + N)
    · rw [if_pos h1] at hi
      rw [hb, dropGapDig_apply, if_pos h1] at hi
      have := Finset.mem_range.mp (hn (Finsupp.mem_support_iff.mpr hi))
      omega
    · rw [if_neg h1] at hi
      by_cases h2 : k₀ * ((M : ℕ) + N) + M ≤ i
      · rw [if_pos h2] at hi
        rw [hb, dropGapDig_apply, if_neg (by omega)] at hi
        have hidx : i - (M : ℕ) + ((M : ℕ) + N) = i + N := by omega
        rw [hidx] at hi
        have := Finset.mem_range.mp (hn (Finsupp.mem_support_iff.mpr hi))
        omega
      · rw [if_neg h2] at hi
        exact absurd rfl hi
  obtain ⟨e', he', hsum', hbox, hval⟩ := ih (n - N) (by have := N.pos; omega)
    (fun i => gapDig_lt p hblt hp.out.pos _ _ i)
    (by rw [gapDig_sum]; exact hbsum) hsupp'
  exact ⟨e', he', hsum', hbox, fun f hf => (hval f hf).trans (hstep f hf)⟩

/-- **Gap contraction** (per-function corollary of `exists_confined_rep_forall`): modulo
the values of an `(M, N)`-periodic function at level `c`, every canonical expansion of
digit sum `≤ c` may be replaced by one with digits confined to
`Finset.range ((c+1)(M+N))`. -/
theorem IsTwistPeriodic.exists_confined_rep {f : ℚ → 𝔽ᵃ_[p]} {c : ℕ} {M N : ℕ+}
    (h : IsTwistPeriodic p f c M N) {e : ℕ →₀ ℕ} (he : ∀ i, e i < p)
    (hsum : (e.sum fun _ v => v) ≤ c) :
    ∃ e' : ℕ →₀ ℕ, (∀ i, e' i < p) ∧ (e'.sum fun _ v => v) ≤ c ∧
      e'.support ⊆ Finset.range ((c + 1) * ((M : ℕ) + N)) ∧
      f (-fracVal p e') = f (-fracVal p e) := by
  obtain ⟨e', he', hsum', hbox, hval⟩ := exists_confined_rep_forall c M N he hsum
  exact ⟨e', he', hsum', hbox, hval f h⟩

variable (p)

/-- The negated values of canonical expansions with digits `< p` confined to
`Finset.range B` form a finite set (there are at most `p ^ B` of them). -/
theorem finite_neg_fracVal_confined (B : ℕ) :
    {z : ℚ | ∃ e : ℕ →₀ ℕ, (∀ i, e i < p) ∧ e.support ⊆ Finset.range B ∧
      z = -fracVal p e}.Finite := by
  refine Set.Finite.subset ((Set.finite_Iio (p ^ B)).image
    fun C : ℕ => -((C : ℚ) / (p : ℚ) ^ B)) ?_
  rintro z ⟨e, he, hsupp, rfl⟩
  have hval := fracVal_mul_pow p hp.out.pos e hsupp
  set C : ℕ := Nat.ofDigits p ((List.range B).map fun j => e (B - 1 - j)) with hC
  have hp0 : (0 : ℚ) < (p : ℚ) := by exact_mod_cast hp.out.pos
  have hpow : (0 : ℚ) < (p : ℚ) ^ B := by positivity
  refine ⟨C, Set.mem_Iio.mpr ?_, ?_⟩
  · have hlt : fracVal p e < 1 := fracVal_lt_one p hp.out.one_lt he
    have h2 : (C : ℚ) < (p : ℚ) ^ B := by
      rw [← hval]
      nlinarith [fracVal_nonneg p e]
    exact_mod_cast h2
  · rw [neg_inj, div_eq_iff hpow.ne']
    exact hval.symm

/-- Points of `T_c` are negated values of canonical expansions of digit sum `≤ c`. -/
theorem Tc_subset_neg_fracVal (c : ℕ) :
    Tc p c ⊆ {z : ℚ | ∃ e : ℕ →₀ ℕ, (∀ i, e i < p) ∧ (e.sum fun _ v => v) ≤ c ∧
      z = -fracVal p e} := by
  rintro z ⟨⟨n, d, hn, hd, hsum, rfl⟩, hIoo⟩
  refine ⟨d, hd, hsum, ?_⟩
  obtain ⟨h1, h2⟩ := hIoo
  rw [fracVal_def] at h1 h2 ⊢
  have hlt := fracVal_lt_one p hp.out.one_lt hd
  have hnn := fracVal_nonneg p d
  have hone : ((1 : ℕ+) : ℚ) = 1 := by norm_num
  rw [hone] at h1 h2 ⊢
  have hn0 : n = 0 := by
    have hu : (n : ℚ) < 1 := by nlinarith
    have hl : (-1 : ℚ) < (n : ℚ) := by nlinarith
    have hu' : n < 1 := by exact_mod_cast hu
    have hl' : -1 < n := by exact_mod_cast hl
    omega
  rw [hn0]
  push_cast
  ring

variable {p}

/-- **Finite image** (Kedlaya (2001a), proof of Lemma 4): a twist-periodic function at
level `c` takes finitely many values on the negated canonical expansions of digit sum
`≤ c`. -/
theorem IsTwistPeriodic.finite_image_levelSet {f : ℚ → 𝔽ᵃ_[p]} {c : ℕ} {M N : ℕ+}
    (h : IsTwistPeriodic p f c M N) :
    {v : 𝔽ᵃ_[p] | ∃ e : ℕ →₀ ℕ, (∀ i, e i < p) ∧ (e.sum fun _ v => v) ≤ c ∧
      v = f (-fracVal p e)}.Finite := by
  refine Set.Finite.subset
    ((finite_neg_fracVal_confined p ((c + 1) * ((M : ℕ) + N))).image f) ?_
  rintro v ⟨e, he, hsum, rfl⟩
  obtain ⟨e', he', hsum', hbox, hval⟩ := h.exists_confined_rep he hsum
  exact ⟨-fracVal p e', ⟨e', he', hbox, rfl⟩, hval⟩

/-- The image `f '' T_c` of a twist-periodic function at level `c` is finite. -/
theorem IsTwistPeriodic.finite_image_Tc {f : ℚ → 𝔽ᵃ_[p]} {c : ℕ} {M N : ℕ+}
    (h : IsTwistPeriodic p f c M N) : (f '' Tc p c).Finite := by
  refine h.finite_image_levelSet.subset ?_
  rintro v ⟨z, hz, rfl⟩
  obtain ⟨e, he, hsum, rfl⟩ := Tc_subset_neg_fracVal p c hz
  exact ⟨e, he, hsum, rfl⟩

/-- **A single finite subfield receives all level-`c` values** of a twist-periodic
function: there is `d ≥ 1` with `f(-w)^(p^d) = f(-w)` for every canonical expansion `w`
of digit sum `≤ c`.  This includes all values of all twist sequences of `f` built from
level-`c` digit data (the twist evaluation points are the `-w` by
`twistSeq_eq_neg_fracVal_gapDig`), which is the hypothesis format of the orbit lemma
`eventually_periodic_of_frobenius_affine`. -/
theorem IsTwistPeriodic.exists_uniform_subfield {f : ℚ → 𝔽ᵃ_[p]} {c : ℕ} {M N : ℕ+}
    (h : IsTwistPeriodic p f c M N) :
    ∃ d : ℕ, 0 < d ∧ ∀ e : ℕ →₀ ℕ, (∀ i, e i < p) → (e.sum fun _ v => v) ≤ c →
      f (-fracVal p e) ^ p ^ d = f (-fracVal p e) := by
  choose dOf hdOf using exists_pow_pow_eq_self p
  refine ⟨∏ v ∈ h.finite_image_levelSet.toFinset, dOf v,
    Finset.prod_pos fun v _ => (hdOf v).1, ?_⟩
  intro e he hsum
  have hmem : f (-fracVal p e) ∈ h.finite_image_levelSet.toFinset :=
    h.finite_image_levelSet.mem_toFinset.mpr ⟨e, he, hsum, rfl⟩
  obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem dOf hmem
  rw [hk]
  exact pow_pow_mul_eq_self (hdOf _).2 k

end TrustworthyKedlaya.UP
