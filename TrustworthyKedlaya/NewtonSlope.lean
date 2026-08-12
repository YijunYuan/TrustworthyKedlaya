/-
Copyright (c) 2026 Shanwen Wang, Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import TrustworthyKedlaya.LpCoeff
public import Mathlib.Algebra.Polynomial.Taylor

/-!
# The last Newton slope of a polynomial over `𝕃_p`

The transfinite Newton algorithm (Wang-Yuan, Section 2) improves an approximate root `z`
of a polynomial `P` over `𝕃_[p]` by tracking the **last slope** of the Newton polygon of
`P`: writing `v` for the valuation and reading coefficients by their degree index,

  `s_max(P) = max { (v(P.coeff 0) - v(P.coeff j)) / j : 1 ≤ j ≤ deg P, P.coeff j ≠ 0 }`.

Rather than the convex-hull combinatorics of the full Newton polygon, only two facts
about `s_max` are ever used, and we take them as the interface:

- the **line bound** `le_val_coeff_of_lastSlope`: every coefficient satisfies
  `v(P.coeff j) ≥ v(P.coeff 0) - s_max(P)·j`;
- **attainment** `exists_lastSlope_attained`: some index `j ≥ 1` attains equality.

The key stability statement (Wang-Yuan, Lemma 2.4; blueprint `lem:newton-shift`) is that
the substitution `T ↦ T + z` with `v(z) ≥ s_max(P)` preserves the line bound
(`le_val_taylor_coeff`), is exact at the top attaining index
(`val_taylor_coeff_eq_of_forall_lt`), and can only increase the last slope
(`lastSlope_le_lastSlope_taylor`); in particular `v(P(z)) ≥ v(P(0))`
(`le_val_eval_of_lastSlope_le`).
-/

@[expose] public section

namespace TrustworthyKedlaya.pAdicHahnSeries

open Polynomial

variable {p : ℕ} [hp : Fact (Nat.Prime p)]

/-! ### The rational value of the valuation -/

/-- The valuation of a series as a bare rational (junk value `0` on the zero series). -/
noncomputable def valQ (x : 𝕃_[p]) : ℚ := (val p x).untopD 0

theorem coe_valQ {x : 𝕃_[p]} (hx : x ≠ 0) : (valQ x : WithTop ℚ) = val p x := by
  obtain ⟨q, hq⟩ := WithTop.ne_top_iff_exists.mp fun h => hx (val_eq_top_iff.mp h)
  rw [valQ, ← hq, WithTop.untopD_coe]

/-! ### Valuation estimates for polynomial evaluation -/

/-- Multiplication by (the image of) a natural number — e.g. a binomial coefficient —
does not lower the valuation. -/
theorem le_val_natCast_mul (n : ℕ) (x : 𝕃_[p]) : val p x ≤ val p ((n : 𝕃_[p]) * x) := by
  induction n with
  | zero => rw [Nat.cast_zero, zero_mul, val_zero_eq_top]; exact le_top
  | succ n ih =>
    rw [Nat.cast_succ, add_mul, one_mul]
    exact (val p).map_le_add ih le_rfl

/-- Powers scale a valuation lower bound linearly. -/
theorem le_val_pow {x : 𝕃_[p]} {s : ℚ} (h : (s : WithTop ℚ) ≤ val p x) (n : ℕ) :
    ((n * s : ℚ) : WithTop ℚ) ≤ val p (x ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, (val p).map_mul]
    have hcast : ((n + 1 : ℕ) : ℚ) * s = n * s + s := by push_cast; ring
    rw [hcast, WithTop.coe_add]
    exact add_le_add ih h

/-! ### The last slope -/

open Classical in
/-- The indices contributing to the last-slope maximum: positive coefficient indices at
which `P` has a nonzero coefficient. -/
noncomputable def slopeIndices (P : Polynomial 𝕃_[p]) : Finset ℕ :=
  (Finset.Icc 1 P.natDegree).filter fun j => P.coeff j ≠ 0

theorem mem_slopeIndices {P : Polynomial 𝕃_[p]} {j : ℕ} :
    j ∈ slopeIndices P ↔ 1 ≤ j ∧ j ≤ P.natDegree ∧ P.coeff j ≠ 0 := by
  simp [slopeIndices, Finset.mem_filter, Finset.mem_Icc, and_assoc]

theorem slopeIndices_nonempty {P : Polynomial 𝕃_[p]} (hP : P ≠ 0)
    (hn : P.natDegree ≠ 0) : (slopeIndices P).Nonempty :=
  ⟨P.natDegree, mem_slopeIndices.mpr ⟨Nat.one_le_iff_ne_zero.mpr hn, le_rfl,
    Polynomial.leadingCoeff_ne_zero.mpr hP⟩⟩

/-- The slope of the segment from `(0, v(P.coeff 0))` to `(j, v(P.coeff j))`, read
downward: `(v(P.coeff 0) - v(P.coeff j)) / j`. -/
noncomputable def slopeAt (P : Polynomial 𝕃_[p]) (j : ℕ) : ℚ :=
  (valQ (P.coeff 0) - valQ (P.coeff j)) / j

open Classical in
/-- The **last slope** `s_max(P)` of a polynomial over `𝕃_[p]` (Wang-Yuan, Section 2):
the largest slope of its Newton polygon, as the maximum of `slopeAt` over
`slopeIndices` (junk value `0` when no index qualifies). -/
noncomputable def lastSlope (P : Polynomial 𝕃_[p]) : ℚ :=
  if h : (slopeIndices P).Nonempty then
    ((slopeIndices P).image (slopeAt P)).max' (h.image (slopeAt P))
  else 0

theorem le_lastSlope {P : Polynomial 𝕃_[p]} {j : ℕ} (hj : j ∈ slopeIndices P) :
    slopeAt P j ≤ lastSlope P := by
  rw [lastSlope, dif_pos ⟨j, hj⟩]
  exact Finset.le_max' _ _ (Finset.mem_image_of_mem _ hj)

theorem exists_lastSlope_attained {P : Polynomial 𝕃_[p]} (h : (slopeIndices P).Nonempty) :
    ∃ j ∈ slopeIndices P, lastSlope P = slopeAt P j := by
  rw [lastSlope, dif_pos h]
  obtain ⟨j, hj, hje⟩ := Finset.mem_image.mp (Finset.max'_mem _ (h.image (slopeAt P)))
  exact ⟨j, hj, hje.symm⟩

/-- The **line bound**: every coefficient of `P` lies on or above the last-slope line
through `(0, v(P.coeff 0))`. -/
theorem le_val_coeff_of_lastSlope {P : Polynomial 𝕃_[p]} (h0 : P.coeff 0 ≠ 0) (j : ℕ) :
    ((valQ (P.coeff 0) - lastSlope P * j : ℚ) : WithTop ℚ) ≤ val p (P.coeff j) := by
  rcases eq_or_ne j 0 with rfl | hj0
  · simp [coe_valQ h0]
  rcases eq_or_ne (P.coeff j) 0 with hcj | hcj
  · rw [hcj, val_zero_eq_top]; exact le_top
  rcases le_or_gt j P.natDegree with hjn | hjn
  · have hj : j ∈ slopeIndices P :=
      mem_slopeIndices.mpr ⟨Nat.one_le_iff_ne_zero.mpr hj0, hjn, hcj⟩
    have hle := le_lastSlope hj
    rw [slopeAt, div_le_iff₀ (by positivity : (0 : ℚ) < j)] at hle
    rw [← coe_valQ hcj]
    exact WithTop.coe_le_coe.mpr (by linarith)
  · exact absurd (Polynomial.coeff_eq_zero_of_natDegree_lt hjn) hcj

/-! ### Line-bound transport under the shift `T ↦ T + z` -/

/-- **Line-bound transport** (Wang-Yuan, Lemma 2.4): if every coefficient of `P`
satisfies the valuation line bound `v(P.coeff j) ≥ v₀ - s·j` and `v(z) ≥ s`, then the
coefficients of `P(T + z)` satisfy the same bound. -/
theorem le_val_taylor_coeff {P : Polynomial 𝕃_[p]} {v₀ s : ℚ}
    (hline : ∀ j : ℕ, ((v₀ - s * j : ℚ) : WithTop ℚ) ≤ val p (P.coeff j))
    {z : 𝕃_[p]} (hz : (s : WithTop ℚ) ≤ val p z) (k : ℕ) :
    ((v₀ - s * k : ℚ) : WithTop ℚ) ≤ val p ((Polynomial.taylor z P).coeff k) := by
  rw [Polynomial.taylor_coeff, Polynomial.eval_eq_sum_range]
  apply (val p).map_le_sum
  intro j _
  rw [Polynomial.hasseDeriv_coeff]
  have hsplit : (v₀ - s * k : ℚ) = (v₀ - s * ((j + k : ℕ) : ℚ)) + j * s := by
    push_cast; ring
  calc ((v₀ - s * k : ℚ) : WithTop ℚ)
      = ((v₀ - s * ((j + k : ℕ) : ℚ) : ℚ) : WithTop ℚ) + ((j * s : ℚ) : WithTop ℚ) := by
        rw [← WithTop.coe_add, hsplit]
    _ ≤ val p (((j + k).choose k : 𝕃_[p]) * P.coeff (j + k)) + val p (z ^ j) :=
        add_le_add (le_trans (hline (j + k)) (le_val_natCast_mul _ _)) (le_val_pow hz j)
    _ = val p (((j + k).choose k : 𝕃_[p]) * P.coeff (j + k) * z ^ j) :=
        ((val p).map_mul _ _).symm

/-- `v(P(z)) ≥ v(P(0))` whenever `v(z) ≥ s_max(P)` (Wang-Yuan, Lemma 2.4). -/
theorem le_val_eval_of_lastSlope_le {P : Polynomial 𝕃_[p]} (h0 : P.coeff 0 ≠ 0)
    {z : 𝕃_[p]} (hz : ((lastSlope P : ℚ) : WithTop ℚ) ≤ val p z) :
    val p (P.coeff 0) ≤ val p (P.eval z) := by
  have h := le_val_taylor_coeff (le_val_coeff_of_lastSlope h0) hz 0
  rw [Polynomial.taylor_coeff_zero] at h
  simpa [coe_valQ h0] using h

/-! ### Exactness at the top attaining index -/

/-- **Exactness transport**: if the line bound is exact at `k₀` and strict at every
larger index, then after the shift `T ↦ T + z` (with `v(z) ≥ s`) it is still exact
at `k₀`. -/
theorem val_taylor_coeff_eq_of_forall_lt {P : Polynomial 𝕃_[p]} {v₀ s : ℚ} {k₀ : ℕ}
    (hexact : val p (P.coeff k₀) = ((v₀ - s * k₀ : ℚ) : WithTop ℚ))
    (hstrict : ∀ j : ℕ, k₀ < j → ((v₀ - s * j : ℚ) : WithTop ℚ) < val p (P.coeff j))
    {z : 𝕃_[p]} (hz : (s : WithTop ℚ) ≤ val p z) :
    val p ((Polynomial.taylor z P).coeff k₀) = ((v₀ - s * k₀ : ℚ) : WithTop ℚ) := by
  rw [Polynomial.taylor_coeff, Polynomial.eval_eq_sum_range, Finset.sum_range_succ']
  -- the `j = 0` term is exactly `P.coeff k₀`
  have hzero : (Polynomial.hasseDeriv k₀ P).coeff 0 * z ^ 0 = P.coeff k₀ := by
    simp [Polynomial.hasseDeriv_coeff]
  -- every `j ≥ 1` term lies strictly above the line
  have hrest : ((v₀ - s * k₀ : ℚ) : WithTop ℚ)
      < val p (∑ i ∈ Finset.range (Polynomial.hasseDeriv k₀ P).natDegree,
          (Polynomial.hasseDeriv k₀ P).coeff (i + 1) * z ^ (i + 1)) := by
    apply (val p).map_lt_sum WithTop.coe_ne_top
    intro j _
    rw [Polynomial.hasseDeriv_coeff]
    have h1 : ((v₀ - s * ((j + 1 + k₀ : ℕ) : ℚ) : ℚ) : WithTop ℚ)
        < val p (((j + 1 + k₀).choose k₀ : 𝕃_[p]) * P.coeff (j + 1 + k₀)) :=
      lt_of_lt_of_le (hstrict _ (by omega)) (le_val_natCast_mul _ _)
    have h2 : (((j + 1 : ℕ) * s : ℚ) : WithTop ℚ) ≤ val p (z ^ (j + 1)) :=
      le_val_pow hz (j + 1)
    have hsplit : (v₀ - s * k₀ : ℚ)
        = (v₀ - s * ((j + 1 + k₀ : ℕ) : ℚ)) + ((j + 1 : ℕ) : ℚ) * s := by
      push_cast; ring
    calc ((v₀ - s * k₀ : ℚ) : WithTop ℚ)
        = ((v₀ - s * ((j + 1 + k₀ : ℕ) : ℚ) : ℚ) : WithTop ℚ)
            + (((j + 1 : ℕ) * s : ℚ) : WithTop ℚ) := by
          rw [← WithTop.coe_add, hsplit]
      _ < val p (((j + 1 + k₀).choose k₀ : 𝕃_[p]) * P.coeff (j + 1 + k₀))
            + (((j + 1 : ℕ) * s : ℚ) : WithTop ℚ) :=
          WithTop.add_lt_add_right WithTop.coe_ne_top h1
      _ ≤ val p (((j + 1 + k₀).choose k₀ : 𝕃_[p]) * P.coeff (j + 1 + k₀))
            + val p (z ^ (j + 1)) := add_le_add le_rfl h2
      _ = val p (((j + 1 + k₀).choose k₀ : 𝕃_[p]) * P.coeff (j + 1 + k₀) * z ^ (j + 1)) :=
          ((val p).map_mul _ _).symm
  rw [hzero, (val p).map_add_eq_of_lt_right (by rw [hexact]; exact hrest)]
  exact hexact

open Classical in
/-- The **top attainer**: the largest index attaining the last-slope maximum.  It
attains the line bound exactly, and every index strictly above it satisfies the line
bound strictly. -/
theorem exists_topAttainer {P : Polynomial 𝕃_[p]} (hP : P ≠ 0) (hn : P.natDegree ≠ 0)
    (h0 : P.coeff 0 ≠ 0) :
    ∃ k₀, 1 ≤ k₀ ∧ k₀ ≤ P.natDegree ∧
      val p (P.coeff k₀) = ((valQ (P.coeff 0) - lastSlope P * k₀ : ℚ) : WithTop ℚ) ∧
      ∀ j : ℕ, k₀ < j →
        ((valQ (P.coeff 0) - lastSlope P * j : ℚ) : WithTop ℚ) < val p (P.coeff j) := by
  set A := (slopeIndices P).filter
    (fun j => valQ (P.coeff j) = valQ (P.coeff 0) - lastSlope P * j) with hA_def
  have hA_ne : A.Nonempty := by
    obtain ⟨j, hj, hje⟩ := exists_lastSlope_attained (slopeIndices_nonempty hP hn)
    refine ⟨j, Finset.mem_filter.mpr ⟨hj, ?_⟩⟩
    have hjQ : (j : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by
      have := (mem_slopeIndices.mp hj).1; omega)
    rw [slopeAt, eq_div_iff hjQ] at hje
    linarith
  refine ⟨A.max' hA_ne, ?_, ?_, ?_, ?_⟩
  · exact (mem_slopeIndices.mp (Finset.mem_filter.mp (Finset.max'_mem A hA_ne)).1).1
  · exact (mem_slopeIndices.mp (Finset.mem_filter.mp (Finset.max'_mem A hA_ne)).1).2.1
  · have hc := (mem_slopeIndices.mp (Finset.mem_filter.mp (Finset.max'_mem A hA_ne)).1).2.2
    rw [← coe_valQ hc, (Finset.mem_filter.mp (Finset.max'_mem A hA_ne)).2]
  · intro j hj
    rcases eq_or_ne (P.coeff j) 0 with hcj | hcj
    · rw [hcj, val_zero_eq_top]; exact WithTop.coe_lt_top _
    · have hjS : j ∈ slopeIndices P := mem_slopeIndices.mpr
        ⟨by have := (mem_slopeIndices.mp (Finset.mem_filter.mp
            (Finset.max'_mem A hA_ne)).1).1; omega,
          Polynomial.le_natDegree_of_ne_zero hcj, hcj⟩
      rcases (le_val_coeff_of_lastSlope h0 j).lt_or_eq with hlt | heq
      · exact hlt
      · exfalso
        have hjA : j ∈ A := Finset.mem_filter.mpr ⟨hjS, by
          rw [← coe_valQ hcj] at heq
          exact (WithTop.coe_inj.mp heq).symm⟩
        exact absurd (Finset.le_max' A j hjA) (by omega)

/-- **Shift stability of the last slope** (Wang-Yuan, Lemma 2.4; second half of
`lem:newton-shift`): substituting `T ↦ T + z` with `v(z) ≥ s_max(P)` can only increase
the last slope, provided the shifted polynomial keeps a nonzero constant term. -/
theorem lastSlope_le_lastSlope_taylor {P : Polynomial 𝕃_[p]} (hP : P ≠ 0)
    (hn : P.natDegree ≠ 0) (h0 : P.coeff 0 ≠ 0) {z : 𝕃_[p]}
    (hz : ((lastSlope P : ℚ) : WithTop ℚ) ≤ val p z)
    (hz0 : (Polynomial.taylor z P).coeff 0 ≠ 0) :
    lastSlope P ≤ lastSlope (Polynomial.taylor z P) := by
  obtain ⟨k₀, hk₀1, hk₀n, hexact, hstrict⟩ := exists_topAttainer hP hn h0
  have htay := val_taylor_coeff_eq_of_forall_lt hexact hstrict hz
  have h0tay := le_val_taylor_coeff (le_val_coeff_of_lastSlope h0) hz 0
  -- the shifted coefficient at `k₀` is nonzero, so `k₀` indexes a slope of the shift
  have hk₀tay_c : (Polynomial.taylor z P).coeff k₀ ≠ 0 := by
    intro hzero
    rw [hzero, val_zero_eq_top] at htay
    exact absurd htay.symm WithTop.coe_ne_top
  have hk₀tayS : k₀ ∈ slopeIndices (Polynomial.taylor z P) :=
    mem_slopeIndices.mpr ⟨hk₀1, by rw [Polynomial.natDegree_taylor]; exact hk₀n, hk₀tay_c⟩
  refine le_trans ?_ (le_lastSlope hk₀tayS)
  -- compare through the ratio at `k₀`
  have hvk : valQ ((Polynomial.taylor z P).coeff k₀)
      = valQ (P.coeff 0) - lastSlope P * k₀ :=
    WithTop.coe_inj.mp (by rw [coe_valQ hk₀tay_c, htay])
  have hv0' : valQ (P.coeff 0) ≤ valQ ((Polynomial.taylor z P).coeff 0) := by
    rw [← coe_valQ hz0] at h0tay
    have := WithTop.coe_le_coe.mp h0tay
    simpa using this
  rw [slopeAt, hvk, le_div_iff₀ (by exact_mod_cast Nat.pos_of_ne_zero (by omega))]
  linarith

/-- The last slope is the **least** `s` satisfying the line bound (the equivalent
characterization in Wang-Yuan, Section 2). -/
theorem lastSlope_le_of_line_bound {P : Polynomial 𝕃_[p]} (hP : P ≠ 0)
    (hn : P.natDegree ≠ 0) {s' : ℚ}
    (h : ∀ j : ℕ, 1 ≤ j → j ≤ P.natDegree → P.coeff j ≠ 0 →
      valQ (P.coeff 0) - s' * j ≤ valQ (P.coeff j)) :
    lastSlope P ≤ s' := by
  obtain ⟨j, hj, hje⟩ := exists_lastSlope_attained (slopeIndices_nonempty hP hn)
  obtain ⟨h1, h2, h3⟩ := mem_slopeIndices.mp hj
  rw [hje, slopeAt, div_le_iff₀ (by exact_mod_cast Nat.pos_of_ne_zero (by omega))]
  have := h j h1 h2 h3
  linarith

/-! ### The residue polynomial -/

/-- The **residue polynomial** of `P` along its last slope (Wang-Yuan, Section 2): the
coefficients of `P` on the last-slope line, read through the coefficient maps of
`𝕃_[p]`. -/
noncomputable def residuePoly (P : Polynomial 𝕃_[p]) : Polynomial (Fpbar p) :=
  ∑ k ∈ Finset.range (P.natDegree + 1),
    Polynomial.C ((P.coeff k).coeff (valQ (P.coeff 0) - lastSlope P * k))
      * Polynomial.X ^ k

theorem residuePoly_coeff (P : Polynomial 𝕃_[p]) {k : ℕ} (hk : k ≤ P.natDegree) :
    (residuePoly P).coeff k
      = (P.coeff k).coeff (valQ (P.coeff 0) - lastSlope P * k) := by
  rw [residuePoly, Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single k (fun j _ hjk => by
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg (Ne.symm hjk), mul_zero])
    (fun hk' => absurd (Finset.mem_range.mpr (Nat.lt_succ_of_le hk)) hk')]
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl, mul_one]

theorem natDegree_residuePoly_le (P : Polynomial 𝕃_[p]) :
    (residuePoly P).natDegree ≤ P.natDegree := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro k hk
  refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
  rw [Polynomial.natDegree_X_pow]
  exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)

/-- The residue polynomial has **nonzero constant term** (Wang-Yuan, Section 2): the
coefficient of `P.coeff 0` at its own valuation. -/
theorem residuePoly_coeff_zero_ne_zero {P : Polynomial 𝕃_[p]} (h0 : P.coeff 0 ≠ 0) :
    (residuePoly P).coeff 0 ≠ 0 := by
  rw [residuePoly_coeff P (Nat.zero_le _)]
  simp only [Nat.cast_zero, mul_zero, sub_zero]
  exact coeff_val_ne_zero (coe_valQ h0).symm

/-- The residue polynomial is **nonconstant** (Wang-Yuan, Section 2): the top attaining
index contributes a nonzero coefficient in positive degree. -/
theorem exists_residuePoly_coeff_ne_zero {P : Polynomial 𝕃_[p]} (hP : P ≠ 0)
    (hn : P.natDegree ≠ 0) (h0 : P.coeff 0 ≠ 0) :
    ∃ k, 1 ≤ k ∧ k ≤ P.natDegree ∧ (residuePoly P).coeff k ≠ 0 := by
  obtain ⟨k₀, hk₀1, hk₀n, hexact, -⟩ := exists_topAttainer hP hn h0
  exact ⟨k₀, hk₀1, hk₀n, by
    rw [residuePoly_coeff P hk₀n]; exact coeff_val_ne_zero hexact⟩

end TrustworthyKedlaya.pAdicHahnSeries
