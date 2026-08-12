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

end TrustworthyKedlaya.pAdicHahnSeries
