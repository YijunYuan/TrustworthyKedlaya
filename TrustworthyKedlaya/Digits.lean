/-
Copyright (c) 2026 Shanwen Wang, Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Nat.Digits.Lemmas
public import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# Base-`p` digit sums and fractional digit expansions

Support sets `S_{a,b,c}` are described by fractional base-`p` expansions with bounded digit
sum, modelled as finitely supported functions `d : ℕ →₀ ℕ` of value
`∑ i, d i · p^{-(i+1)}`.  This file provides the arithmetic infrastructure for manipulating
them:

- digit-sum subadditivity for natural numbers, `(p.digits (m + n)).sum ≤
  (p.digits m).sum + (p.digits n).sum`, via Legendre's factorial formula (each carry lowers
  the digit sum by `p - 1`);
- the bridge between a digit finsupp supported in `[0, L)` and the natural number obtained
  by scaling its value by `p^L` (an `Nat.ofDigits` value of the reversed digit list);
- `exists_carry_normalization`: any finitely supported "pseudo-digit" expansion (entries
  allowed to be `≥ p`) equals `k + fracVal d` for an integer carry `k ≥ 0` and a canonical
  expansion `d` (digits `< p`), with `(p.digits k).sum + digitsum d ≤ digitsum e`.

These are the carry lemmas underlying the support calculus of Kedlaya (2001a), Lemma 2 and
Kedlaya (2017), Section 2.

## References

- K. S. Kedlaya, *The algebraic closure of the power series field in positive
  characteristic*, Proc. Amer. Math. Soc. 129 (2001) [Ked01a].
- K. S. Kedlaya, *On the algebraicity of generalized power series*, Beiträge Algebra
  Geom. 58 (2017) [Ked17].
-/

@[expose] public section

namespace TrustworthyKedlaya.UP

open Finset

variable (p : ℕ)

/-! ### Digit sums of natural numbers -/

/-- For any base `p ≥ 1` the list sum of a (pseudo-)digit list bounds nothing more than its
`ofDigits` value: `l.sum ≤ Nat.ofDigits p l`. -/
theorem sum_le_ofDigits (hp : 1 ≤ p) (l : List ℕ) : l.sum ≤ Nat.ofDigits p l := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [Nat.ofDigits_cons, List.sum_cons]
    have h1 : Nat.ofDigits p t ≤ p * Nat.ofDigits p t := Nat.le_mul_of_pos_left _ hp
    omega

/-- The base-`p` digit sum of `n` is at most `n`. -/
theorem sum_digits_le_self (hp : 1 ≤ p) (n : ℕ) : (p.digits n).sum ≤ n := by
  conv_rhs => rw [← Nat.ofDigits_digits p n]
  exact sum_le_ofDigits p hp _

/-- **Digit sums are subadditive** in a prime base: each carry lowers the digit sum by
`p - 1`.  Proved via Legendre's formula `(p-1)·v_p(n!) = n - S_p(n)` and integrality of
binomial coefficients. -/
theorem sum_digits_add_le [hp : Fact p.Prime] (m n : ℕ) :
    (p.digits (m + n)).sum ≤ (p.digits m).sum + (p.digits n).sum := by
  have L1 := sub_one_mul_padicValNat_factorial (p := p) (m + n)
  have L2 := sub_one_mul_padicValNat_factorial (p := p) m
  have L3 := sub_one_mul_padicValNat_factorial (p := p) n
  have hfac : (m + n).choose m * m.factorial * n.factorial = (m + n).factorial := by
    simpa using Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right m n)
  have hchoose : (m + n).choose m ≠ 0 := (Nat.choose_pos (Nat.le_add_right m n)).ne'
  have hv : padicValNat p m.factorial + padicValNat p n.factorial ≤
      padicValNat p (m + n).factorial := by
    rw [← hfac, padicValNat.mul (mul_ne_zero hchoose m.factorial_ne_zero) n.factorial_ne_zero,
      padicValNat.mul hchoose m.factorial_ne_zero]
    omega
  have hb1 : (p - 1) * (padicValNat p m.factorial + padicValNat p n.factorial) ≤
      (p - 1) * padicValNat p (m + n).factorial := Nat.mul_le_mul_left _ hv
  rw [Nat.mul_add, L1, L2, L3] at hb1
  have s1 := sum_digits_le_self p hp.out.one_lt.le (m + n)
  have s2 := sum_digits_le_self p hp.out.one_lt.le m
  have s3 := sum_digits_le_self p hp.out.one_lt.le n
  omega

/-- Multiplying by the base shifts digits, so the digit sum is unchanged. -/
theorem sum_digits_base_mul (hp : 1 < p) (m : ℕ) :
    (p.digits (p * m)).sum = (p.digits m).sum := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · rw [Nat.digits_base_mul hp hm, List.sum_cons, Nat.zero_add]

/-- Renormalizing an arbitrary (possibly overflowing) digit list into canonical base-`p`
digits only lowers the total digit sum. -/
theorem sum_digits_ofDigits_le [hp : Fact p.Prime] (l : List ℕ) :
    (p.digits (Nat.ofDigits p l)).sum ≤ l.sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [Nat.ofDigits_cons, List.sum_cons]
    calc (p.digits (a + p * Nat.ofDigits p t)).sum
        ≤ (p.digits a).sum + (p.digits (p * Nat.ofDigits p t)).sum := sum_digits_add_le p a _
      _ = (p.digits a).sum + (p.digits (Nat.ofDigits p t)).sum := by
          rw [sum_digits_base_mul p hp.out.one_lt]
      _ ≤ a + t.sum := add_le_add (sum_digits_le_self p hp.out.one_lt.le a) ih

/-- `ofDigits` of a list built by mapping over `List.range`. -/
theorem ofDigits_map_range (f : ℕ → ℕ) (L : ℕ) :
    Nat.ofDigits p ((List.range L).map f) = ∑ j ∈ range L, f j * p ^ j := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [List.range_succ, List.map_append, Nat.ofDigits_append, ih, Finset.sum_range_succ]
    simp only [List.length_map, List.length_range, List.map_cons, List.map_nil,
      Nat.ofDigits_singleton]
    ring

/-- `ofDigits` as a `getD`-weighted sum over any window covering the list. -/
theorem ofDigits_eq_sum_getD (l : List ℕ) {L : ℕ} (h : l.length ≤ L) :
    Nat.ofDigits p l = ∑ j ∈ range L, l.getD j 0 * p ^ j := by
  induction l generalizing L with
  | nil => simp
  | cons a t ih =>
    obtain ⟨L', rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by simp at h; omega⟩
    rw [Finset.sum_range_succ', Nat.ofDigits_cons]
    simp only [List.getD_cons_succ, List.getD_cons_zero, pow_zero, mul_one]
    rw [ih (by simpa using h), Finset.mul_sum]
    have key : ∀ j, p * (t.getD j 0 * p ^ j) = t.getD j 0 * p ^ (j + 1) := fun j => by ring
    rw [Finset.sum_congr rfl fun j _ => key j]
    omega

/-- The list sum as a `getD`-sum over any window covering the list. -/
theorem sum_eq_sum_getD (l : List ℕ) {L : ℕ} (h : l.length ≤ L) :
    l.sum = ∑ j ∈ range L, l.getD j 0 := by
  have h1 := ofDigits_eq_sum_getD 1 l h
  simpa [Nat.ofDigits_one] using h1

/-! ### Fractional digit expansions

A finitely supported `d : ℕ →₀ ℕ` models the fractional expansion
`0.d₀d₁d₂… = ∑ i, dᵢ p^{-(i+1)}` (the digit `dᵢ` sits at value `p^{-(i+1)}`).  The
defining sum is syntactically the inner sum of `Sabc`. -/

/-- The value `∑ i, dᵢ · p^{-(i+1)} ∈ ℚ` of a fractional digit expansion.  This is
syntactically the inner sum appearing in `Sabc`. -/
def fracVal (d : ℕ →₀ ℕ) : ℚ :=
  d.sum fun i v => (v : ℚ) * (p : ℚ) ^ (-(i + 1 : ℤ))

/-- Rewriting lemma matching the inner sum of `Sabc` to `fracVal`. -/
theorem fracVal_def (d : ℕ →₀ ℕ) :
    (d.sum fun i v => (v : ℚ) * (p : ℚ) ^ (-(i + 1 : ℤ))) = fracVal p d := rfl

@[simp] theorem fracVal_zero : fracVal p 0 = 0 :=
  Finsupp.sum_zero_index

theorem fracVal_add (d e : ℕ →₀ ℕ) : fracVal p (d + e) = fracVal p d + fracVal p e :=
  Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by push_cast; ring)

theorem fracVal_single (i v : ℕ) :
    fracVal p (Finsupp.single i v) = (v : ℚ) * (p : ℚ) ^ (-(i + 1 : ℤ)) :=
  Finsupp.sum_single_index (by simp)

theorem fracVal_nonneg (d : ℕ →₀ ℕ) : 0 ≤ fracVal p d :=
  Finsupp.sum_nonneg fun _ _ =>
    mul_nonneg (Nat.cast_nonneg _) (zpow_nonneg (Nat.cast_nonneg _) _)

/-- A nonzero digit expansion has positive fractional value. -/
theorem fracVal_pos (hp : 0 < p) {d : ℕ →₀ ℕ} (hd : d ≠ 0) : 0 < fracVal p d := by
  obtain ⟨i, hi⟩ : ∃ i, d i ≠ 0 := by
    by_contra h
    push Not at h
    exact hd (Finsupp.ext h)
  have hp0 : (0 : ℚ) < (p : ℚ) := by exact_mod_cast hp
  rw [fracVal, Finsupp.sum]
  refine Finset.sum_pos'
    (fun j _ => mul_nonneg (Nat.cast_nonneg _) (zpow_nonneg (Nat.cast_nonneg _) _))
    ⟨i, Finsupp.mem_support_iff.mpr hi, ?_⟩
  have h1 : (1 : ℚ) ≤ (d i : ℚ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hi
  have h2 : (0 : ℚ) < (p : ℚ) ^ (-(i + 1 : ℤ)) := zpow_pos hp0 _
  nlinarith

theorem fracVal_eq_sum_range (d : ℕ →₀ ℕ) {L : ℕ} (h : d.support ⊆ range L) :
    fracVal p d = ∑ i ∈ range L, (d i : ℚ) * (p : ℚ) ^ (-(i + 1 : ℤ)) :=
  Finsupp.sum_of_support_subset d h _ (fun i _ => by simp)

-- The `unusedTactic` linter misreports the `push_cast` below (it rewrites only under the
-- `∑` binder), but the proof breaks without it.
set_option linter.unusedTactic false in
/-- **Bridge to ℕ**: over a window `[0, L)` containing the support, `p^L` times the
fractional value is the `ofDigits` value of the reversed digit list. -/
theorem fracVal_mul_pow (hp : 0 < p) (d : ℕ →₀ ℕ) {L : ℕ} (h : d.support ⊆ range L) :
    fracVal p d * (p : ℚ) ^ L
      = ((Nat.ofDigits p ((List.range L).map fun j => d (L - 1 - j)) : ℕ) : ℚ) := by
  have hstep : ∀ i ∈ range L,
      (d i : ℚ) * (p : ℚ) ^ (-(i + 1 : ℤ)) * (p : ℚ) ^ L
        = (d i : ℚ) * (p : ℚ) ^ (L - 1 - i : ℕ) := by
    intro i hi
    rw [mem_range] at hi
    rw [mul_assoc]
    congr 1
    rw [← zpow_natCast (p : ℚ) L, ← zpow_add₀ (by exact_mod_cast hp.ne'),
      ← zpow_natCast (p : ℚ) (L - 1 - i)]
    congr 1
    push_cast
    omega
  rw [fracVal_eq_sum_range p d h, Finset.sum_mul, Finset.sum_congr rfl hstep,
    ← Finset.sum_range_reflect, ofDigits_map_range]
  push_cast
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [mem_range] at hj
  have hexp : L - 1 - (L - 1 - j) = j := by omega
  rw [hexp]

/-- A canonical expansion (all digits `< p`) has fractional value less than `1`. -/
theorem fracVal_lt_one (hp : 1 < p) {d : ℕ →₀ ℕ} (hd : ∀ i, d i < p) :
    fracVal p d < 1 := by
  obtain ⟨L, hL⟩ := d.support.exists_nat_subset_range
  have hb := fracVal_mul_pow p (by omega) d hL
  have hV : Nat.ofDigits p ((List.range L).map fun j => d (L - 1 - j)) < p ^ L := by
    have hlt := Nat.ofDigits_lt_base_pow_length (l := (List.range L).map fun j => d (L - 1 - j))
      hp (by rintro x hx; obtain ⟨j, -, rfl⟩ := List.mem_map.mp hx; exact hd _)
    simpa using hlt
  have hpL : (0 : ℚ) < (p : ℚ) ^ L := by positivity
  have hdiv : fracVal p d = ((Nat.ofDigits p ((List.range L).map fun j => d (L - 1 - j)) : ℕ) : ℚ)
      / (p : ℚ) ^ L := by
    rw [eq_div_iff hpL.ne']
    exact hb
  rw [hdiv, div_lt_one hpL]
  exact_mod_cast hV

/-- Digit extraction from `ofDigits`: for a list of digits `< p`, the `j`-th digit is
recovered from the value by `/ p^j % p`. -/
theorem ofDigits_div_pow_mod (hp : 1 < p) (l : List ℕ) (hl : ∀ x ∈ l, x < p) :
    ∀ j : ℕ, Nat.ofDigits p l / p ^ j % p = l.getD j 0 := by
  induction l with
  | nil => intro j; simp
  | cons a t ih =>
    intro j
    have ha : a < p := hl a List.mem_cons_self
    cases j with
    | zero =>
      rw [Nat.ofDigits_cons, pow_zero, Nat.div_one, List.getD_cons_zero,
        Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha]
    | succ j =>
      have hdiv : (a + p * Nat.ofDigits p t : ℕ) / p ^ (j + 1)
          = Nat.ofDigits p t / p ^ j := by
        rw [pow_succ', ← Nat.div_div_eq_div_mul,
          Nat.add_mul_div_left a _ (by omega : 0 < p), Nat.div_eq_of_lt ha, zero_add]
      rw [Nat.ofDigits_cons, hdiv, List.getD_cons_succ]
      exact ih (fun x hx => hl x (List.mem_cons_of_mem a hx)) j

/-- `getD` of a list built by mapping over `List.range`. -/
theorem getD_range_map (f : ℕ → ℕ) {L j : ℕ} (h : j < L) :
    ((List.range L).map f).getD j 0 = f j := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range h]
  rfl

/-- **Canonical fractional expansions are unique**: a finitely supported digit function
with all digits `< p` is determined by its fractional value. -/
theorem eq_of_fracVal_eq (hp : 1 < p) {d e : ℕ →₀ ℕ} (hd : ∀ i, d i < p)
    (he : ∀ i, e i < p) (h : fracVal p d = fracVal p e) : d = e := by
  obtain ⟨L, hL⟩ := (d.support ∪ e.support).exists_nat_subset_range
  have hdL : d.support ⊆ range L := Finset.union_subset_iff.mp hL |>.1
  have heL : e.support ⊆ range L := Finset.union_subset_iff.mp hL |>.2
  have hd' := fracVal_mul_pow p (by omega) d hdL
  have he' := fracVal_mul_pow p (by omega) e heL
  rw [h] at hd'
  have hV : Nat.ofDigits p ((List.range L).map fun j => d (L - 1 - j))
      = Nat.ofDigits p ((List.range L).map fun j => e (L - 1 - j)) := by
    exact_mod_cast hd'.symm.trans he'
  have hld : ∀ x ∈ (List.range L).map fun j => d (L - 1 - j), x < p := by
    rintro x hx
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hx
    exact hd _
  have hle : ∀ x ∈ (List.range L).map fun j => e (L - 1 - j), x < p := by
    rintro x hx
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hx
    exact he _
  ext i
  by_cases hiL : i < L
  · have hji : L - 1 - (L - 1 - i) = i := by omega
    have h1 := ofDigits_div_pow_mod p hp _ hld (L - 1 - i)
    have h2 := ofDigits_div_pow_mod p hp _ hle (L - 1 - i)
    rw [getD_range_map _ (by omega), hji] at h1 h2
    rw [← h1, ← h2, hV]
  · have h1 : d i = 0 := Finsupp.notMem_support_iff.mp
      (fun hmem => hiL (Finset.mem_range.mp (hdL hmem)))
    have h2 : e i = 0 := Finsupp.notMem_support_iff.mp
      (fun hmem => hiL (Finset.mem_range.mp (heL hmem)))
    rw [h1, h2]

/-- The canonical digit finsupp of `C / p^L` for `C < p^L`: position `i` (of value
`p^{-(i+1)}`) carries the `(L-1-i)`-th base-`p` digit of `C`. -/
noncomputable def digitFinsupp (C L : ℕ) : ℕ →₀ ℕ :=
  Finsupp.onFinset (range L) (fun i => if i < L then C / p ^ (L - 1 - i) % p else 0)
    (fun i hi => by
      rw [mem_range]
      by_contra h
      rw [if_neg h] at hi
      exact hi rfl)

theorem digitFinsupp_lt (hp : 0 < p) (C L i : ℕ) : digitFinsupp p C L i < p := by
  simp only [digitFinsupp, Finsupp.onFinset_apply]
  split
  · exact Nat.mod_lt _ hp
  · exact hp

theorem digitFinsupp_support_subset (C L : ℕ) : (digitFinsupp p C L).support ⊆ range L :=
  Finsupp.support_onFinset_subset

/-- The digit sum of the canonical digit finsupp is the base-`p` digit sum of `C`. -/
theorem digitFinsupp_sum (hp : 1 < p) {C L : ℕ} (hC : C < p ^ L) :
    ((digitFinsupp p C L).sum fun _ v => v) = (p.digits C).sum := by
  rw [Finsupp.sum_of_support_subset _ (digitFinsupp_support_subset p C L) _ (fun _ _ => rfl)]
  have happ : ∀ i ∈ range L, digitFinsupp p C L i = C / p ^ (L - 1 - i) % p := by
    intro i hi
    rw [mem_range] at hi
    simp only [digitFinsupp, Finsupp.onFinset_apply, if_pos hi]
  rw [Finset.sum_congr rfl happ, Finset.sum_range_reflect (fun j => C / p ^ j % p) L]
  have hgetD : ∀ j ∈ range L, C / p ^ j % p = (p.digits C).getD j 0 := fun j _ =>
    (Nat.getD_digits C j hp).symm
  rw [Finset.sum_congr rfl hgetD]
  exact (sum_eq_sum_getD _ ((Nat.digits_length_le_iff hp C).mpr hC)).symm

/-- The fractional value of the canonical digit finsupp of `C < p^L` is `C / p^L`. -/
theorem fracVal_digitFinsupp_mul_pow (hp : 1 < p) {C L : ℕ} (hC : C < p ^ L) :
    fracVal p (digitFinsupp p C L) * (p : ℚ) ^ L = (C : ℚ) := by
  rw [fracVal_mul_pow p (by omega) _ (digitFinsupp_support_subset p C L)]
  norm_cast
  rw [ofDigits_map_range]
  have happ : ∀ j ∈ range L,
      digitFinsupp p C L (L - 1 - j) * p ^ j = (p.digits C).getD j 0 * p ^ j := by
    intro j hj
    rw [mem_range] at hj
    have h1 : L - 1 - j < L := by omega
    have h2 : L - 1 - (L - 1 - j) = j := by omega
    simp only [digitFinsupp, Finsupp.onFinset_apply, if_pos h1, h2, Nat.getD_digits C j hp]
  rw [Finset.sum_congr rfl happ,
    ← ofDigits_eq_sum_getD p _ ((Nat.digits_length_le_iff hp C).mpr hC),
    Nat.ofDigits_digits]

/-- **Carry normalization.**  Any finitely supported pseudo-digit expansion `e` (entries
allowed to exceed `p`) has value `k + fracVal d` where `k ∈ ℕ` is the integer carry and
`d` is a canonical expansion (digits `< p`); moreover carrying only lowers the total digit
sum: `S_p(k) + Σ d ≤ Σ e`. -/
theorem exists_carry_normalization [hp : Fact p.Prime] (e : ℕ →₀ ℕ) :
    ∃ (k : ℕ) (d : ℕ →₀ ℕ), (∀ i, d i < p) ∧
      (p.digits k).sum + (d.sum fun _ v => v) ≤ (e.sum fun _ v => v) ∧
      fracVal p e = (k : ℚ) + fracVal p d := by
  have hp1 : 1 < p := hp.out.one_lt
  obtain ⟨L, hL⟩ := e.support.exists_nat_subset_range
  set l : List ℕ := (List.range L).map fun j => e (L - 1 - j) with hl
  set V : ℕ := Nat.ofDigits p l with hV
  set dl : List ℕ := p.digits V with hdl
  set C : ℕ := Nat.ofDigits p (dl.take L) with hC
  set k : ℕ := Nat.ofDigits p (dl.drop L) with hk
  -- The truncation `C` is an honest `L`-digit number.
  have hCp : C < p ^ L := by
    have h1 : C < p ^ (dl.take L).length :=
      Nat.ofDigits_lt_base_pow_length hp1
        (fun x hx => Nat.digits_lt_base hp1 (List.mem_of_mem_take hx))
    exact h1.trans_le (Nat.pow_le_pow_right (by omega) (by simp))
  -- Splitting the digit list of `V` at position `L`: `V = C + p^L * k`.
  have hsplit : V = C + p ^ L * k := by
    by_cases hlen : dl.length ≤ L
    · have hdrop : dl.drop L = [] := List.drop_eq_nil_of_le hlen
      have htake : dl.take L = dl := List.take_of_length_le hlen
      rw [hC, hk, hdrop, htake, hdl, Nat.ofDigits_digits]
      simp
    · have hlen' : (dl.take L).length = L := by
        rw [List.length_take]
        omega
      have h1 : Nat.ofDigits p (dl.take L ++ dl.drop L) = C + p ^ L * k := by
        rw [Nat.ofDigits_append, hlen', hC, hk]
      rw [List.take_append_drop, hdl, Nat.ofDigits_digits] at h1
      exact h1
  -- Digit-sum bookkeeping: `S_p(C) + S_p(k) = S_p(V) ≤ l.sum = Σ e`.
  have hSC : (p.digits C).sum = (dl.take L).sum :=
    Nat.sum_digits_ofDigits_eq_sum hp1
      ⟨rfl, fun x hx => Nat.digits_lt_base hp1 (List.mem_of_mem_take hx)⟩
  have hSk : (p.digits k).sum = (dl.drop L).sum :=
    Nat.sum_digits_ofDigits_eq_sum hp1
      ⟨rfl, fun x hx => Nat.digits_lt_base hp1 (List.mem_of_mem_drop hx)⟩
  have hSV : (dl.take L).sum + (dl.drop L).sum = (p.digits V).sum := by
    rw [← List.sum_append, List.take_append_drop]
  have hVle : (p.digits V).sum ≤ l.sum := sum_digits_ofDigits_le p l
  have hlsum : l.sum = (e.sum fun _ v => v) := by
    have h1 : l.sum = Nat.ofDigits 1 l := (Nat.ofDigits_one l).symm
    rw [h1, hl, ofDigits_map_range]
    simp only [one_pow, mul_one]
    rw [Finset.sum_range_reflect (fun i => e i) L]
    exact (Finsupp.sum_of_support_subset e hL (fun _ v => v) (fun _ _ => rfl)).symm
  -- Value bookkeeping, after scaling by `p^L`.
  have hpLne : ((p : ℚ) ^ L) ≠ 0 := by positivity
  have hval : fracVal p e * (p : ℚ) ^ L
      = ((k : ℚ) + fracVal p (digitFinsupp p C L)) * (p : ℚ) ^ L := by
    rw [fracVal_mul_pow p (by omega) e hL, ← hl, ← hV, add_mul,
      fracVal_digitFinsupp_mul_pow p hp1 hCp, hsplit]
    push_cast
    ring
  refine ⟨k, digitFinsupp p C L, fun i => digitFinsupp_lt p (by omega) C L i, ?_, ?_⟩
  · rw [digitFinsupp_sum p hp1 hCp, hSC, hSk, ← hlsum]
    omega
  · exact mul_right_cancel₀ hpLne hval

/-! ### Digit sums of quotients: the division-by-`k` dichotomy

Dividing a base-`p` digit string that vanishes on a widening gap by an integer `k`
coprime to `p` either terminates exactly (when `k` divides both the head and the tail
numerators separately), or the remainder cycles through a nonzero orbit across the gap
and deposits a nonzero quotient digit at least once every `k` positions, forcing the
digit sum of the quotient to grow linearly with the gap length.  These lemmas are the
arithmetic engine behind the slice-width upgrade for UP series (`lem:up-rescale`). -/

/-- **Remainder-orbit lemma.**  If `k ∤ A` and `k` is coprime to `p`, the base-`p` digit
stream of the quotients `A p^d / k` never stays zero for `k` consecutive positions:
a vanishing digit means the remainder is multiplied exactly by `p`, and `k` consecutive
exact multiplications would force `p^k · r < k` for a remainder `r ≥ 1`, contradicting
`p^k > k`. -/
theorem exists_digit_div_ne_zero (hp : 1 < p) {k A : ℕ} (hcop : Nat.Coprime p k)
    (hkA : ¬ k ∣ A) (d₀ : ℕ) :
    ∃ d, d₀ < d ∧ d ≤ d₀ + k ∧ (A * p ^ d / k) % p ≠ 0 := by
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [Nat.coprime_zero_right] at hcop
    omega
  by_contra hzero
  push Not at hzero
  -- All digits in the window vanish, so each step multiplies the remainder exactly by `p`.
  set r : ℕ → ℕ := fun i => A * p ^ i % k with hr
  have hrlt : ∀ i, r i < k := fun i => Nat.mod_lt _ (by omega)
  have hrne : ∀ i, r i ≠ 0 := by
    intro i h
    have hdvd : k ∣ A * p ^ i := Nat.dvd_of_mod_eq_zero h
    exact hkA ((Nat.Coprime.pow_right i hcop.symm).dvd_of_dvd_mul_right hdvd)
  have hstep : ∀ i, (A * p ^ (i + 1) / k) % p = 0 → r (i + 1) = p * r i := by
    intro i hdig
    have hsplit : A * p ^ (i + 1) = k * (p * (A * p ^ i / k)) + p * r i := by
      have := Nat.div_add_mod (A * p ^ i) k
      calc A * p ^ (i + 1) = p * (A * p ^ i) := by ring
        _ = p * (k * (A * p ^ i / k) + r i) := by rw [this]
        _ = k * (p * (A * p ^ i / k)) + p * r i := by ring
    have hdiv : A * p ^ (i + 1) / k = p * (A * p ^ i / k) + p * r i / k := by
      rw [hsplit, Nat.mul_add_div (by omega)]
    have hql : p * r i / k < p := by
      rw [Nat.div_lt_iff_lt_mul (by omega : 0 < k)]
      exact mul_lt_mul_of_pos_left (hrlt i) (by omega : (0 : ℕ) < p)
    have hq0 : p * r i / k = 0 := by
      have h := hdig
      rw [hdiv, Nat.mul_add_mod, Nat.mod_eq_of_lt hql] at h
      exact h
    have hlt : p * r i < k := (Nat.div_eq_zero_iff.mp hq0).resolve_left (by omega)
    have hmod : A * p ^ (i + 1) % k = (p * r i) % k := by
      rw [hsplit, Nat.mul_add_mod]
    rw [hr]
    simp only
    rw [hmod, Nat.mod_eq_of_lt hlt]
  -- Iterate across the gap window.
  have hiter : ∀ t, t ≤ k → r (d₀ + t) = p ^ t * r d₀ := by
    intro t ht
    induction t with
    | zero => simp
    | succ t ih =>
      have hd : d₀ < d₀ + t + 1 := by omega
      have hd' : d₀ + t + 1 ≤ d₀ + k := by omega
      have h1 := hstep (d₀ + t) (hzero (d₀ + t + 1) hd hd')
      rw [show d₀ + (t + 1) = d₀ + t + 1 by omega, h1, ih (by omega)]
      ring
  have hfinal := hiter k le_rfl
  have hge : p ^ k ≤ p ^ k * r d₀ := by
    calc p ^ k = p ^ k * 1 := (mul_one _).symm
      _ ≤ p ^ k * r d₀ := Nat.mul_le_mul_left _ (Nat.pos_of_ne_zero (hrne d₀))
  have hpk : k + 1 ≤ p ^ k := by
    have h2 : k < 2 ^ k := Nat.lt_two_pow_self
    have h3 : 2 ^ k ≤ p ^ k := Nat.pow_le_pow_left (by omega) k
    omega
  have := hrlt (d₀ + k)
  omega

/-- The base-`p` digit sum of `Q` dominates the sum of the extracted digits
`Q / p^s % p` over any finite set of places. -/
theorem sum_div_pow_mod_le_digits_sum (hp : 1 < p) (Q : ℕ) (P : Finset ℕ) :
    ∑ s ∈ P, Q / p ^ s % p ≤ (p.digits Q).sum := by
  set L : ℕ := max (p.digits Q).length (P.sup id + 1) with hL
  have hlen : (p.digits Q).length ≤ L := le_max_left _ _
  have hPL : P ⊆ range L := by
    intro s hs
    rw [mem_range]
    exact lt_of_le_of_lt (Finset.le_sup (f := id) hs) (by omega)
  have hsum : (p.digits Q).sum = ∑ s ∈ range L, Q / p ^ s % p := by
    rw [sum_eq_sum_getD (p.digits Q) hlen]
    exact Finset.sum_congr rfl fun s _ => Nat.getD_digits Q s hp
  rw [hsum]
  exact Finset.sum_le_sum_of_subset hPL

/-- Multiplying by a power of the base preserves the base-`p` digit sum. -/
theorem sum_digits_pow_mul (hp : 1 < p) (t m : ℕ) :
    (p.digits (p ^ t * m)).sum = (p.digits m).sum := by
  induction t with
  | zero => simp
  | succ t ih => rw [pow_succ', mul_assoc, sum_digits_base_mul p hp, ih]

/-- **Digit-sum growth for inexact division.**  If `k` is coprime to `p`, `k ∤ A` and
`G < p^m`, then whatever the gap length `n ≥ k(c+1)`, the base-`p` digit sum of
`(A p^{m+n} + G) / k` exceeds `c`: the quotient digits across the gap window come from
the nonzero remainder orbit of `A`, which deposits a nonzero digit at least once every
`k` positions. -/
theorem le_digits_sum_div_of_not_dvd (hp : 1 < p) {k A G m c n : ℕ}
    (hcop : Nat.Coprime p k) (hkA : ¬ k ∣ A) (hG : G < p ^ m)
    (hn : k * (c + 1) ≤ n) :
    c + 1 ≤ (p.digits ((A * p ^ (m + n) + G) / k)).sum := by
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [Nat.coprime_zero_right] at hcop
    omega
  set T : ℕ := k with hT
  have hT1 : 1 ≤ T := by omega
  set Q : ℕ := (A * p ^ (m + n) + G) / k with hQ
  -- Pick one witness digit in each length-`T` window of the gap.
  have hex : ∀ i : ℕ, ∃ d, i * T < d ∧ d ≤ i * T + T ∧ (A * p ^ d / k) % p ≠ 0 :=
    fun i => exists_digit_div_ne_zero p hp hcop hkA (i * T)
  choose f hf1 hf2 hf3 using hex
  -- Each witness digit of the orbit is literally a digit of `Q` at place `m + n - f i`.
  have hfn : ∀ i, i ≤ c → f i ≤ n := fun i hi =>
    (hf2 i).trans (by calc i * T + T = (i + 1) * T := by ring
      _ ≤ (c + 1) * T := Nat.mul_le_mul_right T (by omega)
      _ ≤ n := by rw [mul_comm]; exact hn)
  have hdigit : ∀ i, i ≤ c → Q / p ^ (m + n - f i) % p = (A * p ^ (f i) / k) % p := by
    intro i hi
    have hfi : f i ≤ n := hfn i hi
    set s : ℕ := m + n - f i with hs
    have hsm : m ≤ s := by omega
    have hsplit : A * p ^ (m + n) + G = p ^ s * (A * p ^ (f i)) + G := by
      have hexp : m + n = s + f i := by omega
      rw [hexp, pow_add]
      ring
    have hGz : G / p ^ s = 0 :=
      Nat.div_eq_of_lt (hG.trans_le (Nat.pow_le_pow_right (by omega) hsm))
    have hdivs : Q / p ^ s = A * p ^ (f i) / k := by
      rw [hQ, Nat.div_div_eq_div_mul, mul_comm k (p ^ s), ← Nat.div_div_eq_div_mul,
        hsplit, Nat.mul_add_div (by positivity), hGz, add_zero]
    rw [hdivs]
  -- The witness places are pairwise distinct, giving `c + 1` nonzero digits of `Q`.
  set P : Finset ℕ := (range (c + 1)).image (fun i => m + n - f i) with hP
  have hinj : Set.InjOn (fun i => m + n - f i) (range (c + 1)) := by
    intro i hi i' hi' h
    rw [coe_range, Set.mem_Iio] at hi hi'
    by_contra hne
    -- distinct indices give witnesses in disjoint windows
    wlog hlt : i < i' generalizing i i'
    · exact this hi' hi h.symm (Ne.symm hne) (by omega)
    have h1 : f i ≤ i * T + T := hf2 i
    have h2 : i' * T < f i' := hf1 i'
    have h3 : i * T + T ≤ i' * T := by
      calc i * T + T = (i + 1) * T := by ring
        _ ≤ i' * T := Nat.mul_le_mul_right T (by omega)
    have h4 : f i ≤ n := hfn i (by omega)
    have h5 : f i' ≤ n := hfn i' (by omega)
    simp only at h
    omega
  have hcard : P.card = c + 1 := by
    rw [hP, Finset.card_image_of_injOn hinj, Finset.card_range]
  have hone : ∀ s ∈ P, 1 ≤ Q / p ^ s % p := by
    intro s hs
    rw [hP, Finset.mem_image] at hs
    obtain ⟨i, hi, rfl⟩ := hs
    rw [mem_range] at hi
    rw [hdigit i (by omega)]
    exact Nat.one_le_iff_ne_zero.mpr (hf3 i)
  calc c + 1 = ∑ _s ∈ P, 1 := by rw [Finset.sum_const, hcard, smul_eq_mul, mul_one]
    _ ≤ ∑ s ∈ P, Q / p ^ s % p := Finset.sum_le_sum hone
    _ ≤ (p.digits Q).sum := sum_div_pow_mod_le_digits_sum p hp Q P

/-- If `C < p^{L-t}`, the canonical digit finsupp of `C / p^L` is supported in
`[t, L)`: small numerators only occupy the low places. -/
theorem digitFinsupp_support_subset_Ico (hp : 1 < p) {C L t : ℕ} (hC : C < p ^ (L - t)) :
    (digitFinsupp p C L).support ⊆ Finset.Ico t L := by
  intro i hi
  have hiL : i < L := mem_range.mp (digitFinsupp_support_subset p C L hi)
  rw [Finset.mem_Ico]
  refine ⟨?_, hiL⟩
  by_contra hit
  push Not at hit
  have hne : digitFinsupp p C L i ≠ 0 := Finsupp.mem_support_iff.mp hi
  have happ : digitFinsupp p C L i = C / p ^ (L - 1 - i) % p := by
    simp only [digitFinsupp, Finsupp.onFinset_apply, if_pos hiL]
  have hdivne : C / p ^ (L - 1 - i) ≠ 0 := by
    intro h
    rw [happ, h] at hne
    exact hne (Nat.zero_mod p)
  have hle : p ^ (L - 1 - i) ≤ C := by
    by_contra hlt
    exact hdivne (Nat.div_eq_of_lt (by omega))
  have hmono : p ^ (L - t) ≤ p ^ (L - 1 - i) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  omega

end TrustworthyKedlaya.UP
