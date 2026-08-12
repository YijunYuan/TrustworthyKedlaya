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

end TrustworthyKedlaya.UP
