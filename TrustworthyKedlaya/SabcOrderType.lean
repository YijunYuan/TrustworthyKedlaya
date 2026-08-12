/-
Copyright (c) 2026 Shanwen Wang, Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import TrustworthyKedlaya.SupportSets
public import Mathlib.SetTheory.Ordinal.Exponential

/-!
# Order-type bounds for the support sets `S_{a,b,c}`

Kedlaya (2001b), Section 4: the support sets `S_{a,b,c}` are not just well-ordered but of
uniformly small order type.

- `TrustworthyKedlaya.UP.typeLT_Sabc_inter_Iic_lt`: for every cutoff `R`, the order type of
  `S_{a,b,c} ∩ (-∞, R]` is less than `ω^(c+2)`.
- `TrustworthyKedlaya.UP.typeLT_le_omega0_opow_omega0`: consequently a well-ordered subset
  of `ℚ` which is, for every `n ∈ ℕ`, contained in some `S_{aₙ,bₙ,cₙ} ∪ (n, ∞)` has order
  type at most `ω^ω`.

The first bound is a rank-function argument.  A point `s` of `S_{a,b,c} ∩ (-∞, R]` has a
unique presentation `a·s = n - fracVal d` with `n ∈ ℤ`, `n ≥ -b`, and `d` a canonical digit
expansion (digits `< p`, digit sum `≤ c`); the rank

`Ψ(s) = ω^(c+1)·(2(n+b)+1) + digitRank c d`

is strictly monotone and bounded by `ω^(c+1)·(2(⌊aR⌋+1+b)+2) < ω^(c+2)`.  Here
`digitRank c d` recursively peels the leading (most significant) digit of `d`: larger
fractional values have lexicographically larger digit strings, hence smaller ranks, and a
digit expansion of digit sum `≤ c` always has rank `≤ ω^(c+1)`.

For the second bound, every proper initial segment `{y ∈ S : y < x}` of such a set `S` is
contained in `S_{a,b,c} ∩ (-∞, ⌈x⌉]` for suitable parameters, so has order type `< ω^ω`;
the order type of `S` is then at most `ω^ω` because the type of an initial segment cut at
`x ∈ S` is strictly below the type of `S`.

## References

- K. S. Kedlaya, *The algebraic closure of the power series field in positive
  characteristic*, Proc. Amer. Math. Soc. 129 (2001) [Ked01b], Section 4.
-/

@[expose] public section

open Ordinal

/-! ### Generic order-type tooling

Mathlib's `Ordinal.type_mono` compares order types of subsets only inside a globally
well-founded ambient order.  For well-founded subsets of `ℚ` we need the relative
versions: a subset that is well-founded in its own right has a `typeLT`, strictly
monotone maps bound it, and cutting at an element strictly decreases it. -/

/-- A set that is well-founded under `<` is a well-founded order in its own right. -/
theorem Set.IsWF.wellFoundedLT {α : Type*} [Preorder α] {s : Set α} (hs : s.IsWF) :
    WellFoundedLT ↥s := by
  refine ⟨?_⟩
  have h : WellFounded (Function.onFun (fun x y : α => x < y) (Subtype.val : s → α)) :=
    (Set.wellFoundedOn_range (f := (Subtype.val : s → α)) (r := (· < ·))).mp
      (by simpa [Set.IsWF] using hs)
  change WellFounded (fun x y : ↥s => x.1 < y.1)
  exact h

/-- **Order types of subsets via strictly monotone maps.**  A strictly monotone map from
`↥s` into a well-founded linear order `γ` bounds the order type of `s` by that of `γ`. -/
theorem Ordinal.typeLT_set_le_of_strictMono {α γ : Type u} [LinearOrder α] [LinearOrder γ]
    [WellFoundedLT γ] {s : Set α} [WellFoundedLT ↥s] (f : ↥s → γ)
    (hf : StrictMono f) : typeLT ↥s ≤ typeLT γ :=
  Ordinal.type_le_iff'.mpr ⟨⟨⟨f, hf.injective⟩, hf.lt_iff_lt⟩⟩

/-- **Order types of subsets via ordinal-valued ranks.**  A strictly monotone rank
function on `↥s` with values below `β` bounds the order type of `s` by `β`. -/
theorem Ordinal.typeLT_set_le_of_rank {α : Type u} [LinearOrder α] {s : Set α}
    [WellFoundedLT ↥s] {β : Ordinal.{u}} (ψ : ↥s → Ordinal.{u}) (hψ : StrictMono ψ)
    (hβ : ∀ x, ψ x < β) : typeLT ↥s ≤ β := by
  have h := Ordinal.typeLT_set_le_of_strictMono (γ := β.ToType)
    (fun x => Ordinal.ToType.mk ⟨ψ x, hβ x⟩)
    (fun x y hxy => Ordinal.ToType.mk.lt_iff_lt.mpr (by exact hψ hxy))
  rwa [Ordinal.type_toType] at h

/-- **Cutting a well-founded set at one of its elements strictly lowers the order
type.**  This is the set-level counterpart of `Ordinal.typein_lt_type`. -/
theorem Ordinal.typeLT_inter_Iio_lt {α : Type u} [LinearOrder α] {t : Set α} {x : α}
    [WellFoundedLT ↥t] [WellFoundedLT ↥(t ∩ Set.Iio x)] (hx : x ∈ t) :
    typeLT ↥(t ∩ Set.Iio x) < typeLT ↥t := by
  refine PrincipalSeg.ordinal_type_lt
    (@PrincipalSeg.mk ↥(t ∩ Set.Iio x) ↥t (· < ·) (· < ·)
      ⟨⟨Set.inclusion Set.inter_subset_left, Set.inclusion_injective _⟩, Iff.rfl⟩
      ⟨x, hx⟩ fun b => ?_)
  · constructor
    · rintro ⟨a, rfl⟩
      exact a.2.2
    · intro hb
      exact ⟨⟨b.1, b.2, hb⟩, rfl⟩

namespace TrustworthyKedlaya.UP

variable (p : ℕ)

/-! ### The leading digit and the digit rank -/

/-- The leading (most significant) digit position of a fractional expansion: the smallest
element of the support (`0` for the zero expansion, by convention). -/
def leadPos (d : ℕ →₀ ℕ) : ℕ := d.support.min.getD 0

theorem leadPos_mem {d : ℕ →₀ ℕ} (hd : d ≠ 0) : leadPos d ∈ d.support := by
  obtain ⟨j, hj⟩ := Finset.min_of_nonempty (Finsupp.support_nonempty_iff.mpr hd)
  rw [leadPos, hj]
  exact Finset.mem_of_min hj

theorem leadPos_le {d : ℕ →₀ ℕ} {i : ℕ} (hi : i ∈ d.support) : leadPos d ≤ i := by
  obtain ⟨j, hj⟩ := Finset.min_of_nonempty ⟨i, hi⟩
  rw [leadPos, hj]
  exact Finset.min_le_of_eq hi hj

theorem leadPos_pos {d : ℕ →₀ ℕ} (hd : d ≠ 0) : 1 ≤ d (leadPos d) :=
  Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp (leadPos_mem hd))

theorem apply_eq_zero_of_lt_leadPos {d : ℕ →₀ ℕ} {i : ℕ} (hi : i < leadPos d) :
    d i = 0 := by
  by_contra h
  exact absurd (leadPos_le (Finsupp.mem_support_iff.mpr h)) (by omega)

/-- Peeling off the digit at any position `j`. -/
theorem fracVal_eq_apply_add_erase (j : ℕ) (d : ℕ →₀ ℕ) :
    fracVal p d = (d j : ℚ) * (p : ℚ) ^ (-(j + 1 : ℤ)) + fracVal p (d.erase j) := by
  conv_lhs => rw [← Finsupp.single_add_erase j d]
  rw [fracVal_add, fracVal_single]

/-- Canonical expansions vanishing below position `k` have value less than `p^{-k}`. -/
theorem fracVal_lt_zpow_neg (hp : 1 < p) :
    ∀ (k : ℕ) (d : ℕ →₀ ℕ), (∀ i, d i < p) → (∀ i < k, d i = 0) →
      fracVal p d < (p : ℚ) ^ (-(k : ℤ)) := by
  intro k
  induction k with
  | zero =>
    intro d hd _
    simpa using fracVal_lt_one p hp hd
  | succ k ih =>
    intro d hd hzero
    have hppos : (0 : ℚ) < (p : ℚ) := by exact_mod_cast (by omega : 0 < p)
    have hshift := p_mul_fracVal p (by omega) d
    rw [hzero 0 (by omega), Nat.cast_zero, zero_add] at hshift
    have htail := ih (unshiftDig d) (fun i => hd (i + 1)) (fun i hik => hzero (i + 1) (by omega))
    have hlt : (p : ℚ) * fracVal p d < (p : ℚ) ^ (-(k : ℤ)) := hshift ▸ htail
    have hexp : (p : ℚ) ^ (-(k : ℤ)) = (p : ℚ) * (p : ℚ) ^ (-((k + 1 : ℕ) : ℤ)) := by
      rw [mul_comm, ← zpow_add_one₀ hppos.ne']
      congr 1
      push_cast
      ring
    rw [hexp] at hlt
    exact lt_of_mul_lt_mul_left hlt hppos.le

/-- The value of a nonzero canonical expansion lies in
`[v·p^{-(j+1)}, (v+1)·p^{-(j+1)})` where `j` is the leading position and `v` the leading
digit: the head digit dominates the tail. -/
theorem apply_leadPos_le_fracVal (d : ℕ →₀ ℕ) :
    (d (leadPos d) : ℚ) * (p : ℚ) ^ (-(leadPos d + 1 : ℤ)) ≤ fracVal p d := by
  rw [fracVal_eq_apply_add_erase p (leadPos d) d]
  have := fracVal_nonneg p (d.erase (leadPos d))
  linarith

theorem fracVal_lt_apply_leadPos_succ (hp : 1 < p) {d : ℕ →₀ ℕ} (hd : ∀ i, d i < p) :
    fracVal p d < ((d (leadPos d) : ℚ) + 1) * (p : ℚ) ^ (-(leadPos d + 1 : ℤ)) := by
  rw [fracVal_eq_apply_add_erase p (leadPos d) d]
  have htail : fracVal p (d.erase (leadPos d)) < (p : ℚ) ^ (-(leadPos d + 1 : ℕ) : ℤ) := by
    refine fracVal_lt_zpow_neg p hp _ _ (fun i => ?_) (fun i hik => ?_)
    · rw [Finsupp.erase_apply]
      split
      · omega
      · exact hd i
    · rw [Finsupp.erase_apply]
      split
      · rfl
      · exact apply_eq_zero_of_lt_leadPos (by omega)
  have hexp : ((leadPos d + 1 : ℕ) : ℤ) = (leadPos d + 1 : ℤ) := by push_cast; ring
  rw [hexp] at htail
  linarith

/-- **Larger values have lexicographically larger heads**: if `e` has an earlier leading
position than `d`, or the same leading position with a larger leading digit, then `e` has
the larger value. -/
theorem fracVal_lt_fracVal_of_lead (hp : 1 < p) {d e : ℕ →₀ ℕ} (hd : ∀ i, d i < p)
    (hene : e ≠ 0)
    (h : leadPos e < leadPos d ∨ (leadPos e = leadPos d ∧ d (leadPos d) < e (leadPos e))) :
    fracVal p d < fracVal p e := by
  have hppos : (0 : ℚ) < (p : ℚ) := by exact_mod_cast (by omega : 0 < p)
  have h1 : fracVal p d < ((d (leadPos d) : ℚ) + 1) * (p : ℚ) ^ (-(leadPos d + 1 : ℤ)) :=
    fracVal_lt_apply_leadPos_succ p hp hd
  have h2 : (e (leadPos e) : ℚ) * (p : ℚ) ^ (-(leadPos e + 1 : ℤ)) ≤ fracVal p e :=
    apply_leadPos_le_fracVal p e
  have hzpos : ∀ z : ℤ, (0 : ℚ) < (p : ℚ) ^ z := fun z => zpow_pos hppos z
  rcases h with hlt | ⟨heq, hdig⟩
  · -- `e` leads strictly earlier: `fracVal d < p^{-leadPos d} ≤ p^{-(leadPos e + 1)} ≤ fracVal e`.
    have hstep1 : ((d (leadPos d) : ℚ) + 1) * (p : ℚ) ^ (-(leadPos d + 1 : ℤ))
        ≤ (p : ℚ) ^ (-(leadPos d : ℤ)) := by
      have hple : ((d (leadPos d) : ℚ) + 1) ≤ (p : ℚ) := by
        exact_mod_cast hd (leadPos d)
      have hmul : (p : ℚ) * (p : ℚ) ^ (-(leadPos d + 1 : ℤ)) = (p : ℚ) ^ (-(leadPos d : ℤ)) := by
        rw [mul_comm, ← zpow_add_one₀ hppos.ne']
        congr 1
        ring
      calc ((d (leadPos d) : ℚ) + 1) * (p : ℚ) ^ (-(leadPos d + 1 : ℤ))
          ≤ (p : ℚ) * (p : ℚ) ^ (-(leadPos d + 1 : ℤ)) :=
            mul_le_mul_of_nonneg_right hple (hzpos _).le
        _ = (p : ℚ) ^ (-(leadPos d : ℤ)) := hmul
    have hstep2 : (p : ℚ) ^ (-(leadPos d : ℤ)) ≤ (p : ℚ) ^ (-(leadPos e + 1 : ℤ)) := by
      refine zpow_le_zpow_right₀ (by exact_mod_cast hp.le) (by omega)
    have hstep3 : (p : ℚ) ^ (-(leadPos e + 1 : ℤ))
        ≤ (e (leadPos e) : ℚ) * (p : ℚ) ^ (-(leadPos e + 1 : ℤ)) := by
      have h1e : (1 : ℚ) ≤ (e (leadPos e) : ℚ) := by exact_mod_cast leadPos_pos hene
      nlinarith [hzpos (-(leadPos e + 1 : ℤ))]
    linarith
  · -- Same leading position, larger leading digit on `e`.
    have hstep : ((d (leadPos d) : ℚ) + 1) * (p : ℚ) ^ (-(leadPos d + 1 : ℤ))
        ≤ (e (leadPos e) : ℚ) * (p : ℚ) ^ (-(leadPos e + 1 : ℤ)) := by
      rw [heq] at hdig ⊢
      have : ((d (leadPos d) : ℚ) + 1) ≤ (e (leadPos d) : ℚ) := by exact_mod_cast hdig
      exact mul_le_mul_of_nonneg_right this (hzpos _).le
    linarith

/-- The digit rank: a strictly value-reversing ordinal rank on canonical fractional
expansions.  The zero expansion (the largest element in reversed order) gets `ω^(c+1)`; a
nonzero expansion with leading position `j` and leading digit `v` gets
`ω^c·(2(jp + (p-1-v)) + 1)` plus the rank of its tail at budget `c - v`.  Larger values
have lexicographically larger digit strings and receive strictly smaller ranks. -/
noncomputable def digitRank : ℕ → (ℕ →₀ ℕ) → Ordinal
  | c, d =>
    if _hd : d = 0 then omega0 ^ ((c : Ordinal) + 1)
    else
      omega0 ^ (c : Ordinal)
          * ((2 * (leadPos d * p + (p - 1 - d (leadPos d))) + 1 : ℕ) : Ordinal)
        + digitRank (c - d (leadPos d)) (d.erase (leadPos d))
  termination_by _ d => d.support.card
  decreasing_by
    have hmem := leadPos_mem _hd
    have hcard : 0 < d.support.card := Finset.card_pos.mpr ⟨_, hmem⟩
    rw [Finsupp.support_erase, Finset.card_erase_of_mem hmem]
    omega

theorem digitRank_zero (c : ℕ) : digitRank p c 0 = omega0 ^ ((c : Ordinal) + 1) := by
  rw [digitRank]
  simp

theorem digitRank_of_ne_zero (c : ℕ) {d : ℕ →₀ ℕ} (hd : d ≠ 0) :
    digitRank p c d
      = omega0 ^ (c : Ordinal)
            * ((2 * (leadPos d * p + (p - 1 - d (leadPos d))) + 1 : ℕ) : Ordinal)
          + digitRank p (c - d (leadPos d)) (d.erase (leadPos d)) := by
  rw [digitRank]
  simp [hd]

/-- The digit sum of the tail after erasing the leading digit. -/
theorem sum_erase_leadPos {d : ℕ →₀ ℕ} {c : ℕ}
    (hsum : (d.sum fun _ v => v) ≤ c) :
    ((d.erase (leadPos d)).sum fun _ v => v) ≤ c - d (leadPos d) := by
  have hkey : d (leadPos d) + ((d.erase (leadPos d)).sum fun _ v => v)
      = d.sum fun _ v => v := by
    conv_rhs => rw [← Finsupp.single_add_erase (leadPos d) d]
    rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl),
      Finsupp.sum_single_index rfl]
  omega

/-- The leading digit is at most the digit sum. -/
theorem apply_leadPos_le_sum (d : ℕ →₀ ℕ) : d (leadPos d) ≤ d.sum fun _ v => v := by
  rcases eq_or_ne d 0 with rfl | hd
  · simp
  · exact Finset.single_le_sum (fun i _ => Nat.zero_le _) (leadPos_mem hd)

/-- **Rank bound**: any expansion of digit sum at most `c` has rank at most `ω^(c+1)`. -/
theorem digitRank_le (c : ℕ) : ∀ (d : ℕ →₀ ℕ), (d.sum fun _ v => v) ≤ c →
    digitRank p c d ≤ omega0 ^ ((c : Ordinal) + 1) := by
  induction c using Nat.strong_induction_on with
  | _ c ih =>
    intro d hsum
    rcases eq_or_ne d 0 with rfl | hd
    · rw [digitRank_zero]
    · rw [digitRank_of_ne_zero p c hd]
      set j := leadPos d
      set v := d j with hv
      have hv1 : 1 ≤ v := leadPos_pos hd
      have hvc : v ≤ c := le_trans (apply_leadPos_le_sum d) hsum
      set m : ℕ := 2 * (j * p + (p - 1 - v)) + 1 with hm
      have htail : digitRank p (c - v) (d.erase j) ≤ omega0 ^ (((c - v : ℕ) : Ordinal) + 1) :=
        ih (c - v) (by omega) _ (sum_erase_leadPos hsum)
      have hexp : omega0 ^ (((c - v : ℕ) : Ordinal) + 1) ≤ omega0 ^ (c : Ordinal) := by
        apply Ordinal.opow_le_opow_right omega0_pos
        rw [← Nat.cast_add_one]
        exact Nat.cast_le.mpr (by omega : c - v + 1 ≤ c)
      have hstep : ((m : Ordinal) + 1) ≤ omega0 := by
        rw [← Nat.cast_add_one]
        exact (natCast_lt_omega0 (m + 1)).le
      calc omega0 ^ (c : Ordinal) * (m : Ordinal) + digitRank p (c - v) (d.erase j)
          ≤ omega0 ^ (c : Ordinal) * (m : Ordinal) + omega0 ^ (c : Ordinal) :=
            add_le_add le_rfl (le_trans htail hexp)
        _ = omega0 ^ (c : Ordinal) * ((m : Ordinal) + 1) := by
            rw [mul_add, mul_one]
        _ ≤ omega0 ^ (c : Ordinal) * omega0 := mul_le_mul_right hstep _
        _ = omega0 ^ ((c : Ordinal) + 1) := by
            rw [Ordinal.opow_add, Ordinal.opow_one]

/-- **Strict rank bound**: a nonzero expansion of digit sum at most `c` has rank
strictly below `ω^(c+1)` (the rank of the zero expansion). -/
theorem digitRank_lt_of_ne_zero (c : ℕ) {d : ℕ →₀ ℕ} (hd : d ≠ 0)
    (hsum : (d.sum fun _ v => v) ≤ c) :
    digitRank p c d < omega0 ^ ((c : Ordinal) + 1) := by
  rw [digitRank_of_ne_zero p c hd]
  set j := leadPos d
  set v := d j with hv
  have hv1 : 1 ≤ v := leadPos_pos hd
  have hvc : v ≤ c := le_trans (apply_leadPos_le_sum d) hsum
  set m : ℕ := 2 * (j * p + (p - 1 - v)) + 1 with hm
  have htail : digitRank p (c - v) (d.erase j) ≤ omega0 ^ (((c - v : ℕ) : Ordinal) + 1) :=
    digitRank_le p (c - v) _ (sum_erase_leadPos hsum)
  have hexp : omega0 ^ (((c - v : ℕ) : Ordinal) + 1) ≤ omega0 ^ (c : Ordinal) := by
    apply Ordinal.opow_le_opow_right omega0_pos
    rw [← Nat.cast_add_one]
    exact Nat.cast_le.mpr (by omega : c - v + 1 ≤ c)
  calc omega0 ^ (c : Ordinal) * (m : Ordinal) + digitRank p (c - v) (d.erase j)
      ≤ omega0 ^ (c : Ordinal) * (m : Ordinal) + omega0 ^ (c : Ordinal) :=
        add_le_add le_rfl (le_trans htail hexp)
    _ = omega0 ^ (c : Ordinal) * ((m : Ordinal) + 1) := by rw [mul_add, mul_one]
    _ < omega0 ^ (c : Ordinal) * omega0 := by
        apply mul_lt_mul_of_pos_left ?_ (Ordinal.opow_pos _ omega0_pos)
        rw [← Nat.cast_add_one]
        exact natCast_lt_omega0 (m + 1)
    _ = omega0 ^ ((c : Ordinal) + 1) := by rw [Ordinal.opow_add, Ordinal.opow_one]

/-- The digits of the tail are still canonical. -/
theorem erase_apply_lt {d : ℕ →₀ ℕ} (hd : ∀ i, d i < p) (j i : ℕ) : (d.erase j) i < p := by
  rw [Finsupp.erase_apply]
  split
  · exact (Nat.zero_le _).trans_lt (hd i)
  · exact hd i

/-- **Rank monotonicity**: among canonical expansions of digit sum at most `c`, a larger
fractional value means a strictly smaller digit rank. -/
theorem digitRank_lt_of_fracVal_lt (hp : 1 < p) :
    ∀ (c : ℕ) {d e : ℕ →₀ ℕ}, (∀ i, d i < p) → (∀ i, e i < p) →
      (d.sum fun _ v => v) ≤ c → (e.sum fun _ v => v) ≤ c →
      fracVal p e < fracVal p d →
      digitRank p c d < digitRank p c e := by
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ih =>
    intro d e hd he hsumd hsume hlt
    have hdne : d ≠ 0 := by
      rintro rfl
      rw [fracVal_zero] at hlt
      exact absurd hlt (not_lt.mpr (fracVal_nonneg p e))
    rcases eq_or_ne e 0 with rfl | hene
    · rw [digitRank_zero]
      exact digitRank_lt_of_ne_zero p c hdne hsumd
    · set jd := leadPos d with hjd
      set je := leadPos e with hje
      set vd := d jd with hvd
      set ve := e je with hve
      have hvd1 : 1 ≤ vd := leadPos_pos hdne
      have hve1 : 1 ≤ ve := leadPos_pos hene
      have hvdp : vd < p := hd jd
      have hvep : ve < p := he je
      have hvdc : vd ≤ c := le_trans (apply_leadPos_le_sum d) hsumd
      have hvec : ve ≤ c := le_trans (apply_leadPos_le_sum e) hsume
      -- A strictly smaller head coefficient forces a strictly smaller total rank.
      have hcase : 2 * (jd * p + (p - 1 - vd)) + 1 < 2 * (je * p + (p - 1 - ve)) + 1 →
          digitRank p c d < digitRank p c e := by
        intro hm
        rw [digitRank_of_ne_zero p c hdne, digitRank_of_ne_zero p c hene, ← hjd, ← hje,
          ← hvd, ← hve]
        set md : ℕ := 2 * (jd * p + (p - 1 - vd)) + 1
        set me : ℕ := 2 * (je * p + (p - 1 - ve)) + 1
        have htail : digitRank p (c - vd) (d.erase jd) ≤ omega0 ^ (((c - vd : ℕ) : Ordinal) + 1) :=
          digitRank_le p (c - vd) _ (sum_erase_leadPos hsumd)
        have hexp : omega0 ^ (((c - vd : ℕ) : Ordinal) + 1) ≤ omega0 ^ (c : Ordinal) := by
          apply Ordinal.opow_le_opow_right omega0_pos
          rw [← Nat.cast_add_one]
          exact Nat.cast_le.mpr (by omega : c - vd + 1 ≤ c)
        calc omega0 ^ (c : Ordinal) * (md : Ordinal) + digitRank p (c - vd) (d.erase jd)
            ≤ omega0 ^ (c : Ordinal) * (md : Ordinal) + omega0 ^ (c : Ordinal) :=
              add_le_add le_rfl (le_trans htail hexp)
          _ = omega0 ^ (c : Ordinal) * ((md : Ordinal) + 1) := by rw [mul_add, mul_one]
          _ < omega0 ^ (c : Ordinal) * (me : Ordinal) := by
              apply mul_lt_mul_of_pos_left ?_ (Ordinal.opow_pos _ omega0_pos)
              rw [← Nat.cast_add_one]
              exact Nat.cast_lt.mpr (by omega)
          _ ≤ omega0 ^ (c : Ordinal) * (me : Ordinal)
                + digitRank p (c - ve) (e.erase je) := le_add_right le_rfl
      rcases lt_trichotomy jd je with hj | hj | hj
      · -- `d` leads strictly earlier: strictly smaller head coefficient.
        refine hcase ?_
        have h1 : (jd + 1) * p ≤ je * p := Nat.mul_le_mul_right p (by omega)
        rw [add_one_mul] at h1
        omega
      · -- Same leading position: compare the leading digits.
        rcases lt_trichotomy vd ve with hv | hv | hv
        · -- `e` has the larger leading digit: then `fracVal d < fracVal e`, absurd.
          have := fracVal_lt_fracVal_of_lead p hp hd hene
            (Or.inr ⟨by rw [← hje, ← hjd, hj], by rw [← hje, ← hjd, ← hve, ← hvd]; exact hv⟩)
          exact absurd hlt (asymm this)
        · -- Equal heads: recurse on the tails at budget `c - vd`.
          have hveq : ve = vd := hv.symm
          have hdj : d je = vd := by rw [← hj, ← hvd]
          have hej : e je = vd := by rw [← hve, hveq]
          have htails : fracVal p (e.erase je) < fracVal p (d.erase je) := by
            have h1 := fracVal_eq_apply_add_erase p je d
            have h2 := fracVal_eq_apply_add_erase p je e
            rw [hdj] at h1
            rw [hej] at h2
            rw [h1, h2] at hlt
            linarith
          have hsumd' : ((d.erase je).sum fun _ v => v) ≤ c - vd := by
            rw [← hj]
            exact sum_erase_leadPos hsumd
          have hsume' : ((e.erase je).sum fun _ v => v) ≤ c - vd := by
            rw [← hveq]
            exact sum_erase_leadPos hsume
          have hrec := ih (c - vd) (by omega)
            (erase_apply_lt p hd je) (erase_apply_lt p he je)
            hsumd' hsume' htails
          rw [digitRank_of_ne_zero p c hdne, digitRank_of_ne_zero p c hene, ← hjd, ← hje,
            ← hvd, ← hve, hj, hveq]
          exact (add_lt_add_iff_left _).mpr hrec
        · -- `d` has the larger leading digit: strictly smaller head coefficient.
          refine hcase ?_
          rw [hj]
          omega
      · -- `e` leads strictly earlier: then `fracVal d < fracVal e`, absurd.
        have := fracVal_lt_fracVal_of_lead p hp hd hene (Or.inl (by rw [← hje, ← hjd]; exact hj))
        exact absurd hlt (asymm this)

end TrustworthyKedlaya.UP
