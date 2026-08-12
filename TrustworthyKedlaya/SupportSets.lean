/-
Copyright (c) 2026 Shanwen Wang, Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import TrustworthyKedlaya.Digits
public import TrustworthyKedlaya.TwistPeriodicity
public import Mathlib.Data.Finset.MulAntidiagonal
public import Mathlib.Order.WellFoundedSet

/-!
# The support sets `S_{a,b,c}`: well-ordering and additive calculus

Two fundamental properties of the support sets `S_{a,b,c}` of Kedlaya (2001a)/(2017):

- `Sabc_isPWO` / `Sabc_isWF`: each `S_{a,b,c}` is a partially well-ordered (equivalently,
  since `ℚ` is linear, well-ordered) subset of `ℚ`.  Consequently any formal series
  supported on some `S_{a,b,c}` is an honest Hahn series.  The proof avoids all digit
  combinatorics: `S_{a,b,c}` is contained in the image, under division by `a`, of the
  sumset `{n ∈ ℤ : n ≥ -b} + (-D_c)`, where `-D_c` is in turn contained in the `c`-fold
  sumset of the set `{0} ∪ {-p^{-k} : k ≥ 1}` of negated place values; partial
  well-ordering is preserved by sumsets (`Set.IsPWO.add`) and monotone images.

- `Sabc_add_subset`: `S_{a,b,c} + S_{a,b',c'} ⊆ S_{a, b+b'+1, c+c'}`.  This is the carry
  estimate: base-`p` addition of two fractional expansions with digit sums `≤ c, ≤ c'`
  yields, after carrying (`exists_carry_normalization`), an expansion with digit sum
  `≤ c + c'` plus an integer carry `∈ {0, 1}`.

## References

- K. S. Kedlaya, *The algebraic closure of the power series field in positive
  characteristic*, Proc. Amer. Math. Soc. 129 (2001) [Ked01a], Lemmas 1-2.
- K. S. Kedlaya, *On the algebraicity of generalized power series*, Beiträge Algebra
  Geom. 58 (2017) [Ked17], Section 2.
-/

@[expose] public section

namespace TrustworthyKedlaya.UP

open Finset Pointwise

variable (p : ℕ)

/-! ### Well-ordering -/

/-- The negated place values `-p^{-(k+1)}`, `k ≥ 0`, together with `0`: the possible
contributions of a single digit unit to a negated fractional expansion. -/
def negPlaceValues : Set ℚ :=
  insert 0 (Set.range fun k : ℕ => -((p : ℚ) ^ (-(k + 1 : ℤ))))

theorem zero_mem_negPlaceValues : (0 : ℚ) ∈ negPlaceValues p :=
  Set.mem_insert 0 _

theorem isPWO_negPlaceValues (hp : 1 ≤ p) : (negPlaceValues p).IsPWO := by
  refine Set.IsPWO.insert ?_ 0
  have huniv : (Set.univ : Set ℕ).IsPWO :=
    (Set.isWF_univ_iff.mpr inferInstance).isPWO
  have hmono : Monotone fun k : ℕ => -((p : ℚ) ^ (-(k + 1 : ℤ))) := by
    intro x y hxy
    rw [neg_le_neg_iff]
    refine zpow_le_zpow_right₀ (by exact_mod_cast hp) ?_
    omega
  simpa [Set.image_univ] using huniv.image_of_monotone hmono

/-- `negFracSums p c`: all sums of at most `c` negated place values, i.e. the negated
values of fractional expansions with digit sum at most `c` (with no constraint that
individual digits stay below `p`). -/
def negFracSums (p : ℕ) : ℕ → Set ℚ
  | 0 => {0}
  | c + 1 => negPlaceValues p + negFracSums p c

theorem negFracSums_succ (c : ℕ) :
    negFracSums p (c + 1) = negPlaceValues p + negFracSums p c := rfl

theorem isPWO_negFracSums (hp : 1 ≤ p) : ∀ c, (negFracSums p c).IsPWO
  | 0 => (Set.finite_singleton 0).isPWO
  | c + 1 => (isPWO_negPlaceValues p hp).add (isPWO_negFracSums hp c)

theorem zero_mem_negFracSums : ∀ c, (0 : ℚ) ∈ negFracSums p c
  | 0 => rfl
  | c + 1 => by
    rw [negFracSums_succ]
    simpa using Set.add_mem_add (zero_mem_negPlaceValues p) (zero_mem_negFracSums c)

theorem negFracSums_subset_succ (c : ℕ) : negFracSums p c ⊆ negFracSums p (c + 1) :=
  fun x hx => by
    rw [negFracSums_succ]
    simpa using Set.add_mem_add (zero_mem_negPlaceValues p) hx

theorem negFracSums_mono {c c' : ℕ} (h : c ≤ c') : negFracSums p c ⊆ negFracSums p c' := by
  induction c' with
  | zero => rw [Nat.le_zero.mp h]
  | succ c' ih =>
    rcases Nat.eq_or_lt_of_le h with rfl | hlt
    · exact subset_rfl
    · exact (ih (by omega)).trans (negFracSums_subset_succ p c')

/-- The negated value of any pseudo-digit expansion with digit sum at most `c` lies in the
`c`-fold sumset of negated place values. -/
theorem neg_fracVal_mem_negFracSums (e : ℕ →₀ ℕ) :
    ∀ {c : ℕ}, (e.sum fun _ v => v) ≤ c → -fracVal p e ∈ negFracSums p c := by
  induction e using Finsupp.induction with
  | zero => intro c _; simpa using zero_mem_negFracSums p c
  | single_add a v f ha hv ih =>
    intro c hc
    have hsum : v + (f.sum fun _ w => w) ≤ c := by
      rwa [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl),
        Finsupp.sum_single_index rfl] at hc
    rw [fracVal_add, fracVal_single]
    -- Peel off the `v` units of the digit at position `a` one at a time.
    have key : ∀ (w c : ℕ), w + (f.sum fun _ x => x) ≤ c →
        -((w : ℚ) * (p : ℚ) ^ (-(a + 1 : ℤ)) + fracVal p f) ∈ negFracSums p c := by
      intro w
      induction w with
      | zero =>
        intro c hc0
        simpa using negFracSums_mono p (by omega) (ih (le_refl _))
      | succ w ihw =>
        intro c hc0
        obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
        have hmem : -((p : ℚ) ^ (-(a + 1 : ℤ))) ∈ negPlaceValues p :=
          Set.mem_insert_of_mem _ ⟨a, rfl⟩
        have hrec := ihw c' (by omega)
        have hkey : -(((w + 1 : ℕ) : ℚ) * (p : ℚ) ^ (-(a + 1 : ℤ)) + fracVal p f)
            = -((p : ℚ) ^ (-(a + 1 : ℤ)))
              + -((w : ℚ) * (p : ℚ) ^ (-(a + 1 : ℤ)) + fracVal p f) := by
          push_cast
          ring
        rw [hkey, negFracSums_succ]
        exact Set.add_mem_add hmem hrec
    exact key v c hsum

/-- The set of rational casts of integers `≥ -b` is partially well-ordered. -/
theorem isPWO_intCastGE (b : ℕ) :
    {q : ℚ | ∃ n : ℤ, -(b : ℤ) ≤ n ∧ q = (n : ℚ)}.IsPWO := by
  have huniv : (Set.univ : Set ℕ).IsPWO :=
    (Set.isWF_univ_iff.mpr inferInstance).isPWO
  have hmono : Monotone fun m : ℕ => (m : ℚ) - (b : ℚ) := by
    intro x y hxy
    have : (x : ℚ) ≤ (y : ℚ) := by exact_mod_cast hxy
    linarith
  refine ((huniv.image_of_monotone hmono).mono ?_)
  rintro q ⟨n, hn, rfl⟩
  refine ⟨(n + b).toNat, Set.mem_univ _, ?_⟩
  have h0 : (0 : ℤ) ≤ n + b := by omega
  have h1 : (((n + b).toNat : ℕ) : ℚ) = (n : ℚ) + (b : ℚ) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg h0]
    push_cast
    ring
  simp only [h1]
  ring

variable [hp : Fact (Nat.Prime p)]

/-- **`S_{a,b,c}` is partially well-ordered** (hence well-ordered, as `ℚ` is linear):
it lies in the monotone image of a sumset of partially well-ordered sets.  In particular
any formal series supported on some `S_{a,b,c}` is a Hahn series. -/
theorem Sabc_isPWO (a : ℕ+) (b c : ℕ) : (Sabc p a b c).IsPWO := by
  have hp1 : 1 ≤ p := hp.out.one_lt.le
  have hsum := (isPWO_intCastGE b).add (isPWO_negFracSums p hp1 c)
  have ha : (0 : ℚ) < (a : ℚ) := by exact_mod_cast a.pos
  have hmono : Monotone fun q : ℚ => q / (a : ℚ) := fun x y hxy => by
    simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_right hxy (inv_nonneg.mpr ha.le)
  refine ((hsum.image_of_monotone hmono).mono ?_)
  rintro s ⟨n, d, hn, hd, hsd, rfl⟩
  rw [fracVal_def]
  refine ⟨(n : ℚ) + -fracVal p d,
    Set.add_mem_add ⟨n, hn, rfl⟩ (neg_fracVal_mem_negFracSums p d hsd), ?_⟩
  ring

/-- `S_{a,b,c}` is a well-ordered subset of `ℚ`. -/
theorem Sabc_isWF (a : ℕ+) (b c : ℕ) : (Sabc p a b c).IsWF :=
  (Sabc_isPWO p a b c).isWF

/-! ### Twist evaluation points as canonical expansions -/

/-- The canonical digit expansion of the twist evaluation point of `twistSeq` at gap
size `n`: the prefix digits (positions `< j - 1`) stay in place, while the tail digits
(positions `≥ j - 1`) are shifted out by `n`. -/
noncomputable def gapDig (j n : ℕ) (b : ℕ →₀ ℕ) : ℕ →₀ ℕ :=
  b.filter (fun i => i < j - 1)
    + Finsupp.embDomain ⟨fun i => i + n, add_left_injective n⟩
        (b.filter (fun i => j - 1 ≤ i))

omit [hp : Fact (Nat.Prime p)] in
/-- Gap insertion does not create digits `≥ p`. -/
theorem gapDig_lt {b : ℕ →₀ ℕ} (hb : ∀ i, b i < p) (hp0 : 0 < p) (j n i : ℕ) :
    gapDig j n b i < p := by
  rw [gapDig, Finsupp.add_apply, Finsupp.filter_apply]
  by_cases h1 : i < j - 1
  · rw [if_pos h1]
    have h2 : Finsupp.embDomain ⟨fun i => i + n, add_left_injective n⟩
        (b.filter (fun i => j - 1 ≤ i)) i = 0 := by
      by_cases hn : n ≤ i
      · have hi : i = (i - n) + n := by omega
        rw [hi, show ((i - n) + n) = (⟨fun i => i + n, add_left_injective n⟩ : ℕ ↪ ℕ) (i - n)
            from rfl, Finsupp.embDomain_apply_self]
        exact Finsupp.filter_apply_neg _ _ (by omega)
      · exact Finsupp.embDomain_of_notMem_range _ _ _
          (by rintro ⟨k, hk⟩; simp only [Function.Embedding.coeFn_mk] at hk; omega)
    rw [h2, add_zero]
    exact hb i
  · rw [if_neg h1, zero_add]
    by_cases hn : n ≤ i
    · have hi : i = (i - n) + n := by omega
      rw [hi, show ((i - n) + n) = (⟨fun i => i + n, add_left_injective n⟩ : ℕ ↪ ℕ) (i - n)
          from rfl, Finsupp.embDomain_apply_self, Finsupp.filter_apply]
      split
      · exact hb _
      · exact hp0
    · rw [Finsupp.embDomain_of_notMem_range _ _ _
        (by rintro ⟨k, hk⟩; simp only [Function.Embedding.coeFn_mk] at hk; omega)]
      exact hp0

omit [hp : Fact (Nat.Prime p)] in
/-- Gap insertion preserves the digit sum. -/
theorem gapDig_sum (j n : ℕ) (b : ℕ →₀ ℕ) :
    ((gapDig j n b).sum fun _ v => v) = b.sum fun _ v => v := by
  have hfilter : ∀ (q : ℕ → Prop) [DecidablePred q],
      ((b.filter q).sum fun _ v => v) = ∑ i ∈ b.support with q i, b i := by
    intro q _
    rw [Finsupp.sum, Finsupp.support_filter]
    exact Finset.sum_congr rfl fun i hi =>
      Finsupp.filter_apply_pos _ _ (Finset.mem_filter.mp hi).2
  rw [gapDig, Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl),
    Finsupp.sum_embDomain, hfilter (fun i => i < j - 1), hfilter (fun i => j - 1 ≤ i),
    show (b.support.filter fun i => j - 1 ≤ i) = b.support.filter fun i => ¬i < j - 1 from
      Finset.filter_congr fun i _ => not_lt.symm,
    Finset.sum_filter_add_sum_filter_not]
  rfl

omit [hp : Fact (Nat.Prime p)] in
/-- The fractional value of the gap-inserted expansion is the (negated) twist
evaluation point of `twistSeq`. -/
theorem fracVal_gapDig (hp0 : 0 < p) (j n : ℕ) (b : ℕ →₀ ℕ) :
    fracVal p (gapDig j n b)
      = (∑ i ∈ Finset.range (j - 1), (b i : ℚ) * (p : ℚ) ^ (-(i + 1 : ℤ)))
        + (p : ℚ) ^ (-(n : ℤ)) *
            ∑ i ∈ b.support.filter (fun i => j - 1 ≤ i),
              (b i : ℚ) * (p : ℚ) ^ (-(i + 1 : ℤ)) := by
  rw [gapDig, fracVal_add]
  congr 1
  · -- The prefix part: extend the sum over the filtered support to the full window.
    rw [fracVal, Finsupp.sum, Finsupp.support_filter]
    rw [show ∀ s : Finset ℕ, (∑ i ∈ s, ((b.filter fun i => i < j - 1) i : ℚ)
          * (p : ℚ) ^ (-(i + 1 : ℤ)))
        = ∑ i ∈ s, if i < j - 1 then (b i : ℚ) * (p : ℚ) ^ (-(i + 1 : ℤ)) else 0 from
        fun s => Finset.sum_congr rfl fun i _ => by
          rw [Finsupp.filter_apply]
          split <;> simp]
    rw [Finset.sum_ite_of_true (fun i hi => (Finset.mem_filter.mp hi).2) _ _]
    refine Finset.sum_subset (fun i hi => Finset.mem_range.mpr (Finset.mem_filter.mp hi).2)
      fun i hi hni => ?_
    have : b i = 0 := by
      by_contra hbi
      exact hni (Finset.mem_filter.mpr ⟨Finsupp.mem_support_iff.mpr hbi,
        Finset.mem_range.mp hi⟩)
    rw [this]
    simp
  · -- The tail part: the shift by `n` factors out as `p^{-n}`.
    rw [fracVal, Finsupp.sum_embDomain, Finsupp.sum, Finsupp.support_filter,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finsupp.filter_apply_pos _ _ (Finset.mem_filter.mp hi).2,
      Function.Embedding.coeFn_mk]
    rw [show (-(↑(i + n) + 1) : ℤ) = (-(n : ℤ)) + (-(i + 1 : ℤ)) by push_cast; ring,
      zpow_add₀ (by exact_mod_cast hp0.ne' : (p : ℚ) ≠ 0)]
    ring

/-! ### The additive carry estimate -/

/-- **Carry estimate for sums of support sets**:
`S_{a,b,c} + S_{a,b',c'} ⊆ S_{a, b+b'+1, c+c'}`.  Adding two fractional expansions with
digit sums `≤ c` and `≤ c'` and carrying yields a canonical expansion of digit sum
`≤ c + c'`, at the cost of an integer carry `∈ {0, 1}` absorbed into the integer part. -/
theorem Sabc_add_subset {a : ℕ+} {b b' c c' : ℕ} {s s' : ℚ}
    (hs : s ∈ Sabc p a b c) (hs' : s' ∈ Sabc p a b' c') :
    s + s' ∈ Sabc p a (b + b' + 1) (c + c') := by
  obtain ⟨n, d, hn, hd, hsum, rfl⟩ := hs
  obtain ⟨n', d', hn', hd', hsum', rfl⟩ := hs'
  obtain ⟨k, dd, hdd, hsumdd, hval⟩ := exists_carry_normalization p (d + d')
  have hsum2 : ((d + d').sum fun _ v => v) ≤ c + c' := by
    rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)]
    omega
  -- The integer carry is 0 or 1 because both fractional values are in `[0, 1)`.
  have hk1 : k ≤ 1 := by
    by_contra hk
    have h2 : (2 : ℚ) ≤ (k : ℚ) := by exact_mod_cast (by omega : 2 ≤ k)
    have hlt : fracVal p (d + d') < 2 := by
      rw [fracVal_add]
      have hd1 := fracVal_lt_one p hp.out.one_lt hd
      have hd2 := fracVal_lt_one p hp.out.one_lt hd'
      linarith
    have hge : (k : ℚ) ≤ fracVal p (d + d') := by
      rw [hval]
      have := fracVal_nonneg p dd
      linarith
    linarith
  refine ⟨n + n' - k, dd, by push_cast; omega, hdd, by omega, ?_⟩
  have hfv : fracVal p d + fracVal p d' = (k : ℚ) + fracVal p dd := by
    rw [← fracVal_add]; exact hval
  rw [fracVal_def p d, fracVal_def p d', fracVal_def p dd]
  push_cast
  linear_combination (-(1 / (a : ℚ))) * hfv

/-! ### Twist-sequence vanishing off the support data -/

/-- Twist sequences evaluate `f` at the negated value of the gap-inserted expansion. -/
theorem twistSeq_eq_neg_fracVal_gapDig (f : ℚ → 𝔽ᵃ_[p]) (j : ℕ) (b : ℕ →₀ ℕ) (n : ℕ) :
    twistSeq p f j b n = f (-fracVal p (gapDig j n b)) := by
  rw [twistSeq]
  congr 1
  rw [fracVal_gapDig p hp.out.pos]
  ring

/-- Membership of `(1/a)(m - w)` in `S_{a,b,c}`, with `w` the value of a canonical digit
expansion, forces the defining bounds on the integer part and the digit sum: the
canonical representation of a member of `S_{a,b,c}` is unique. -/
theorem Sabc_mem_canonical {a : ℕ+} {b c : ℕ} {m : ℤ} {e : ℕ →₀ ℕ}
    (he : ∀ i, e i < p)
    (hmem : (1 / (a : ℚ)) * ((m : ℚ) - fracVal p e) ∈ Sabc p a b c) :
    -(b : ℤ) ≤ m ∧ (e.sum fun _ v => v) ≤ c := by
  obtain ⟨n, d, hn, hd, hsum, heq⟩ := hmem
  have ha : ((a : ℚ)) ≠ 0 := by exact_mod_cast a.pos.ne'
  rw [fracVal_def] at heq
  have h2 : (m : ℚ) - fracVal p e = (n : ℚ) - fracVal p d :=
    mul_left_cancel₀ (one_div_ne_zero ha) heq
  have hde := fracVal_lt_one p hp.out.one_lt hd
  have hee := fracVal_lt_one p hp.out.one_lt he
  have hdnn := fracVal_nonneg p d
  have henn := fracVal_nonneg p e
  have hmn : m = n := by
    have hcast : ((m - n : ℤ) : ℚ) = fracVal p e - fracVal p d := by push_cast; linarith
    have h1 : |((m - n : ℤ) : ℚ)| < 1 := by
      rw [hcast, abs_lt]
      constructor <;> linarith
    rw [← Int.cast_abs] at h1
    have h3 : |m - n| < 1 := by exact_mod_cast h1
    have h4 := abs_lt.mp h3
    omega
  subst hmn
  have hw : fracVal p e = fracVal p d := by linarith
  rw [eq_of_fracVal_eq p hp.out.one_lt he hd hw]
  exact ⟨hn, hsum⟩

/-- **Slices sampled outside the support data vanish on all twist points**: if `x` is
supported in `S_{a,b,c}` and either the slice index satisfies `m < -b` or the digit sum
of `dig` exceeds `c`, then every term of every twist sequence of the slice function
`f_m(z) = x_{(m+z)/a}` is `0`.  This is uniqueness of the canonical representation:
the twist evaluation points carry the digits of `dig` verbatim (with a gap), so their
canonical expansions have the same digit sum and integer part `m`. -/
theorem twistSeq_slice_eq_zero {x : HahnSeries ℚ (𝔽ᵃ_[p])} {a : ℕ+} {b c : ℕ}
    (hsupp : x.support ⊆ Sabc p a b c) {m : ℤ} {dig : ℕ →₀ ℕ}
    (hdig : ∀ i, dig i < p)
    (hout : m < -(b : ℤ) ∨ c < (dig.sum fun _ v => v)) (j n : ℕ) :
    twistSeq p (fun z => x.coeff (((m : ℚ) + z) / (a : ℚ))) j dig n = 0 := by
  rw [twistSeq_eq_neg_fracVal_gapDig]
  by_contra h0
  have hmem : ((m : ℚ) + -fracVal p (gapDig j n dig)) / (a : ℚ) ∈ Sabc p a b c :=
    hsupp ((HahnSeries.mem_support _ _).mpr h0)
  rw [show ((m : ℚ) + -fracVal p (gapDig j n dig)) / (a : ℚ)
      = (1 / (a : ℚ)) * ((m : ℚ) - fracVal p (gapDig j n dig)) by ring] at hmem
  have hbounds := Sabc_mem_canonical p (gapDig_lt p hdig hp.out.pos j n) hmem
  rw [gapDig_sum] at hbounds
  rcases hout with h | h
  · omega
  · omega

/-- **Robustness of uniform periodicity**: for `x` supported in `S_{a,b,c}` whose
slices `m ≥ -b` are `(M,N)`-periodic at level `c`, *every* slice `m : ℤ` is
`(M,N)`-periodic at *every* level `c'`.  Indeed twist sequences outside the support
data are identically zero by `twistSeq_slice_eq_zero`.  This makes the support/level
parameters of `IsUP` freely enlargeable, which the closure lemmas use to pass to
common parameters. -/
theorem isTwistPeriodic_slice_upgrade {x : HahnSeries ℚ (𝔽ᵃ_[p])} {a : ℕ+} {b c : ℕ}
    {M N : ℕ+} (hsupp : x.support ⊆ Sabc p a b c)
    (hper : ∀ m : ℤ, -(b : ℤ) ≤ m →
      IsTwistPeriodic p (fun z => x.coeff (((m : ℚ) + z) / (a : ℚ))) c M N)
    (c' : ℕ) (m : ℤ) :
    IsTwistPeriodic p (fun z => x.coeff (((m : ℚ) + z) / (a : ℚ))) c' M N := by
  intro j dig hj hdig hsum n hn
  by_cases hm : -(b : ℤ) ≤ m
  · by_cases hc : (dig.sum fun _ v => v) ≤ c
    · exact hper m hm j dig hj hdig hc n hn
    · rw [twistSeq_slice_eq_zero p hsupp hdig (Or.inr (by omega)) j (n + N),
        twistSeq_slice_eq_zero p hsupp hdig (Or.inr (by omega)) j n]
  · rw [twistSeq_slice_eq_zero p hsupp hdig (Or.inl (by omega)) j (n + N),
      twistSeq_slice_eq_zero p hsupp hdig (Or.inl (by omega)) j n]

/-! ### Digit shifts and the scaling of `S_{a,b,c}` by `p^{±1}`

Multiplying a support point by `p` shifts its digits up by one position, moving the
leading fractional digit into the integer part; dividing by `p` shifts them down,
moving the residue of the integer part into a new leading fractional digit.  The digit
sum changes by at most `p - 1`, in the direction that only the division can increase. -/

/-- Drop the leading fractional digit: `unshiftDig d` has digit `d (i+1)` at
position `i`. -/
noncomputable def unshiftDig (d : ℕ →₀ ℕ) : ℕ →₀ ℕ :=
  d.comapDomain (· + 1) (add_left_injective 1).injOn

omit hp in
@[simp] theorem unshiftDig_apply (d : ℕ →₀ ℕ) (i : ℕ) : unshiftDig d i = d (i + 1) := rfl

omit hp in
/-- Dropping the leading digit only lowers the digit sum. -/
theorem unshiftDig_sum_le (d : ℕ →₀ ℕ) :
    ((unshiftDig d).sum fun _ v => v) ≤ d.sum fun _ v => v := by
  rw [Finsupp.sum, Finsupp.sum,
    show ∑ i ∈ (unshiftDig d).support, unshiftDig d i
        = ∑ i ∈ (unshiftDig d).support, d (i + 1) from
      Finset.sum_congr rfl fun i _ => rfl,
    ← Finset.sum_image (g := fun i => i + 1) (f := fun j => d j)
      (fun x _ y _ h => by simpa using h)]
  refine Finset.sum_le_sum_of_subset fun j hj => ?_
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
  rw [Finsupp.mem_support_iff] at hi ⊢
  exact hi

omit hp in
/-- Multiplication by `p` on fractional values: the leading digit becomes the integer
part, the rest is the unshifted expansion. -/
theorem p_mul_fracVal (hp0 : 0 < p) (d : ℕ →₀ ℕ) :
    (p : ℚ) * fracVal p d = (d 0 : ℚ) + fracVal p (unshiftDig d) := by
  have hpne : ((p : ℚ)) ≠ 0 := by exact_mod_cast hp0.ne'
  obtain ⟨L, hL⟩ := d.support.exists_nat_subset_range
  have hL' : d.support ⊆ range (L + 1) :=
    hL.trans fun x hx => Finset.mem_range.mpr (by have := Finset.mem_range.mp hx; omega)
  have hd' : (unshiftDig d).support ⊆ range L := by
    intro i hi
    rw [Finsupp.mem_support_iff, unshiftDig_apply] at hi
    have h1 := Finset.mem_range.mp (hL' (Finsupp.mem_support_iff.mpr hi))
    exact Finset.mem_range.mpr (by omega)
  rw [fracVal_eq_sum_range p d hL', fracVal_eq_sum_range p _ hd', Finset.mul_sum,
    Finset.sum_range_succ', add_comm]
  congr 1
  · have hone : (p : ℚ) * ((d 0 : ℚ) * (p : ℚ) ^ (-(0 + 1 : ℤ))) = (d 0 : ℚ) := by
      rw [show (-(0 + 1 : ℤ)) = (-1 : ℤ) by ring, zpow_neg_one]
      field_simp
    exact hone
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [unshiftDig_apply]
    have hpow : (p : ℚ) ^ (-(↑i + 1 : ℤ)) = (p : ℚ) ^ (-(↑(i + 1) + 1 : ℤ)) * (p : ℚ) := by
      rw [← zpow_add_one₀ hpne,
        show ((-(↑(i + 1) + 1) + 1 : ℤ)) = (-(↑i + 1 : ℤ)) by push_cast; ring]
    rw [hpow]
    ring

/-- Prepend a leading fractional digit: `consDig v d` has digit `v` at position `0` and
digit `d i` at position `i + 1`. -/
noncomputable def consDig (v : ℕ) (d : ℕ →₀ ℕ) : ℕ →₀ ℕ :=
  Finsupp.single 0 v
    + Finsupp.embDomain ⟨fun i => i + 1, add_left_injective 1⟩ d

omit hp in
theorem consDig_lt {v : ℕ} {d : ℕ →₀ ℕ} (hv : v < p) (hd : ∀ i, d i < p) (i : ℕ) :
    consDig v d i < p := by
  rw [consDig, Finsupp.add_apply]
  cases i with
  | zero =>
    rw [Finsupp.single_eq_same,
      Finsupp.embDomain_of_notMem_range _ _ _
        (by rintro ⟨k, hk⟩; simp only [Function.Embedding.coeFn_mk] at hk; omega),
      add_zero]
    exact hv
  | succ i =>
    rw [Finsupp.single_eq_of_ne (by omega),
      show (i + 1) = (⟨fun i => i + 1, add_left_injective 1⟩ : ℕ ↪ ℕ) i from rfl,
      Finsupp.embDomain_apply_self, zero_add]
    exact hd i

omit hp in
theorem consDig_sum (v : ℕ) (d : ℕ →₀ ℕ) :
    ((consDig v d).sum fun _ v => v) = v + d.sum fun _ v => v := by
  rw [consDig, Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl),
    Finsupp.sum_embDomain, Finsupp.sum_single_index rfl]

omit hp in
/-- The fractional value of `consDig v d` is `(v + fracVal d) / p`. -/
theorem fracVal_consDig (hp0 : 0 < p) (v : ℕ) (d : ℕ →₀ ℕ) :
    fracVal p (consDig v d) = ((v : ℚ) + fracVal p d) / p := by
  have hpne : ((p : ℚ)) ≠ 0 := by exact_mod_cast hp0.ne'
  rw [consDig, fracVal_add, fracVal_single, fracVal, Finsupp.sum_embDomain, fracVal,
    Finsupp.sum, Finsupp.sum, add_div, div_eq_mul_inv (Finset.sum _ _), Finset.sum_mul]
  congr 1
  · rw [show (-(↑(0 : ℕ) + 1 : ℤ)) = (-1 : ℤ) by norm_num, zpow_neg_one, div_eq_mul_inv]
  · refine Finset.sum_congr rfl fun i hi => ?_
    rw [Function.Embedding.coeFn_mk]
    have hpow : (p : ℚ) ^ (-(↑(i + 1) + 1 : ℤ))
        = (p : ℚ) ^ (-(↑i + 1 : ℤ)) * (p : ℚ)⁻¹ := by
      rw [← zpow_neg_one (p : ℚ), ← zpow_add₀ hpne,
        show ((-(↑i + 1) + -1 : ℤ)) = (-(↑(i + 1) + 1 : ℤ)) by push_cast; ring]
    rw [hpow]
    ring

omit hp in
/-- Pointwise description of `gapDig`. -/
theorem gapDig_apply (j n : ℕ) (b : ℕ →₀ ℕ) (i : ℕ) :
    gapDig j n b i
      = if i < j - 1 then b i else if j - 1 + n ≤ i then b (i - n) else 0 := by
  rw [gapDig, Finsupp.add_apply, Finsupp.filter_apply]
  have hemb : Finsupp.embDomain ⟨fun i => i + n, add_left_injective n⟩
      (b.filter (fun i => j - 1 ≤ i)) i
        = if j - 1 + n ≤ i then b (i - n) else 0 := by
    by_cases hn : n ≤ i
    · conv_lhs => rw [show i = (i - n) + n by omega,
        show ((i - n) + n) = (⟨fun i => i + n, add_left_injective n⟩ : ℕ ↪ ℕ) (i - n)
          from rfl]
      rw [Finsupp.embDomain_apply_self, Finsupp.filter_apply]
      by_cases hb : j - 1 ≤ i - n
      · rw [if_pos hb, if_pos (by omega)]
      · rw [if_neg hb, if_neg (by omega)]
    · rw [Finsupp.embDomain_of_notMem_range _ _ _
        (by rintro ⟨k, hk⟩; simp only [Function.Embedding.coeFn_mk] at hk; omega),
        if_neg (by omega)]
  rw [hemb]
  by_cases h1 : i < j - 1
  · rw [if_pos h1, if_pos h1, if_neg (by omega), add_zero]
  · rw [if_neg h1, if_neg h1, zero_add]

omit hp in
/-- Pointwise description of `consDig`. -/
theorem consDig_apply (v : ℕ) (d : ℕ →₀ ℕ) (i : ℕ) :
    consDig v d i = if i = 0 then v else d (i - 1) := by
  cases i with
  | zero =>
    rw [if_pos rfl, consDig, Finsupp.add_apply, Finsupp.single_eq_same,
      Finsupp.embDomain_of_notMem_range _ _ _
        (by rintro ⟨k, hk⟩; simp only [Function.Embedding.coeFn_mk] at hk; omega),
      add_zero]
  | succ i =>
    rw [if_neg (by omega), consDig, Finsupp.add_apply, Finsupp.single_eq_of_ne (by omega),
      show (i + 1) = (⟨fun i => i + 1, add_left_injective 1⟩ : ℕ ↪ ℕ) i from rfl,
      Finsupp.embDomain_apply_self, zero_add]
    rfl

omit hp in
/-- Prepending a digit commutes with gap insertion, moving the gap position by one:
the digits of `(v + w)/p` with gap at `j + 1` are the digits of `w` with gap at `j`,
prepended by `v`. -/
theorem gapDig_consDig {j : ℕ} (hj : 0 < j) (n v : ℕ) (dig : ℕ →₀ ℕ) :
    gapDig (j + 1) n (consDig v dig) = consDig v (gapDig j n dig) := by
  ext i
  simp only [gapDig_apply, consDig_apply]
  split_ifs <;> first | rfl | (exfalso; omega) | (congr 1; omega)

omit hp in
/-- Dropping the leading digit commutes with gap insertion for gap position `≥ 2`. -/
theorem unshiftDig_gapDig {j : ℕ} (hj : 2 ≤ j) (n : ℕ) (dig : ℕ →₀ ℕ) :
    unshiftDig (gapDig j n dig) = gapDig (j - 1) n (unshiftDig dig) := by
  ext i
  simp only [unshiftDig_apply, gapDig_apply]
  split_ifs <;> first | rfl | (exfalso; omega) | (congr 1; omega)

omit hp in
/-- For gap position `1`, dropping the leading digit shrinks the gap by one. -/
theorem unshiftDig_gapDig_one (n : ℕ) (dig : ℕ →₀ ℕ) :
    unshiftDig (gapDig 1 (n + 1) dig) = gapDig 1 n dig := by
  ext i
  simp only [unshiftDig_apply, gapDig_apply]
  split_ifs <;> first | rfl | (exfalso; omega) | (congr 1; omega)

omit hp in
/-- For gap position `≥ 2` the leading digit survives gap insertion. -/
theorem gapDig_apply_zero {j : ℕ} (hj : 2 ≤ j) (n : ℕ) (dig : ℕ →₀ ℕ) :
    gapDig j n dig 0 = dig 0 := by
  rw [gapDig_apply, if_pos (by omega)]

omit hp in
/-- For gap position `1` and a positive gap the leading digit is `0`. -/
theorem gapDig_one_apply_zero (n : ℕ) (dig : ℕ →₀ ℕ) :
    gapDig 1 (n + 1) dig 0 = 0 := by
  rw [gapDig_apply, if_neg (by omega), if_neg (by omega)]

/-- **Scaling by `p`**: `p · S_{a,b,c} ⊆ S_{a, pb+(p-1), c}`.  Digits shift up one
position; the leading fractional digit joins the integer part, so the digit-sum level
is unchanged. -/
theorem Sabc_mem_p_mul {a : ℕ+} {b c : ℕ} {s : ℚ} (hs : s ∈ Sabc p a b c) :
    (p : ℚ) * s ∈ Sabc p a (p * b + (p - 1)) c := by
  obtain ⟨n, d, hn, hd, hsum, rfl⟩ := hs
  have hp2 : 2 ≤ p := hp.out.two_le
  refine ⟨p * n - d 0, unshiftDig d, ?_, fun i => hd (i + 1), ?_, ?_⟩
  · -- `-(pb + (p-1)) ≤ pn - d₀` from `n ≥ -b` and `d₀ ≤ p - 1`.
    have h1 : (p : ℤ) * (-(b : ℤ)) ≤ (p : ℤ) * n :=
      mul_le_mul_of_nonneg_left hn (by positivity)
    have h2 : (d 0 : ℤ) < (p : ℤ) := by exact_mod_cast hd 0
    have h3 : ((p - 1 : ℕ) : ℤ) = (p : ℤ) - 1 := by omega
    push_cast [h3]
    linarith
  · exact (unshiftDig_sum_le d).trans hsum
  · rw [fracVal_def, fracVal_def]
    have hkey := p_mul_fracVal p hp.out.pos d
    push_cast
    linear_combination (-(1 / (a : ℚ))) * hkey

/-- **Scaling by `p⁻¹`**: `(1/p) · S_{a,b,c} ⊆ S_{a, b, c+(p-1)}`.  Digits shift down
one position; the residue of the integer part mod `p` becomes a new leading fractional
digit of size at most `p - 1`. -/
theorem Sabc_mem_div_p {a : ℕ+} {b c : ℕ} {s : ℚ} (hs : s ∈ Sabc p a b c) :
    s / p ∈ Sabc p a b (c + (p - 1)) := by
  obtain ⟨n, d, hn, hd, hsum, rfl⟩ := hs
  have hp2 : 2 ≤ p := hp.out.two_le
  have hppos : (0 : ℤ) < (p : ℤ) := by positivity
  have hpne : ((p : ℚ)) ≠ 0 := by positivity
  set q : ℤ := n / p with hq
  set r : ℤ := n % p with hr
  have hnqr : r + (p : ℤ) * q = n := by rw [hr, hq, Int.emod_def]; ring
  have hr0 : 0 ≤ r := Int.emod_nonneg n (by omega)
  have hrp : r < p := Int.emod_lt_of_pos n hppos
  -- The new integer part is at least `-b` in both cases below.
  have hqb : -(b : ℤ) ≤ q := by
    by_contra hcon
    have h1 : q ≤ -(b : ℤ) - 1 := by omega
    have h2 : (p : ℤ) * q ≤ (p : ℤ) * (-(b : ℤ) - 1) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have h3 : ((b : ℤ)) ≤ (p : ℤ) * b :=
      le_mul_of_one_le_left (by positivity) (by exact_mod_cast hp.out.one_lt.le)
    have h4 : (p : ℤ) * (-(b : ℤ) - 1) = -((p : ℤ) * b) - p := by ring
    linarith
  rcases eq_or_lt_of_le hr0 with hr' | hr'
  · -- `r = 0`: no new digit, `s/p = (1/a)(q - fracVal (consDig 0 d))`… with zero digit.
    refine ⟨q, consDig 0 d, hqb, consDig_lt p (by omega) hd, ?_, ?_⟩
    · rw [consDig_sum]
      omega
    · rw [fracVal_def, fracVal_def, fracVal_consDig p (by omega)]
      have hane : ((a : ℚ)) ≠ 0 := by exact_mod_cast a.pos.ne'
      have hncast : (n : ℚ) = (r : ℚ) + (p : ℚ) * (q : ℚ) := by exact_mod_cast hnqr.symm
      have hrq : (r : ℚ) = 0 := by exact_mod_cast hr'.symm
      rw [hncast, hrq]
      push_cast
      field_simp
      ring
  · -- `r ≥ 1`: the residue becomes the new leading digit `p - r`.
    refine ⟨q + 1, consDig (p - r).toNat d, by omega,
      consDig_lt p (by omega) hd, ?_, ?_⟩
    · rw [consDig_sum]
      have : (p - r).toNat ≤ p - 1 := by omega
      omega
    · rw [fracVal_def, fracVal_def, fracVal_consDig p (by omega)]
      have hane : ((a : ℚ)) ≠ 0 := by exact_mod_cast a.pos.ne'
      have htn : (((p - r).toNat : ℕ) : ℚ) = (p : ℚ) - (r : ℚ) := by
        rw [show (((p - r).toNat : ℕ) : ℚ) = (((p - r).toNat : ℤ) : ℚ) by push_cast; ring,
          Int.toNat_of_nonneg (by omega)]
        push_cast
        ring
      have hncast : (n : ℚ) = (r : ℚ) + (p : ℚ) * (q : ℚ) := by exact_mod_cast hnqr.symm
      rw [htn, hncast]
      push_cast
      field_simp
      ring

end TrustworthyKedlaya.UP
