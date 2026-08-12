/-
Copyright (c) 2026 Shanwen Wang, Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import TrustworthyKedlaya.PAdicHahnSeries
public import Mathlib.Data.PNat.Prime

/-!
# Uniformly periodic coefficient functions and series

For `K = 𝔽̄_p`, the twist-recurrence machinery of Kedlaya (2001a) degenerates to a
*uniform eventual periodicity* condition on twist sequences, which is exactly the form
of `kedlaya_2001a_theorem15_half`.  This file sets up that invariant and its basic
calculus: the support sets `S_{a,b,c}`, twist sequences, `(M, N)`-periodicity at a
digit-sum level `c`, uniformly periodic (UP) Hahn series, and the closure properties
that only involve reindexing and value-wise operations.

## Main definitions

- `TrustworthyKedlaya.UP.Sabc`, `TrustworthyKedlaya.UP.Tc`, `TrustworthyKedlaya.UP.twistSeq`:
  definitionally identical copies of the definitions accompanying the target statement
  (kept in a separate namespace so that this file can sit *below* the statement file in
  the import graph; the final glue identifies them by `rfl`).
- `TrustworthyKedlaya.UP.IsTwistPeriodic`: `f` is `(M, N)`-periodic at level `c` if every
  twist sequence of `f` with digit sum at most `c` satisfies `c_{n+N} = c_n` for `n ≥ M`.
- `TrustworthyKedlaya.UP.IsUP`: a Hahn series in `𝔽̄_p((t^ℚ))` is *uniformly periodic*:
  supported on some `S_{a,b,c}`, with all slice functions `f_m` uniformly
  `(M, N)`-periodic at level `c`.

## References

- K. S. Kedlaya, *The algebraic closure of the power series field in positive
  characteristic*, Proc. Amer. Math. Soc. 129 (2001) [Ked01a].
- K. S. Kedlaya, *On the algebraicity of generalized power series*, Beiträge Algebra
  Geom. 58 (2017) [Ked17], Sections 1-2 (validity of [Ked01a] for `K = 𝔽̄_p`).
-/

@[expose] public section

namespace TrustworthyKedlaya.UP

variable (p : ℕ) [Fact (Nat.Prime p)]

/-- The support set `S_{a,b,c}` of Kedlaya (2017), Definition 2.1 (definitionally equal
copy of the one fixed alongside the target statement).  For a positive integer `a`, an
integer `b` and a nonnegative integer `c`,
`S_{a,b,c} = { (1/a)(n - ∑_{i≥1} bᵢ p^{-i}) : n ∈ ℤ, n ≥ -b, bᵢ ∈ {0,…,p-1}, ∑ bᵢ ≤ c }`,
with the base-`p` digit sequence modelled as a finitely-supported `d : ℕ →₀ ℕ`. -/
def Sabc (a : ℕ+) (b c : ℕ) : Set ℚ :=
  { s : ℚ | ∃ (n : ℤ) (d : ℕ →₀ ℕ),
      -b ≤ n ∧ (∀ i, d i < p) ∧ (d.sum fun _ v => v) ≤ c ∧
      s = (1 / (a : ℚ)) *
        ((n : ℚ) - d.sum fun i v => (v : ℚ) * (p : ℚ) ^ (-(i + 1 : ℤ))) }

/-- The slice `T_c = S_{1,0,c} ∩ (-1, 0)` of Kedlaya (2017), Definition 2.3. -/
def Tc (c : ℕ) : Set ℚ := Sabc p 1 0 c ∩ Set.Ioo (-1) 0

/-- The twist-input sequence `(cₙ)` of Kedlaya (2017), Definition 2.3, eq. (2.2), with
the corrected minus sign (definitionally equal copy of the one fixed alongside the
target statement): for `f : ℚ → 𝔽̄_p`, a positive integer `j` and digits `b : ℕ →₀ ℕ`,
`cₙ = f( -∑_{i < j-1} bᵢ p^{-(i+1)} − p^{-n} · ∑_{i ≥ j-1} bᵢ p^{-(i+1)} )`. -/
def twistSeq (f : ℚ → 𝔽ᵃ_[p]) (j : ℕ) (b : ℕ →₀ ℕ) (n : ℕ) : 𝔽ᵃ_[p] :=
  f (-(∑ i ∈ Finset.range (j - 1), (b i : ℚ) * (p : ℚ) ^ (-(i + 1 : ℤ)))
     - (p : ℚ) ^ (-(n : ℤ)) *
        ∑ i ∈ b.support.filter (fun i => j - 1 ≤ i), (b i : ℚ) * (p : ℚ) ^ (-(i + 1 : ℤ)))

omit [Fact (Nat.Prime p)] in
/-- `S_{a,b,c}` is monotone in the parameters `b` and `c`. -/
lemma Sabc_mono (a : ℕ+) {b b' c c' : ℕ} (hb : b ≤ b') (hc : c ≤ c') :
    Sabc p a b c ⊆ Sabc p a b' c' := by
  rintro s ⟨n, d, hn, hd, hsum, rfl⟩
  exact ⟨n, d, le_trans (by exact_mod_cast neg_le_neg (Int.ofNat_le.mpr hb)) hn, hd,
    hsum.trans hc, rfl⟩

/-- A function `f : ℚ → 𝔽̄_p` is `(M, N)`-periodic at level `c` if every twist sequence
of `f` built from digits `< p` with digit sum at most `c` satisfies `cₙ₊N = cₙ` for all
`n ≥ M`.  This is the specialization to `K = 𝔽̄_p` of twist-recurrence (Kedlaya (2001a),
Definition 5 together with Lemma 13 there), and it is the invariant carried through the
whole Artin-Schreier tower induction. -/
def IsTwistPeriodic (f : ℚ → 𝔽ᵃ_[p]) (c : ℕ) (M N : ℕ+) : Prop :=
  ∀ (j : ℕ) (dig : ℕ →₀ ℕ), 0 < j → (∀ i, dig i < p) → (dig.sum fun _ v => v) ≤ c →
    ∀ n : ℕ, (M : ℕ) ≤ n → twistSeq p f j dig (n + N) = twistSeq p f j dig n

/-- A Hahn series `x ∈ 𝔽̄_p((t^ℚ))` is *uniformly periodic* (UP) if its support lies in
some `S_{a,b,c}` and, for a single pair `(M, N)`, every slice function
`f_m(z) = x_{(m+z)/a}` (`m ≥ -b`) is `(M, N)`-periodic at level `c`.  This is exactly
the conclusion of `kedlaya_2001a_theorem15_half`. -/
def IsUP (x : HahnSeries ℚ (𝔽ᵃ_[p])) : Prop :=
  ∃ (a : ℕ+) (b c : ℕ), x.support ⊆ Sabc p a b c ∧
    ∃ M N : ℕ+, ∀ m : ℤ, -(b : ℤ) ≤ m →
      IsTwistPeriodic p (fun z => x.coeff (((m : ℚ) + z) / (a : ℚ))) c M N

variable {p}

/-- Twist sequences are computed pointwise, so post-composition with any function of the
values commutes with taking twist sequences. -/
lemma twistSeq_comp (φ : 𝔽ᵃ_[p] → 𝔽ᵃ_[p]) (f : ℚ → 𝔽ᵃ_[p]) (j : ℕ) (b : ℕ →₀ ℕ)
    (n : ℕ) : twistSeq p (fun z => φ (f z)) j b n = φ (twistSeq p f j b n) := rfl

/-- Twist sequences of a pointwise sum are the termwise sums of twist sequences. -/
lemma twistSeq_add (f g : ℚ → 𝔽ᵃ_[p]) (j : ℕ) (b : ℕ →₀ ℕ) (n : ℕ) :
    twistSeq p (fun z => f z + g z) j b n = twistSeq p f j b n + twistSeq p g j b n := rfl

/-- Constant functions are `(M, N)`-periodic at every level. -/
lemma isTwistPeriodic_const (v : 𝔽ᵃ_[p]) (c : ℕ) (M N : ℕ+) :
    IsTwistPeriodic p (fun _ => v) c M N := fun _ _ _ _ _ _ _ => rfl

/-- Periodicity is preserved by post-composition with any function of the values.
This subsumes scalar multiplication, Frobenius and inverse Frobenius on values. -/
lemma IsTwistPeriodic.comp {f : ℚ → 𝔽ᵃ_[p]} {c : ℕ} {M N : ℕ+}
    (h : IsTwistPeriodic p f c M N) (φ : 𝔽ᵃ_[p] → 𝔽ᵃ_[p]) :
    IsTwistPeriodic p (fun z => φ (f z)) c M N :=
  fun j dig hj hd hs n hn => congrArg φ (h j dig hj hd hs n hn)

/-- Periodicity persists when the preperiod grows, the period is replaced by a positive
multiple, and the digit-sum level shrinks. -/
lemma IsTwistPeriodic.mono {f : ℚ → 𝔽ᵃ_[p]} {c c' : ℕ} {M M' N N' : ℕ+}
    (h : IsTwistPeriodic p f c M N) (hc : c' ≤ c) (hM : (M : ℕ) ≤ (M' : ℕ))
    (hN : (N : ℕ) ∣ (N' : ℕ)) : IsTwistPeriodic p f c' M' N' := by
  intro j dig hj hd hs n hn
  obtain ⟨k, hk⟩ := hN
  -- Iterate the base period `k` times.
  have key : ∀ k' : ℕ, twistSeq p f j dig (n + N * k') = twistSeq p f j dig n := by
    intro k'
    induction k' with
    | zero => rfl
    | succ k' ih =>
      have hstep : twistSeq p f j dig ((n + N * k') + N) = twistSeq p f j dig (n + N * k') :=
        h j dig hj hd (hs.trans hc) (n + N * k')
          (le_trans (le_trans hM hn) (Nat.le_add_right n _))
      calc twistSeq p f j dig (n + N * (k' + 1))
          = twistSeq p f j dig ((n + N * k') + N) := by ring_nf
        _ = twistSeq p f j dig (n + N * k') := hstep
        _ = twistSeq p f j dig n := ih
  simpa [hk] using key k

/-- The sum of two periodic functions is periodic, with preperiod the maximum and period
the least common multiple of the originals. -/
lemma IsTwistPeriodic.add {f g : ℚ → 𝔽ᵃ_[p]} {c : ℕ} {Mf Mg Nf Ng : ℕ+}
    (hf : IsTwistPeriodic p f c Mf Nf) (hg : IsTwistPeriodic p g c Mg Ng) :
    IsTwistPeriodic p (fun z => f z + g z) c (max Mf Mg) (Nf.lcm Ng) := by
  have hf' : IsTwistPeriodic p f c (max Mf Mg) (Nf.lcm Ng) :=
    hf.mono le_rfl (by exact_mod_cast le_max_left Mf Mg)
      (PNat.dvd_iff.mp (PNat.dvd_lcm_left Nf Ng))
  have hg' : IsTwistPeriodic p g c (max Mf Mg) (Nf.lcm Ng) :=
    hg.mono le_rfl (by exact_mod_cast le_max_right Mf Mg)
      (PNat.dvd_iff.mp (PNat.dvd_lcm_right Nf Ng))
  intro j dig hj hd hs n hn
  rw [twistSeq_add, twistSeq_add, hf' j dig hj hd hs n hn, hg' j dig hj hd hs n hn]

/-- At digit-sum level `0` every twist sequence is constant (all digits vanish, so the
evaluation point is `0` independently of the gap), hence every function is
`(M, N)`-periodic at level `0`. -/
lemma isTwistPeriodic_zero_level (f : ℚ → 𝔽ᵃ_[p]) (M N : ℕ+) :
    IsTwistPeriodic p f 0 M N := by
  intro j dig hj hdig hsum n hn
  have hdig0 : dig = 0 := by
    ext i
    simp only [Finsupp.coe_zero, Pi.zero_apply]
    by_contra hi
    have hle := Finset.single_le_sum (f := fun i => dig i) (fun i _ => Nat.zero_le _)
      (Finsupp.mem_support_iff.mpr hi)
    rw [Finsupp.sum] at hsum
    omega
  subst hdig0
  simp [twistSeq]

/-- **Laurent series are UP**: any Hahn series supported on `(1/n)·ℤ` — that is, any
element of `𝔽̄_p((t^{1/n})) ⊆ 𝔽̄_p((t^ℚ))` — is uniformly periodic, with digit-sum
level `0` and constant twist sequences. -/
theorem isUP_of_support_int_div (n : ℕ+) {x : HahnSeries ℚ (𝔽ᵃ_[p])}
    (hsupp : ∀ s ∈ x.support, ∃ k : ℤ, s = (k : ℚ) / (n : ℚ)) : IsUP p x := by
  have hn0 : (0 : ℚ) < (n : ℚ) := by exact_mod_cast n.pos
  rcases eq_or_ne x 0 with rfl | hx0
  · refine ⟨n, 0, 0, ?_, 1, 1, fun m _ => isTwistPeriodic_zero_level _ 1 1⟩
    simp
  · -- Bound the support below by its minimum.
    have hne : x.support.Nonempty := HahnSeries.support_nonempty_iff.mpr hx0
    obtain ⟨k₀, hk₀⟩ := hsupp _ (x.isWF_support.min_mem hne)
    refine ⟨n, (-k₀).toNat, 0, ?_, 1, 1, fun m _ => isTwistPeriodic_zero_level _ 1 1⟩
    intro s hs
    obtain ⟨k, hk⟩ := hsupp s hs
    have hmin : x.isWF_support.min hne ≤ s := Set.IsWF.min_le _ hne hs
    have hkk : k₀ ≤ k := by
      rw [hk₀, hk] at hmin
      have h1 := mul_le_mul_of_nonneg_right hmin hn0.le
      rw [div_mul_cancel₀ _ hn0.ne', div_mul_cancel₀ _ hn0.ne'] at h1
      exact_mod_cast h1
    refine ⟨k, 0, by omega, fun i => (Fact.out : p.Prime).pos, by simp, ?_⟩
    rw [hk, Finsupp.sum_zero_index]
    ring

/-! ### Periodicity from a Frobenius-affine recursion

The engine behind Artin-Schreier stability of UP (Kedlaya (2001a), proof of Lemma 4):
a sequence solving `c_{n+1}^p = c_n + y_n` with values in a finite subfield `𝔽_{p^d}`,
where `(y_n)` is eventually `N`-periodic, is itself eventually `N·p·d`-periodic.
Membership in `𝔽_{p^d}` is phrased as the fixed-point equation `x ^ p ^ d = x`. -/

/-- Elements of the finite subfield `𝔽_{p^d} = {x : x^{p^d} = x}` are fixed by
`p^{d·k}`-th powers for every `k`. -/
lemma pow_pow_mul_eq_self {x : 𝔽ᵃ_[p]} {d : ℕ} (hx : x ^ p ^ d = x) (k : ℕ) :
    x ^ p ^ (d * k) = x := by
  induction k with
  | zero => simp
  | succ k ih => rw [Nat.mul_succ, pow_add, pow_mul, ih, hx]

/-- Iterating eventual periodicity. -/
lemma eventually_periodic_iterate {y : ℕ → 𝔽ᵃ_[p]} {M N : ℕ}
    (hyp : ∀ n, M ≤ n → y (n + N) = y n) (k : ℕ) :
    ∀ n, M ≤ n → y (n + N * k) = y n := by
  induction k with
  | zero => simp
  | succ k ih =>
    intro n hn
    have h1 : n + N * (k + 1) = (n + N * k) + N := by ring
    rw [h1, hyp _ (le_trans hn (Nat.le_add_right _ _)), ih n hn]

/-- Telescoping the Frobenius-affine recursion `c_{n+1}^p = c_n + y_n`:
`c_{n+m}^{p^m} = c_n + ∑_{i<m} y_{n+i}^{p^i}`. -/
lemma pow_pow_of_frobenius_affine {c y : ℕ → 𝔽ᵃ_[p]}
    (hrec : ∀ n, c (n + 1) ^ p = c n + y n) (n : ℕ) :
    ∀ m, c (n + m) ^ p ^ m = c n + ∑ i ∈ Finset.range m, y (n + i) ^ p ^ i := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
    calc c (n + (m + 1)) ^ p ^ (m + 1)
        = c ((n + m) + 1) ^ p ^ (m + 1) := rfl
      _ = (c ((n + m) + 1) ^ p) ^ p ^ m := by rw [← pow_mul, ← pow_succ']
      _ = (c (n + m) + y (n + m)) ^ p ^ m := by rw [hrec]
      _ = c (n + m) ^ p ^ m + y (n + m) ^ p ^ m := by rw [add_pow_char_pow]
      _ = c n + (∑ i ∈ Finset.range m, y (n + i) ^ p ^ i) + y (n + m) ^ p ^ m := by
          rw [ih]
      _ = c n + ∑ i ∈ Finset.range (m + 1), y (n + i) ^ p ^ i := by
          rw [Finset.sum_range_succ, add_assoc]

/-- **Periodicity from a Frobenius-affine recursion** (the orbit lemma of Kedlaya
(2001a)).  Let `c, y : ℕ → 𝔽̄_p` take values in the finite subfield `𝔽_{p^d}` (cut out
by `x^{p^d} = x`), let `y_{n+N} = y_n` for `n ≥ M`, and let `c_{n+1}^p = c_n + y_n`
for all `n`.  Then `c_{n + N·p·d} = c_n` for all `n ≥ M`: the solution is eventually
periodic with period `N·p·d` and the same preperiod `M`. -/
theorem eventually_periodic_of_frobenius_affine {c y : ℕ → 𝔽ᵃ_[p]} {d M N : ℕ}
    (hc : ∀ n, c n ^ p ^ d = c n) (hy : ∀ n, y n ^ p ^ d = y n)
    (hyp : ∀ n, M ≤ n → y (n + N) = y n)
    (hrec : ∀ n, c (n + 1) ^ p = c n + y n) :
    ∀ n, M ≤ n → c (n + N * p * d) = c n := by
  intro n hn
  have key := pow_pow_of_frobenius_affine hrec n (N * p * d)
  -- `p^{Npd}`-th powers fix the subfield, so the left side is `c_{n+Npd}` itself.
  have hfix : c (n + N * p * d) ^ p ^ (N * p * d) = c (n + N * p * d) := by
    have h1 : N * p * d = d * (N * p) := by ring
    rw [h1]
    exact pow_pow_mul_eq_self (hc _) _
  -- Each of the `p` blocks of `N·d` consecutive correction terms has the same sum.
  have hblock : ∀ r : ℕ,
      (∑ j ∈ Finset.range (N * d), y (n + (N * d * r + j)) ^ p ^ (N * d * r + j))
        = ∑ j ∈ Finset.range (N * d), y (n + j) ^ p ^ j := by
    intro r
    refine Finset.sum_congr rfl fun j _ => ?_
    have hidx : n + (N * d * r + j) = (n + j) + N * (d * r) := by ring
    have hy1 : y (n + (N * d * r + j)) = y (n + j) := by
      rw [hidx]
      exact eventually_periodic_iterate hyp (d * r) (n + j)
        (le_trans hn (Nat.le_add_right n j))
    have hexp : (y (n + j) : 𝔽ᵃ_[p]) ^ p ^ (N * d * r + j)
        = (y (n + j) ^ p ^ (N * d * r)) ^ p ^ j := by
      rw [← pow_mul, ← pow_add]
    have hyfix : y (n + j) ^ p ^ (N * d * r) = y (n + j) := by
      have h2 : N * d * r = d * (N * r) := by ring
      rw [h2]
      exact pow_pow_mul_eq_self (hy _) _
    rw [hy1, hexp, hyfix]
  -- Hence the whole correction sum is `p` times one block, which vanishes in char `p`.
  have hsum : ∑ i ∈ Finset.range (N * p * d), y (n + i) ^ p ^ i = 0 := by
    have hsplit : ∀ r : ℕ,
        (∑ i ∈ Finset.range (N * d * r), y (n + i) ^ p ^ i)
          = r • ∑ j ∈ Finset.range (N * d), y (n + j) ^ p ^ j := by
      intro r
      induction r with
      | zero => simp
      | succ r ih =>
        have h3 : N * d * (r + 1) = N * d * r + N * d := by ring
        rw [h3, Finset.sum_range_add, ih, hblock r, succ_nsmul]
    have hm : N * p * d = N * d * p := by ring
    rw [hm, hsplit p, nsmul_eq_mul, CharP.cast_eq_zero (𝔽ᵃ_[p]) p, zero_mul]
  rw [hfix, hsum, add_zero] at key
  exact key

/-- **Artin-Schreier roots of constants**: `𝔽̄_p` is algebraically closed, so every
`l` is `m^p - m` for some `m`. -/
theorem exists_artinSchreier_root (l : 𝔽ᵃ_[p]) : ∃ m : 𝔽ᵃ_[p], m ^ p - m = l := by
  have hp1 : (1 : WithBot ℕ) < (p : WithBot ℕ) := by
    exact_mod_cast (Fact.out : p.Prime).one_lt
  have hdlt : (Polynomial.X + Polynomial.C l : Polynomial (𝔽ᵃ_[p])).degree
      < (Polynomial.X ^ p : Polynomial (𝔽ᵃ_[p])).degree := by
    rw [Polynomial.degree_X_pow]
    refine lt_of_le_of_lt (Polynomial.degree_add_le _ _) (max_lt ?_ ?_)
    · rw [Polynomial.degree_X]
      exact hp1
    · refine lt_of_le_of_lt Polynomial.degree_C_le ?_
      exact_mod_cast (Fact.out : p.Prime).pos
  have hdeg : (Polynomial.X ^ p - Polynomial.X - Polynomial.C l
      : Polynomial (𝔽ᵃ_[p])).degree ≠ 0 := by
    rw [sub_sub, Polynomial.degree_sub_eq_left_of_degree_lt hdlt, Polynomial.degree_X_pow]
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root _ hdeg
  refine ⟨x, ?_⟩
  simp only [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_C] at hx
  exact sub_eq_zero.mp (by linear_combination hx)

end TrustworthyKedlaya.UP
