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

end TrustworthyKedlaya.UP
