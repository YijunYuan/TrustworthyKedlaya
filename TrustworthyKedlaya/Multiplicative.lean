/-
Copyright (c) 2026 Shanwen Wang, Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import TrustworthyKedlaya.GapContraction
public import TrustworthyKedlaya.Rescale

/-!
# UP is stable under multiplication

The coefficient of `x * y` at a twist evaluation point is a finite sum, over the
antidiagonal of the supports, of products of coefficients of `x` and `y`.  Each
support point of a factor splits uniquely into an integer slice index and the value
of a canonical digit string (`sliceInt` / `sliceDig`), the exponent equation splits
into an integer carry `κ ∈ {0,1}` and a decomposition of the gapped target
(`decomp_point_split`), and the gap-contraction machinery
(`TrustworthyKedlaya.GapContraction`) matches the decompositions at gap size `n`
with those at any other gap size `≥ n₀ = c₁+c₂+1`, componentwise along twist
families of the contracted strings.  Transporting each antidiagonal term along this
matching identifies the twist sequence of a slice of `x * y` beyond
`max(M₁,M₂) + K + n₀` with a sum of products of twist-sequence values of slices of
`x` and `y` at the index shifted by the gap-tail position, so it inherits
periodicity `lcm(N₁,N₂)`.

## Main statements

- `TrustworthyKedlaya.UP.sliceInt` / `TrustworthyKedlaya.UP.sliceDig`: the canonical
  integer/digit-string decomposition of a support point, with uniqueness
  (`sliceInt_eq`, `sliceDig_eq`) and existence on `S_{a,b,c}` (`Sabc_sliceDig`).
- `TrustworthyKedlaya.UP.decomp_point_split`: the integer-carry split of a sum of
  two support points against a gapped target.

## References

- K. S. Kedlaya, *The algebraic closure of the power series field in positive
  characteristic*, Proc. Amer. Math. Soc. 129 (2001) [Ked01a], proof of Lemma 4.
-/

@[expose] public section

namespace TrustworthyKedlaya.UP

open Finset

variable (p : ℕ) [hp : Fact (Nat.Prime p)]

/-! ### The canonical decomposition of a support point -/

/-- The integer part of a support point at width `a`: for `s = (1/a)(m - w)` with
`w ∈ [0, 1)`, the ceiling of `a·s` recovers `m`. -/
noncomputable def sliceInt (a : ℕ+) (s : ℚ) : ℤ := ⌈(a : ℚ) * s⌉

open Classical in
/-- The canonical digit string of a support point at width `a`: the unique finitely
supported string of digits `< p` whose value is the fractional defect
`sliceInt a s - a·s`, when one exists (junk value `0` otherwise). -/
noncomputable def sliceDig (a : ℕ+) (s : ℚ) : ℕ →₀ ℕ :=
  if h : ∃ u : ℕ →₀ ℕ, (∀ i, u i < p) ∧ (a : ℚ) * s = (sliceInt a s : ℚ) - fracVal p u
  then h.choose else 0

omit hp in
/-- The integer part of a canonical presentation is recovered by `sliceInt`. -/
theorem sliceInt_eq (hp1 : 1 < p) {a : ℕ+} {s : ℚ} {m : ℤ} {u : ℕ →₀ ℕ}
    (hu : ∀ i, u i < p) (h : (a : ℚ) * s = (m : ℚ) - fracVal p u) :
    sliceInt a s = m := by
  have h0 := fracVal_nonneg p u
  have h1 := fracVal_lt_one p hp1 hu
  rw [sliceInt, Int.ceil_eq_iff]
  constructor
  · linarith
  · linarith

/-- The digit string of a canonical presentation is recovered by `sliceDig`. -/
theorem sliceDig_eq {a : ℕ+} {s : ℚ} {m : ℤ} {u : ℕ →₀ ℕ}
    (hu : ∀ i, u i < p) (h : (a : ℚ) * s = (m : ℚ) - fracVal p u) :
    sliceDig p a s = u := by
  have hm := sliceInt_eq p hp.out.one_lt hu h
  have hex : ∃ u' : ℕ →₀ ℕ, (∀ i, u' i < p) ∧
      (a : ℚ) * s = (sliceInt a s : ℚ) - fracVal p u' := ⟨u, hu, by rw [hm]; exact h⟩
  rw [sliceDig, dif_pos hex]
  obtain ⟨hd, hveq⟩ := hex.choose_spec
  have hmq : ((sliceInt a s : ℤ) : ℚ) = (m : ℚ) := by exact_mod_cast hm
  refine eq_of_fracVal_eq p hp.out.one_lt hd hu ?_
  linarith [hveq, h, hmq]

/-- Every point of `S_{a,b,c}` decomposes canonically through `sliceInt` and
`sliceDig`: digits `< p`, digit sum `≤ c`, slice index `≥ -b`, and the defining
equation `a·s = sliceInt a s - fracVal (sliceDig a s)`. -/
theorem Sabc_sliceDig {a : ℕ+} {b c : ℕ} {s : ℚ} (hs : s ∈ Sabc p a b c) :
    (∀ i, sliceDig p a s i < p) ∧ ((sliceDig p a s).sum fun _ v => v) ≤ c ∧
      -(b : ℤ) ≤ sliceInt a s ∧
      (a : ℚ) * s = (sliceInt a s : ℚ) - fracVal p (sliceDig p a s) := by
  obtain ⟨n, d, hn, hd, hsum, rfl⟩ := hs
  have ha : ((a : ℚ)) ≠ 0 := by exact_mod_cast a.pos.ne'
  have heq : (a : ℚ) * ((1 / (a : ℚ)) *
      ((n : ℚ) - d.sum fun i v => (v : ℚ) * (p : ℚ) ^ (-(i + 1 : ℤ))))
      = (n : ℚ) - fracVal p d := by
    rw [fracVal_def]
    field_simp
  rw [sliceDig_eq p hd heq, sliceInt_eq p hp.out.one_lt hd heq]
  exact ⟨hd, hsum, hn, heq⟩

/-- **The integer-carry split**: if two canonically presented points sum to a
canonically presented target, the fractional parts decompose the target's string up
to an integer carry `κ ∈ {0,1}` absorbed by the slice indices. -/
theorem decomp_point_split {m₁ m₂ m : ℤ} {u v g : ℕ →₀ ℕ}
    (hu : ∀ i, u i < p) (hv : ∀ i, v i < p) (hg : ∀ i, g i < p)
    (h : ((m₁ : ℚ) - fracVal p u) + ((m₂ : ℚ) - fracVal p v)
      = (m : ℚ) - fracVal p g) :
    ∃ κ : ℕ, κ ≤ 1 ∧ m₁ + m₂ = m + κ ∧
      fracVal p u + fracVal p v = (κ : ℚ) + fracVal p g := by
  have hp1 := hp.out.one_lt
  have hcast : ((m₁ + m₂ - m : ℤ) : ℚ) = fracVal p u + fracVal p v - fracVal p g := by
    push_cast
    linarith
  have hu0 := fracVal_nonneg p u
  have hv0 := fracVal_nonneg p v
  have hg0 := fracVal_nonneg p g
  have hu1 := fracVal_lt_one p hp1 hu
  have hv1 := fracVal_lt_one p hp1 hv
  have hg1 := fracVal_lt_one p hp1 hg
  have hlo : (-1 : ℚ) < ((m₁ + m₂ - m : ℤ) : ℚ) := by rw [hcast]; linarith
  have hhi : ((m₁ + m₂ - m : ℤ) : ℚ) < 2 := by rw [hcast]; linarith
  have hlo' : (-1 : ℤ) < m₁ + m₂ - m := by exact_mod_cast hlo
  have hhi' : m₁ + m₂ - m < 2 := by exact_mod_cast hhi
  refine ⟨(m₁ + m₂ - m).toNat, by omega, by omega, ?_⟩
  have htn : (((m₁ + m₂ - m).toNat : ℕ) : ℚ) = ((m₁ + m₂ - m : ℤ) : ℚ) := by
    exact_mod_cast Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ m₁ + m₂ - m)
  rw [htn, hcast]
  ring

/-! ### Transport of a decomposition across gap sizes -/

/-- **Transport of a decomposition pair across gap sizes**: a decomposition of the
gapped target at gap size `ν ≥ n₀` has both components vanishing on the gap tail
past `i₀`, contracted digit sums within the levels, and its contraction re-expands
to a decomposition of the gapped target at any other gap size `ν' ≥ n₀`. -/
theorem decomp_gapDig_transport {dig u v : ℕ →₀ ℕ} {κ c₁ c₂ j ν ν' K n₀ i₀ : ℕ}
    (hκ : κ ≤ 1) (hK : K = (c₁ + c₂) / (p - 1)) (hn₀ : n₀ = c₁ + c₂ + 1)
    (hi₀ : i₀ = j - 1 + K) (hν : n₀ ≤ ν) (hν' : n₀ ≤ ν')
    (hdig : ∀ i, dig i < p) (hu : ∀ i, u i < p) (hv : ∀ i, v i < p)
    (hc₁ : (u.sum fun _ v => v) ≤ c₁) (hc₂ : (v.sum fun _ v => v) ≤ c₂)
    (hval : fracVal p u + fracVal p v = (κ : ℚ) + fracVal p (gapDig j ν dig)) :
    (∀ i, i₀ ≤ i → i < i₀ + (ν - K) → u i = 0 ∧ v i = 0) ∧
      ((dropGapDig i₀ (ν - K) u).sum fun _ v => v) ≤ c₁ ∧
      ((dropGapDig i₀ (ν - K) v).sum fun _ v => v) ≤ c₂ ∧
      fracVal p (gapDig (i₀ + 1) (ν' - K) (dropGapDig i₀ (ν - K) u))
          + fracVal p (gapDig (i₀ + 1) (ν' - K) (dropGapDig i₀ (ν - K) v))
        = (κ : ℚ) + fracVal p (gapDig j ν' dig) := by
  have hKle : K ≤ c₁ + c₂ := hK ▸ Nat.div_le_self _ _
  -- confinement at `ν`
  obtain ⟨hzero, -⟩ :=
    decomp_gapDig_confine p hκ hK hi₀ (by omega) hdig hu hv hc₁ hc₂ hval
  have hz : ∀ i, i₀ ≤ i → i < i₀ + (ν - K) → u i = 0 ∧ v i = 0 :=
    fun i h1 h2 => hzero i h1 (by omega)
  -- digit sums of the full contractions
  have hguv : gapDig (i₀ + 1) (ν - K) (dropGapDig i₀ (ν - K) u) = u :=
    gapDig_dropGapDig fun i h1 h2 => (hz i h1 h2).1
  have hgvv : gapDig (i₀ + 1) (ν - K) (dropGapDig i₀ (ν - K) v) = v :=
    gapDig_dropGapDig fun i h1 h2 => (hz i h1 h2).2
  have hsumu : ((dropGapDig i₀ (ν - K) u).sum fun _ v => v) ≤ c₁ := by
    have h := gapDig_sum (i₀ + 1) (ν - K) (dropGapDig i₀ (ν - K) u)
    rw [hguv] at h
    omega
  have hsumv : ((dropGapDig i₀ (ν - K) v).sum fun _ v => v) ≤ c₂ := by
    have h := gapDig_sum (i₀ + 1) (ν - K) (dropGapDig i₀ (ν - K) v)
    rw [hgvv] at h
    omega
  refine ⟨hz, hsumu, hsumv, ?_⟩
  -- contraction to `n₀`
  obtain ⟨hru, hrv, hsu, hsv, hval₀⟩ :=
    decomp_gapDig_contract p hκ hK hn₀ hi₀ rfl hν hdig hu hv hc₁ hc₂ hval
  have hu₀d : ∀ i, dropGapDig i₀ (ν - n₀) u i < p := fun i => dropGapDig_lt p hu i₀ _ i
  have hv₀d : ∀ i, dropGapDig i₀ (ν - n₀) v i < p := fun i => dropGapDig_lt p hv i₀ _ i
  have hu₀s : ((dropGapDig i₀ (ν - n₀) u).sum fun _ v => v) ≤ c₁ := by rw [hsu]; exact hc₁
  have hv₀s : ((dropGapDig i₀ (ν - n₀) v).sum fun _ v => v) ≤ c₂ := by rw [hsv]; exact hc₂
  -- the full contraction factors through the contraction at `n₀`
  have hfactu : dropGapDig i₀ (ν - K) u = dropGapDig i₀ (n₀ - K) (dropGapDig i₀ (ν - n₀) u) := by
    rw [dropGapDig_dropGapDig, show (ν - n₀) + (n₀ - K) = ν - K by omega]
  have hfactv : dropGapDig i₀ (ν - K) v = dropGapDig i₀ (n₀ - K) (dropGapDig i₀ (ν - n₀) v) := by
    rw [dropGapDig_dropGapDig, show (ν - n₀) + (n₀ - K) = ν - K by omega]
  -- confinement at `n₀` re-expands the `n₀`-contraction from the full contraction
  obtain ⟨hzero₀, -⟩ :=
    decomp_gapDig_confine p hκ hK hi₀ (by omega) hdig hu₀d hv₀d hu₀s hv₀s hval₀
  have hgu₀ : gapDig (i₀ + 1) (n₀ - K) (dropGapDig i₀ (n₀ - K) (dropGapDig i₀ (ν - n₀) u))
      = dropGapDig i₀ (ν - n₀) u :=
    gapDig_dropGapDig fun i h1 h2 => (hzero₀ i h1 (by omega)).1
  have hgv₀ : gapDig (i₀ + 1) (n₀ - K) (dropGapDig i₀ (n₀ - K) (dropGapDig i₀ (ν - n₀) v))
      = dropGapDig i₀ (ν - n₀) v :=
    gapDig_dropGapDig fun i h1 h2 => (hzero₀ i h1 (by omega)).2
  -- expansion to `ν'`
  have hval' := decomp_gapDig_expand p hκ hK hn₀ hi₀ rfl hν' hdig hu₀d hv₀d hu₀s hv₀s hval₀
  rw [hfactu, hfactv, show ν' - K = (n₀ - K) + (ν' - n₀) by omega, ← gapDig_gapDig,
    ← gapDig_gapDig, hgu₀, hgv₀]
  exact hval'

/-! ### The transported support point -/

/-- Transport of a support point across gap sizes: keep the integer slice index,
delete the `G` zero columns of the digit string at `i₀`, and re-insert a run of `G'`
zeros there. -/
noncomputable def transportPoint (a : ℕ+) (i₀ G G' : ℕ) (s : ℚ) : ℚ :=
  ((sliceInt a s : ℚ)
    - fracVal p (gapDig (i₀ + 1) G' (dropGapDig i₀ G (sliceDig p a s)))) / (a : ℚ)

/-- Specification of the transported point: its canonical decomposition keeps the
integer part and carries the re-gapped digit string, and transporting back restores
the original point. -/
theorem transportPoint_spec {a : ℕ+} {s : ℚ} {i₀ G G' : ℕ}
    (hval : (a : ℚ) * s = (sliceInt a s : ℚ) - fracVal p (sliceDig p a s))
    (hdig : ∀ i, sliceDig p a s i < p)
    (hzero : ∀ i, i₀ ≤ i → i < i₀ + G → sliceDig p a s i = 0) :
    sliceInt a (transportPoint p a i₀ G G' s) = sliceInt a s ∧
      sliceDig p a (transportPoint p a i₀ G G' s)
        = gapDig (i₀ + 1) G' (dropGapDig i₀ G (sliceDig p a s)) ∧
      transportPoint p a i₀ G' G (transportPoint p a i₀ G G' s) = s := by
  have ha : ((a : ℚ)) ≠ 0 := by exact_mod_cast a.pos.ne'
  have hT : (a : ℚ) * transportPoint p a i₀ G G' s
      = (sliceInt a s : ℚ)
        - fracVal p (gapDig (i₀ + 1) G' (dropGapDig i₀ G (sliceDig p a s))) := by
    rw [transportPoint]
    field_simp
  have hTd : ∀ i, gapDig (i₀ + 1) G' (dropGapDig i₀ G (sliceDig p a s)) i < p :=
    fun i => gapDig_lt p (fun i' => dropGapDig_lt p hdig i₀ G i') hp.out.pos _ _ i
  have hint : sliceInt a (transportPoint p a i₀ G G' s) = sliceInt a s :=
    sliceInt_eq p hp.out.one_lt hTd hT
  have hdig' : sliceDig p a (transportPoint p a i₀ G G' s)
      = gapDig (i₀ + 1) G' (dropGapDig i₀ G (sliceDig p a s)) := sliceDig_eq p hTd hT
  refine ⟨hint, hdig', ?_⟩
  rw [transportPoint, hint, hdig', dropGapDig_gapDig, gapDig_dropGapDig hzero]
  rw [div_eq_iff ha]
  linear_combination -hval

end TrustworthyKedlaya.UP
