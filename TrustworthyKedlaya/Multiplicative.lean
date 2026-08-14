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

/-! ### Transport of an antidiagonal term -/

/-- **Transport of an antidiagonal term**: a pair of support points decomposing the
twist evaluation point of the slice `m` at gap size `ν₁ ≥ n₀` transports to gap size
`ν₂ ≥ n₀`, keeping the coefficients of both factors (they are twist-sequence values
of slices at the gap-tail index, equal under the periodicity input), decomposing the
twist point at `ν₂`, and transporting back to the original pair. -/
theorem mul_antidiagonal_transport {x y : HahnSeries ℚ (𝔽ᵃ_[p])} {a : ℕ+}
    {b₁ b₂ c₁ c₂ : ℕ}
    (hxs : x.support ⊆ Sabc p a b₁ c₁) (hys : y.support ⊆ Sabc p a b₂ c₂)
    {j ν₁ ν₂ K n₀ i₀ : ℕ}
    (hK : K = (c₁ + c₂) / (p - 1)) (hn₀ : n₀ = c₁ + c₂ + 1) (hi₀ : i₀ = j - 1 + K)
    (hν₁ : n₀ ≤ ν₁) (hν₂ : n₀ ≤ ν₂)
    {dig : ℕ →₀ ℕ} (hdig : ∀ i, dig i < p)
    (hTx : ∀ (mi : ℤ) (w : ℕ →₀ ℕ), (∀ i, w i < p) → (w.sum fun _ v => v) ≤ c₁ →
      twistSeq p (fun z => x.coeff (((mi : ℚ) + z) / (a : ℚ))) (i₀ + 1) w (ν₁ - K)
        = twistSeq p (fun z => x.coeff (((mi : ℚ) + z) / (a : ℚ))) (i₀ + 1) w (ν₂ - K))
    (hTy : ∀ (mi : ℤ) (w : ℕ →₀ ℕ), (∀ i, w i < p) → (w.sum fun _ v => v) ≤ c₂ →
      twistSeq p (fun z => y.coeff (((mi : ℚ) + z) / (a : ℚ))) (i₀ + 1) w (ν₁ - K)
        = twistSeq p (fun z => y.coeff (((mi : ℚ) + z) / (a : ℚ))) (i₀ + 1) w (ν₂ - K))
    {m : ℤ} {s₁ s₂ : ℚ} (hs₁ : s₁ ∈ x.support) (hs₂ : s₂ ∈ y.support)
    (hsum12 : s₁ + s₂ = ((m : ℚ) + -fracVal p (gapDig j ν₁ dig)) / (a : ℚ)) :
    x.coeff (transportPoint p a i₀ (ν₁ - K) (ν₂ - K) s₁) = x.coeff s₁ ∧
      y.coeff (transportPoint p a i₀ (ν₁ - K) (ν₂ - K) s₂) = y.coeff s₂ ∧
      transportPoint p a i₀ (ν₁ - K) (ν₂ - K) s₁
          + transportPoint p a i₀ (ν₁ - K) (ν₂ - K) s₂
        = ((m : ℚ) + -fracVal p (gapDig j ν₂ dig)) / (a : ℚ) ∧
      transportPoint p a i₀ (ν₂ - K) (ν₁ - K)
          (transportPoint p a i₀ (ν₁ - K) (ν₂ - K) s₁) = s₁ ∧
      transportPoint p a i₀ (ν₂ - K) (ν₁ - K)
          (transportPoint p a i₀ (ν₁ - K) (ν₂ - K) s₂) = s₂ := by
  have ha : ((a : ℚ)) ≠ 0 := by exact_mod_cast a.pos.ne'
  have hp0 := hp.out.pos
  obtain ⟨hud, hus, -, huval⟩ := Sabc_sliceDig p (hxs hs₁)
  obtain ⟨hvd, hvs, -, hvval⟩ := Sabc_sliceDig p (hys hs₂)
  -- the sum equation in canonical form, and the carry split
  have hgd : ∀ i, gapDig j ν₁ dig i < p := fun i => gapDig_lt p hdig hp0 j ν₁ i
  have hsum' : ((sliceInt a s₁ : ℚ) - fracVal p (sliceDig p a s₁))
      + ((sliceInt a s₂ : ℚ) - fracVal p (sliceDig p a s₂))
      = (m : ℚ) - fracVal p (gapDig j ν₁ dig) := by
    rw [← huval, ← hvval]
    have h12 : (a : ℚ) * (s₁ + s₂) = (m : ℚ) + -fracVal p (gapDig j ν₁ dig) := by
      rw [hsum12]
      field_simp
    linear_combination h12
  obtain ⟨κ, hκ, hmm12, hvalpair⟩ := decomp_point_split p hud hvd hgd hsum'
  -- pair transport across the gap sizes
  obtain ⟨hzero, hsumu, hsumv, hval'⟩ :=
    decomp_gapDig_transport p hκ hK hn₀ hi₀ hν₁ hν₂ hdig hud hvd hus hvs hvalpair
  have hzu : ∀ i, i₀ ≤ i → i < i₀ + (ν₁ - K) → sliceDig p a s₁ i = 0 :=
    fun i h1 h2 => (hzero i h1 h2).1
  have hzv : ∀ i, i₀ ≤ i → i < i₀ + (ν₁ - K) → sliceDig p a s₂ i = 0 :=
    fun i h1 h2 => (hzero i h1 h2).2
  obtain ⟨hint₁, hdig₁, hrt₁⟩ := transportPoint_spec p huval hud hzu
  obtain ⟨hint₂, hdig₂, hrt₂⟩ := transportPoint_spec p hvval hvd hzv
  have hgu : gapDig (i₀ + 1) (ν₁ - K) (dropGapDig i₀ (ν₁ - K) (sliceDig p a s₁))
      = sliceDig p a s₁ := gapDig_dropGapDig hzu
  have hgv : gapDig (i₀ + 1) (ν₁ - K) (dropGapDig i₀ (ν₁ - K) (sliceDig p a s₂))
      = sliceDig p a s₂ := gapDig_dropGapDig hzv
  have huD : ∀ i, dropGapDig i₀ (ν₁ - K) (sliceDig p a s₁) i < p :=
    fun i => dropGapDig_lt p hud i₀ _ i
  have hvD : ∀ i, dropGapDig i₀ (ν₁ - K) (sliceDig p a s₂) i < p :=
    fun i => dropGapDig_lt p hvd i₀ _ i
  -- coefficients as twist-sequence values of the slices
  have htwx : ∀ G : ℕ,
      twistSeq p (fun z => x.coeff (((sliceInt a s₁ : ℚ) + z) / (a : ℚ))) (i₀ + 1)
        (dropGapDig i₀ (ν₁ - K) (sliceDig p a s₁)) G
      = x.coeff (((sliceInt a s₁ : ℚ)
          + -fracVal p (gapDig (i₀ + 1) G (dropGapDig i₀ (ν₁ - K) (sliceDig p a s₁))))
          / (a : ℚ)) :=
    fun G => twistSeq_eq_neg_fracVal_gapDig p _ _ _ _
  have htwy : ∀ G : ℕ,
      twistSeq p (fun z => y.coeff (((sliceInt a s₂ : ℚ) + z) / (a : ℚ))) (i₀ + 1)
        (dropGapDig i₀ (ν₁ - K) (sliceDig p a s₂)) G
      = y.coeff (((sliceInt a s₂ : ℚ)
          + -fracVal p (gapDig (i₀ + 1) G (dropGapDig i₀ (ν₁ - K) (sliceDig p a s₂))))
          / (a : ℚ)) :=
    fun G => twistSeq_eq_neg_fracVal_gapDig p _ _ _ _
  have hargu : ((sliceInt a s₁ : ℚ) + -fracVal p (sliceDig p a s₁)) / (a : ℚ) = s₁ := by
    rw [div_eq_iff ha]
    linear_combination -huval
  have hargv : ((sliceInt a s₂ : ℚ) + -fracVal p (sliceDig p a s₂)) / (a : ℚ) = s₂ := by
    rw [div_eq_iff ha]
    linear_combination -hvval
  have h1 : x.coeff (((sliceInt a s₁ : ℚ)
      + -fracVal p (gapDig (i₀ + 1) (ν₁ - K) (dropGapDig i₀ (ν₁ - K) (sliceDig p a s₁))))
      / (a : ℚ)) = x.coeff s₁ := by
    rw [hgu]
    exact congrArg x.coeff hargu
  have h2 : y.coeff (((sliceInt a s₂ : ℚ)
      + -fracVal p (gapDig (i₀ + 1) (ν₁ - K) (dropGapDig i₀ (ν₁ - K) (sliceDig p a s₂))))
      / (a : ℚ)) = y.coeff s₂ := by
    rw [hgv]
    exact congrArg y.coeff hargv
  have hargTx : transportPoint p a i₀ (ν₁ - K) (ν₂ - K) s₁
      = ((sliceInt a s₁ : ℚ)
        + -fracVal p (gapDig (i₀ + 1) (ν₂ - K) (dropGapDig i₀ (ν₁ - K) (sliceDig p a s₁))))
        / (a : ℚ) := by
    rw [transportPoint]
    ring
  have hargTy : transportPoint p a i₀ (ν₁ - K) (ν₂ - K) s₂
      = ((sliceInt a s₂ : ℚ)
        + -fracVal p (gapDig (i₀ + 1) (ν₂ - K) (dropGapDig i₀ (ν₁ - K) (sliceDig p a s₂))))
        / (a : ℚ) := by
    rw [transportPoint]
    ring
  have h1T := congrArg x.coeff hargTx
  have h2T := congrArg y.coeff hargTy
  have hcx : x.coeff (transportPoint p a i₀ (ν₁ - K) (ν₂ - K) s₁) = x.coeff s₁ :=
    h1T.trans (((htwx (ν₂ - K)).symm.trans
      ((hTx (sliceInt a s₁) _ huD hsumu).symm.trans (htwx (ν₁ - K)))).trans h1)
  have hcy : y.coeff (transportPoint p a i₀ (ν₁ - K) (ν₂ - K) s₂) = y.coeff s₂ :=
    h2T.trans (((htwy (ν₂ - K)).symm.trans
      ((hTy (sliceInt a s₂) _ hvD hsumv).symm.trans (htwy (ν₁ - K)))).trans h2)
  -- the transported pair decomposes the twist point at `ν₂`
  have hmmq : ((sliceInt a s₁ : ℚ)) + ((sliceInt a s₂ : ℚ)) = (m : ℚ) + (κ : ℚ) := by
    exact_mod_cast hmm12
  have hsum2arg : ((sliceInt a s₁ : ℚ)
        - fracVal p (gapDig (i₀ + 1) (ν₂ - K) (dropGapDig i₀ (ν₁ - K) (sliceDig p a s₁))))
      + ((sliceInt a s₂ : ℚ)
        - fracVal p (gapDig (i₀ + 1) (ν₂ - K) (dropGapDig i₀ (ν₁ - K) (sliceDig p a s₂))))
      = (m : ℚ) + -fracVal p (gapDig j ν₂ dig) := by
    linarith [hval', hmmq]
  have hsum2 : transportPoint p a i₀ (ν₁ - K) (ν₂ - K) s₁
      + transportPoint p a i₀ (ν₁ - K) (ν₂ - K) s₂
      = ((m : ℚ) + -fracVal p (gapDig j ν₂ dig)) / (a : ℚ) := by
    rw [transportPoint, transportPoint, ← add_div, hsum2arg]
  exact ⟨hcx, hcy, hsum2, hrt₁, hrt₂⟩

/-! ### Periodicity of the slices of a product -/

variable {p} in
/-- **Periodicity of the slices of a product** (the core of `IsUP.mul`): at a common
slice width `a`, every slice of `x * y` is periodic at level `c₁ + c₂` with data
`(max(M₁,M₂) + (K + n₀), lcm(N₁,N₂))`, where `K = ⌊(c₁+c₂)/(p-1)⌋` and
`n₀ = c₁+c₂+1`. -/
theorem isTwistPeriodic_mul_slice {x y : HahnSeries ℚ (𝔽ᵃ_[p])} {a : ℕ+}
    {b₁ b₂ c₁ c₂ : ℕ} {M₁ M₂ N₁ N₂ : ℕ+}
    (hxs : x.support ⊆ Sabc p a b₁ c₁)
    (hxp : ∀ mi : ℤ, -(b₁ : ℤ) ≤ mi →
      IsTwistPeriodic p (fun z => x.coeff (((mi : ℚ) + z) / (a : ℚ))) c₁ M₁ N₁)
    (hys : y.support ⊆ Sabc p a b₂ c₂)
    (hyp : ∀ mi : ℤ, -(b₂ : ℤ) ≤ mi →
      IsTwistPeriodic p (fun z => y.coeff (((mi : ℚ) + z) / (a : ℚ))) c₂ M₂ N₂)
    (m : ℤ) :
    IsTwistPeriodic p (fun z => (x * y).coeff (((m : ℚ) + z) / (a : ℚ))) (c₁ + c₂)
      (max M₁ M₂ + ⟨(c₁ + c₂) / (p - 1) + (c₁ + c₂ + 1),
        Nat.lt_of_lt_of_le (Nat.succ_pos _) (Nat.le_add_left _ _)⟩)
      (N₁.lcm N₂) := by
  intro j dig _hj hdigits _hdigsum n hn
  classical
  set K := (c₁ + c₂) / (p - 1) with hK
  set n₀ := c₁ + c₂ + 1 with hn₀
  set i₀ := j - 1 + K with hi₀
  have hKle : K ≤ c₁ + c₂ := Nat.div_le_self _ _
  -- index bounds
  have hnb : ((max M₁ M₂ : ℕ+) : ℕ) + (K + n₀) ≤ n := by exact_mod_cast hn
  have hM1 : (M₁ : ℕ) + (K + n₀) ≤ n :=
    le_trans (Nat.add_le_add_right ((PNat.coe_le_coe _ _).mpr (le_max_left M₁ M₂)) _) hnb
  have hM2 : (M₂ : ℕ) + (K + n₀) ≤ n :=
    le_trans (Nat.add_le_add_right ((PNat.coe_le_coe _ _).mpr (le_max_right M₁ M₂)) _) hnb
  have hM1K : (M₁ : ℕ) ≤ n - K :=
    Nat.le_sub_of_add_le (le_trans (Nat.add_le_add_left (Nat.le_add_right K n₀) _) hM1)
  have hM2K : (M₂ : ℕ) ≤ n - K :=
    Nat.le_sub_of_add_le (le_trans (Nat.add_le_add_left (Nat.le_add_right K n₀) _) hM2)
  have hKn : K ≤ n :=
    le_trans (le_trans (Nat.le_add_right K n₀) (Nat.le_add_left _ _)) hM1
  have hn₀n : n₀ ≤ n :=
    le_trans (le_trans (Nat.le_add_left n₀ K) (Nat.le_add_left _ _)) hM1
  have hn₀n' : n₀ ≤ n + ((N₁.lcm N₂ : ℕ+) : ℕ) := le_trans hn₀n (Nat.le_add_right _ _)
  -- slice periodicity for all slices, with the common period
  have hxp' : ∀ mi : ℤ,
      IsTwistPeriodic p (fun z => x.coeff (((mi : ℚ) + z) / (a : ℚ))) c₁ M₁ (N₁.lcm N₂) :=
    fun mi => (isTwistPeriodic_slice_upgrade p hxs hxp c₁ mi).mono le_rfl le_rfl
      (PNat.dvd_iff.mp (PNat.dvd_lcm_left N₁ N₂))
  have hyp' : ∀ mi : ℤ,
      IsTwistPeriodic p (fun z => y.coeff (((mi : ℚ) + z) / (a : ℚ))) c₂ M₂ (N₁.lcm N₂) :=
    fun mi => (isTwistPeriodic_slice_upgrade p hys hyp c₂ mi).mono le_rfl le_rfl
      (PNat.dvd_iff.mp (PNat.dvd_lcm_right N₁ N₂))
  -- the twist-sequence equality between the two gap-tail indices
  have hTx : ∀ (mi : ℤ) (w : ℕ →₀ ℕ), (∀ i, w i < p) → (w.sum fun _ v => v) ≤ c₁ →
      twistSeq p (fun z => x.coeff (((mi : ℚ) + z) / (a : ℚ))) (i₀ + 1) w
          ((n + (N₁.lcm N₂ : ℕ)) - K)
        = twistSeq p (fun z => x.coeff (((mi : ℚ) + z) / (a : ℚ))) (i₀ + 1) w (n - K) := by
    intro mi w hw hwsum
    have h := hxp' mi (i₀ + 1) w (Nat.succ_pos _) hw hwsum (n - K) hM1K
    rwa [← Nat.sub_add_comm hKn] at h
  have hTy : ∀ (mi : ℤ) (w : ℕ →₀ ℕ), (∀ i, w i < p) → (w.sum fun _ v => v) ≤ c₂ →
      twistSeq p (fun z => y.coeff (((mi : ℚ) + z) / (a : ℚ))) (i₀ + 1) w
          ((n + (N₁.lcm N₂ : ℕ)) - K)
        = twistSeq p (fun z => y.coeff (((mi : ℚ) + z) / (a : ℚ))) (i₀ + 1) w (n - K) := by
    intro mi w hw hwsum
    have h := hyp' mi (i₀ + 1) w (Nat.succ_pos _) hw hwsum (n - K) hM2K
    rwa [← Nat.sub_add_comm hKn] at h
  -- both sides as antidiagonal sums
  have htwxy : ∀ G : ℕ,
      twistSeq p (fun z => (x * y).coeff (((m : ℚ) + z) / (a : ℚ))) j dig G
        = (x * y).coeff (((m : ℚ) + -fracVal p (gapDig j G dig)) / (a : ℚ)) :=
    fun G => twistSeq_eq_neg_fracVal_gapDig p _ _ _ _
  rw [htwxy, htwxy, HahnSeries.coeff_mul, HahnSeries.coeff_mul,
    ← Finset.sum_filter_ne_zero (Finset.antidiagonal x.isPWO_support y.isPWO_support _),
    ← Finset.sum_filter_ne_zero (Finset.antidiagonal x.isPWO_support y.isPWO_support _)]
  -- reindex along the transport
  refine Finset.sum_nbij'
    (fun ij => (transportPoint p a i₀ ((n + (N₁.lcm N₂ : ℕ)) - K) (n - K) ij.1,
                transportPoint p a i₀ ((n + (N₁.lcm N₂ : ℕ)) - K) (n - K) ij.2))
    (fun ij => (transportPoint p a i₀ (n - K) ((n + (N₁.lcm N₂ : ℕ)) - K) ij.1,
                transportPoint p a i₀ (n - K) ((n + (N₁.lcm N₂ : ℕ)) - K) ij.2))
    ?_ ?_ ?_ ?_ ?_
  · -- forward membership
    intro ij hij
    obtain ⟨hanti, hne⟩ := Finset.mem_filter.mp hij
    obtain ⟨hm1, hm2, hs12⟩ := Finset.mem_antidiagonal.mp hanti
    obtain ⟨hcx, hcy, hsum2, -, -⟩ := mul_antidiagonal_transport p (j := j)
      (ν₁ := n + (N₁.lcm N₂ : ℕ)) (ν₂ := n) hxs hys hK hn₀ hi₀
      hn₀n' hn₀n hdigits hTx hTy hm1 hm2 hs12
    rw [Finset.mem_filter, Finset.mem_antidiagonal]
    refine ⟨⟨?_, ?_, hsum2⟩, ?_⟩
    · rw [HahnSeries.mem_support, hcx]
      exact left_ne_zero_of_mul hne
    · rw [HahnSeries.mem_support, hcy]
      exact right_ne_zero_of_mul hne
    · rw [hcx, hcy]
      exact hne
  · -- backward membership
    intro ij hij
    obtain ⟨hanti, hne⟩ := Finset.mem_filter.mp hij
    obtain ⟨hm1, hm2, hs12⟩ := Finset.mem_antidiagonal.mp hanti
    obtain ⟨hcx, hcy, hsum2, -, -⟩ := mul_antidiagonal_transport p (j := j)
      (ν₁ := n) (ν₂ := n + (N₁.lcm N₂ : ℕ)) hxs hys hK hn₀ hi₀
      hn₀n hn₀n' hdigits
      (fun mi w hw hs => (hTx mi w hw hs).symm) (fun mi w hw hs => (hTy mi w hw hs).symm)
      hm1 hm2 hs12
    rw [Finset.mem_filter, Finset.mem_antidiagonal]
    refine ⟨⟨?_, ?_, hsum2⟩, ?_⟩
    · rw [HahnSeries.mem_support, hcx]
      exact left_ne_zero_of_mul hne
    · rw [HahnSeries.mem_support, hcy]
      exact right_ne_zero_of_mul hne
    · rw [hcx, hcy]
      exact hne
  · -- left inverse
    intro ij hij
    obtain ⟨hanti, -⟩ := Finset.mem_filter.mp hij
    obtain ⟨hm1, hm2, hs12⟩ := Finset.mem_antidiagonal.mp hanti
    obtain ⟨-, -, -, hr1, hr2⟩ := mul_antidiagonal_transport p (j := j)
      (ν₁ := n + (N₁.lcm N₂ : ℕ)) (ν₂ := n) hxs hys hK hn₀ hi₀
      hn₀n' hn₀n hdigits hTx hTy hm1 hm2 hs12
    exact Prod.ext_iff.mpr ⟨hr1, hr2⟩
  · -- right inverse
    intro ij hij
    obtain ⟨hanti, -⟩ := Finset.mem_filter.mp hij
    obtain ⟨hm1, hm2, hs12⟩ := Finset.mem_antidiagonal.mp hanti
    obtain ⟨-, -, -, hr1, hr2⟩ := mul_antidiagonal_transport p (j := j)
      (ν₁ := n) (ν₂ := n + (N₁.lcm N₂ : ℕ)) hxs hys hK hn₀ hi₀
      hn₀n hn₀n' hdigits
      (fun mi w hw hs => (hTx mi w hw hs).symm) (fun mi w hw hs => (hTy mi w hw hs).symm)
      hm1 hm2 hs12
    exact Prod.ext_iff.mpr ⟨hr1, hr2⟩
  · -- matched terms are equal
    intro ij hij
    obtain ⟨hanti, -⟩ := Finset.mem_filter.mp hij
    obtain ⟨hm1, hm2, hs12⟩ := Finset.mem_antidiagonal.mp hanti
    obtain ⟨hcx, hcy, -, -, -⟩ := mul_antidiagonal_transport p (j := j)
      (ν₁ := n + (N₁.lcm N₂ : ℕ)) (ν₂ := n) hxs hys hK hn₀ hi₀
      hn₀n' hn₀n hdigits hTx hTy hm1 hm2 hs12
    rw [hcx, hcy]

/-! ### The closure theorems -/

variable {p} in
/-- **UP is stable under multiplication at a common slice width**: the support carry
estimate gives `S_{a, b₁+b₂+1, c₁+c₂}`, and the slices inherit the periodicity data
`(max(M₁,M₂) + (K + n₀), lcm(N₁,N₂))`. -/
theorem isUP_mul_of_common_width {x y : HahnSeries ℚ (𝔽ᵃ_[p])} {a : ℕ+}
    {b₁ b₂ c₁ c₂ : ℕ} {M₁ M₂ N₁ N₂ : ℕ+}
    (hxs : x.support ⊆ Sabc p a b₁ c₁)
    (hxp : ∀ mi : ℤ, -(b₁ : ℤ) ≤ mi →
      IsTwistPeriodic p (fun z => x.coeff (((mi : ℚ) + z) / (a : ℚ))) c₁ M₁ N₁)
    (hys : y.support ⊆ Sabc p a b₂ c₂)
    (hyp : ∀ mi : ℤ, -(b₂ : ℤ) ≤ mi →
      IsTwistPeriodic p (fun z => y.coeff (((mi : ℚ) + z) / (a : ℚ))) c₂ M₂ N₂) :
    IsUP p (x * y) := by
  refine ⟨a, b₁ + b₂ + 1, c₁ + c₂, ?_, _, N₁.lcm N₂,
    fun m _ => isTwistPeriodic_mul_slice hxs hxp hys hyp m⟩
  intro g hg
  obtain ⟨g₁, hg₁, g₂, hg₂, rfl⟩ := HahnSeries.support_mul_subset hg
  exact Sabc_add_subset p (hxs hg₁) (hys hg₂)

variable {p} in
/-- **UP is stable under multiplication**: upgrade both presentations
to the common slice width `a'·a` and transport the antidiagonal decompositions. -/
theorem IsUP.mul {x y : HahnSeries ℚ (𝔽ᵃ_[p])} (hx : IsUP p x) (hy : IsUP p y) :
    IsUP p (x * y) := by
  obtain ⟨a, b, c, hxs, M, N, hxp⟩ := hx
  obtain ⟨a', b', c', hys, M', N', hyp⟩ := hy
  obtain ⟨b₁, c₁, M₁, hs₁, hp₁⟩ := SliceWitness.width_mul a' ⟨hxs, hxp⟩
  obtain ⟨b₂, c₂, M₂, hs₂, hp₂⟩ := SliceWitness.width_mul a ⟨hys, hyp⟩
  rw [mul_comm a a'] at hs₂ hp₂
  exact isUP_mul_of_common_width hs₁ hp₁ hs₂ hp₂

end TrustworthyKedlaya.UP
