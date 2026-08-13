/-
Copyright (c) 2026 Shanwen Wang, Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import TrustworthyKedlaya.Multiplicative

/-!
# Convolution combinations of UP series

The coefficient of `x * y` at an exponent `q` is a function of the finite multiset of
coefficient pairs `(x.coeff s₁, y.coeff s₂)` over the antidiagonal decompositions
`q = s₁ + s₂` — namely the sum of the pairwise products.  The transport machinery of
`TrustworthyKedlaya.Multiplicative` proves more than the periodicity of that sum: the
antidiagonal bijections between twist evaluation points preserve each coefficient
pair, so the **multiset itself** is twist-periodic.  Consequently *any* function `Φ`
of the pair multiset with `Φ ∅ = 0` produces a UP series from two UP series, with
periodicity data independent of `Φ` (`lem:up-mul-combine`).  The Teichmüller product
digits of `lem:shadow-mul-collapse` are the intended instances.

## Main statements

- `TrustworthyKedlaya.UP.mulPairs`: the coefficient-pair multiset of an antidiagonal.
- `TrustworthyKedlaya.UP.mulCombine`: the series `q ↦ Φ (mulPairs x y q)`.
- `TrustworthyKedlaya.UP.mulPairs_transport`: the multiset is preserved along the
  twist transport (core of `lem:up-mul-combine`).
- `TrustworthyKedlaya.UP.IsUP.mulCombine`: UP-ness of convolution combinations.

## References

- K. S. Kedlaya, *Power series and p-adic algebraic closures*, J. Number Theory 89
  (2001) [Ked01b], proof of Theorem 7.
-/

@[expose] public section

namespace TrustworthyKedlaya.UP

variable (p : ℕ) [hp : Fact (Nat.Prime p)]

/-! ### The coefficient-pair multiset of an antidiagonal -/

/-- The **coefficient-pair multiset** of two Hahn series along the antidiagonal of
`q`: the multiset of pairs `(x.coeff s₁, y.coeff s₂)` over the finitely many
decompositions `q = s₁ + s₂` with both coefficients nonzero
(`lem:up-mul-combine`). -/
noncomputable def mulPairs (x y : HahnSeries ℚ (𝔽ᵃ_[p])) (q : ℚ) :
    Multiset (𝔽ᵃ_[p] × 𝔽ᵃ_[p]) :=
  (Finset.antidiagonal x.isPWO_support y.isPWO_support q).val.map
    fun ij => (x.coeff ij.1, y.coeff ij.2)

variable {p}

/-- The product coefficient is the sum of the pairwise products of the column. -/
theorem coeff_mul_eq_sum_mulPairs (x y : HahnSeries ℚ (𝔽ᵃ_[p])) (q : ℚ) :
    (x * y).coeff q = ((mulPairs p x y q).map fun uv => uv.1 * uv.2).sum := by
  rw [HahnSeries.coeff_mul, mulPairs, Multiset.map_map]
  rfl

/-- Columns with no support decomposition are empty. -/
theorem mulPairs_eq_zero {x y : HahnSeries ℚ (𝔽ᵃ_[p])} {q : ℚ}
    (h : ∀ s₁ ∈ x.support, ∀ s₂ ∈ y.support, s₁ + s₂ ≠ q) :
    mulPairs p x y q = 0 := by
  have hempty : Finset.antidiagonal x.isPWO_support y.isPWO_support q = ∅ := by
    refine Finset.eq_empty_iff_forall_notMem.mpr fun ij hij => ?_
    obtain ⟨hm1, hm2, hs⟩ := Finset.mem_antidiagonal.mp hij
    exact h ij.1 hm1 ij.2 hm2 hs
  rw [mulPairs, hempty]
  rfl

/-- A nonempty column presents `q` as a sum of support points. -/
theorem exists_support_add_of_mulPairs_ne_zero {x y : HahnSeries ℚ (𝔽ᵃ_[p])} {q : ℚ}
    (h : mulPairs p x y q ≠ 0) :
    ∃ s₁ ∈ x.support, ∃ s₂ ∈ y.support, s₁ + s₂ = q := by
  rw [mulPairs, Ne, Multiset.map_eq_zero] at h
  obtain ⟨ij, hij⟩ := Multiset.exists_mem_of_ne_zero h
  obtain ⟨hm1, hm2, hs⟩ := Finset.mem_antidiagonal.mp hij
  exact ⟨ij.1, hm1, ij.2, hm2, hs⟩

variable (p) in
/-- The **convolution combination** of two Hahn series under a multiset function `Φ`
with `Φ 0 = 0`: the series with coefficient `Φ (mulPairs x y q)` at each exponent
(`lem:up-mul-combine`). -/
noncomputable def mulCombine (Φ : Multiset (𝔽ᵃ_[p] × 𝔽ᵃ_[p]) → 𝔽ᵃ_[p]) (hΦ : Φ 0 = 0)
    (x y : HahnSeries ℚ (𝔽ᵃ_[p])) : HahnSeries ℚ (𝔽ᵃ_[p]) where
  coeff q := Φ (mulPairs p x y q)
  isPWO_support' := by
    refine (x.isPWO_support'.add y.isPWO_support').mono fun q hq => ?_
    rw [Function.mem_support] at hq
    have hne : mulPairs p x y q ≠ 0 := fun h0 => hq (by rw [h0, hΦ])
    obtain ⟨s₁, h₁, s₂, h₂, hs⟩ := exists_support_add_of_mulPairs_ne_zero hne
    exact ⟨s₁, h₁, s₂, h₂, hs⟩

@[simp] theorem coeff_mulCombine (Φ : Multiset (𝔽ᵃ_[p] × 𝔽ᵃ_[p]) → 𝔽ᵃ_[p])
    (hΦ : Φ 0 = 0) (x y : HahnSeries ℚ (𝔽ᵃ_[p])) (q : ℚ) :
    (mulCombine p Φ hΦ x y).coeff q = Φ (mulPairs p x y q) := rfl

/-! ### Transport of the coefficient-pair multiset -/

/-- **Transport of the coefficient-pair multiset** (core of `lem:up-mul-combine`):
under the twist-sequence agreement hypotheses of `mul_antidiagonal_transport`, the
coefficient-pair multisets at the twist evaluation points of gap sizes `ν₁` and `ν₂`
coincide — the antidiagonal bijection matches the index sets, and the agreement of
the factor twist sequences matches the coefficient pairs. -/
theorem mulPairs_transport {x y : HahnSeries ℚ (𝔽ᵃ_[p])} {a : ℕ+}
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
    (m : ℤ) :
    mulPairs p x y (((m : ℚ) + -fracVal p (gapDig j ν₁ dig)) / (a : ℚ))
      = mulPairs p x y (((m : ℚ) + -fracVal p (gapDig j ν₂ dig)) / (a : ℚ)) := by
  classical
  set s₁ : Finset (ℚ × ℚ) :=
    Finset.antidiagonal x.isPWO_support y.isPWO_support
      (((m : ℚ) + -fracVal p (gapDig j ν₁ dig)) / (a : ℚ)) with hs₁
  set s₂ : Finset (ℚ × ℚ) :=
    Finset.antidiagonal x.isPWO_support y.isPWO_support
      (((m : ℚ) + -fracVal p (gapDig j ν₂ dig)) / (a : ℚ)) with hs₂
  -- the transported antidiagonal is the image of the original
  have himg : s₂ = s₁.image (fun ij : ℚ × ℚ =>
      (transportPoint p a i₀ (ν₁ - K) (ν₂ - K) ij.1,
       transportPoint p a i₀ (ν₁ - K) (ν₂ - K) ij.2)) := by
    apply Finset.ext
    intro ij
    constructor
    · intro hij
      obtain ⟨hm1, hm2, hs⟩ := Finset.mem_antidiagonal.mp hij
      obtain ⟨hcx, hcy, hsum2, hr1, hr2⟩ := mul_antidiagonal_transport p (j := j)
        (ν₁ := ν₂) (ν₂ := ν₁) hxs hys hK hn₀ hi₀ hν₂ hν₁ hdig
        (fun mi w hw hws => (hTx mi w hw hws).symm)
        (fun mi w hw hws => (hTy mi w hw hws).symm)
        hm1 hm2 hs
      refine Finset.mem_image.mpr
        ⟨(transportPoint p a i₀ (ν₂ - K) (ν₁ - K) ij.1,
          transportPoint p a i₀ (ν₂ - K) (ν₁ - K) ij.2), ?_, ?_⟩
      · refine Finset.mem_antidiagonal.mpr ⟨?_, ?_, hsum2⟩
        · rw [HahnSeries.mem_support, hcx]
          exact hm1
        · rw [HahnSeries.mem_support, hcy]
          exact hm2
      · exact Prod.ext_iff.mpr ⟨hr1, hr2⟩
    · intro hij
      obtain ⟨ij₀, hij₀, rfl⟩ := Finset.mem_image.mp hij
      obtain ⟨hm1, hm2, hs⟩ := Finset.mem_antidiagonal.mp hij₀
      obtain ⟨hcx, hcy, hsum2, -, -⟩ := mul_antidiagonal_transport p (j := j)
        (ν₁ := ν₁) (ν₂ := ν₂) hxs hys hK hn₀ hi₀ hν₁ hν₂ hdig hTx hTy hm1 hm2 hs
      refine Finset.mem_antidiagonal.mpr ⟨?_, ?_, hsum2⟩
      · rw [HahnSeries.mem_support, hcx]
        exact hm1
      · rw [HahnSeries.mem_support, hcy]
        exact hm2
  -- the transport is injective on the original antidiagonal (round trips)
  have hinj : Set.InjOn (fun ij : ℚ × ℚ =>
      (transportPoint p a i₀ (ν₁ - K) (ν₂ - K) ij.1,
       transportPoint p a i₀ (ν₁ - K) (ν₂ - K) ij.2)) s₁ := by
    intro ij hij ij' hij' heq
    obtain ⟨hm1, hm2, hs⟩ := Finset.mem_antidiagonal.mp (by exact_mod_cast hij)
    obtain ⟨hm1', hm2', hs'⟩ := Finset.mem_antidiagonal.mp (by exact_mod_cast hij')
    obtain ⟨-, -, -, hr1, hr2⟩ := mul_antidiagonal_transport p (j := j)
      (ν₁ := ν₁) (ν₂ := ν₂) hxs hys hK hn₀ hi₀ hν₁ hν₂ hdig hTx hTy hm1 hm2 hs
    obtain ⟨-, -, -, hr1', hr2'⟩ := mul_antidiagonal_transport p (j := j)
      (ν₁ := ν₁) (ν₂ := ν₂) hxs hys hK hn₀ hi₀ hν₁ hν₂ hdig hTx hTy hm1' hm2' hs'
    simp only [Prod.mk.injEq] at heq
    have h1 : ij.1 = ij'.1 := by
      have h := congrArg (transportPoint p a i₀ (ν₂ - K) (ν₁ - K)) heq.1
      rwa [hr1, hr1'] at h
    have h2 : ij.2 = ij'.2 := by
      have h := congrArg (transportPoint p a i₀ (ν₂ - K) (ν₁ - K)) heq.2
      rwa [hr2, hr2'] at h
    exact Prod.ext_iff.mpr ⟨h1, h2⟩
  -- assemble the multiset equality
  symm
  calc (mulPairs p x y (((m : ℚ) + -fracVal p (gapDig j ν₂ dig)) / (a : ℚ)))
      = s₂.val.map (fun ij => (x.coeff ij.1, y.coeff ij.2)) := rfl
    _ = (s₁.image (fun ij : ℚ × ℚ =>
          (transportPoint p a i₀ (ν₁ - K) (ν₂ - K) ij.1,
           transportPoint p a i₀ (ν₁ - K) (ν₂ - K) ij.2))).val.map
          (fun ij => (x.coeff ij.1, y.coeff ij.2)) := by rw [← himg]
    _ = (s₁.val.map (fun ij : ℚ × ℚ =>
          (transportPoint p a i₀ (ν₁ - K) (ν₂ - K) ij.1,
           transportPoint p a i₀ (ν₁ - K) (ν₂ - K) ij.2))).map
          (fun ij => (x.coeff ij.1, y.coeff ij.2)) := by
        rw [Finset.image_val_of_injOn hinj]
    _ = s₁.val.map (fun ij : ℚ × ℚ =>
          (x.coeff (transportPoint p a i₀ (ν₁ - K) (ν₂ - K) ij.1),
           y.coeff (transportPoint p a i₀ (ν₁ - K) (ν₂ - K) ij.2))) := by
        rw [Multiset.map_map]
        rfl
    _ = s₁.val.map (fun ij => (x.coeff ij.1, y.coeff ij.2)) := by
        refine Multiset.map_congr rfl fun ij hij => ?_
        obtain ⟨hm1, hm2, hs⟩ := Finset.mem_antidiagonal.mp (Finset.mem_def.mpr hij)
        obtain ⟨hcx, hcy, -, -, -⟩ := mul_antidiagonal_transport p (j := j)
          (ν₁ := ν₁) (ν₂ := ν₂) hxs hys hK hn₀ hi₀ hν₁ hν₂ hdig hTx hTy hm1 hm2 hs
        rw [hcx, hcy]
    _ = mulPairs p x y (((m : ℚ) + -fracVal p (gapDig j ν₁ dig)) / (a : ℚ)) := rfl

/-! ### Periodicity of the slices of a convolution combination -/

/-- **Periodicity of the slices of a convolution combination**
(`lem:up-mul-combine`): at a common slice width `a`, every slice of
`mulCombine Φ hΦ x y` is periodic at level `c₁ + c₂` with the same data
`(max(M₁,M₂) + (K + n₀), lcm(N₁,N₂))` as the product — independently of `Φ`. -/
theorem isTwistPeriodic_mulCombine_slice
    (Φ : Multiset (𝔽ᵃ_[p] × 𝔽ᵃ_[p]) → 𝔽ᵃ_[p]) (hΦ : Φ 0 = 0)
    {x y : HahnSeries ℚ (𝔽ᵃ_[p])} {a : ℕ+}
    {b₁ b₂ c₁ c₂ : ℕ} {M₁ M₂ N₁ N₂ : ℕ+}
    (hxs : x.support ⊆ Sabc p a b₁ c₁)
    (hxp : ∀ mi : ℤ, -(b₁ : ℤ) ≤ mi →
      IsTwistPeriodic p (fun z => x.coeff (((mi : ℚ) + z) / (a : ℚ))) c₁ M₁ N₁)
    (hys : y.support ⊆ Sabc p a b₂ c₂)
    (hyp : ∀ mi : ℤ, -(b₂ : ℤ) ≤ mi →
      IsTwistPeriodic p (fun z => y.coeff (((mi : ℚ) + z) / (a : ℚ))) c₂ M₂ N₂)
    (m : ℤ) :
    IsTwistPeriodic p
      (fun z => (mulCombine p Φ hΦ x y).coeff (((m : ℚ) + z) / (a : ℚ))) (c₁ + c₂)
      (max M₁ M₂ + ⟨(c₁ + c₂) / (p - 1) + (c₁ + c₂ + 1),
        Nat.lt_of_lt_of_le (Nat.succ_pos _) (Nat.le_add_left _ _)⟩)
      (N₁.lcm N₂) := by
  intro j dig _hj hdigits _hdigsum n hn
  classical
  set K := (c₁ + c₂) / (p - 1) with hK
  set n₀ := c₁ + c₂ + 1 with hn₀
  set i₀ := j - 1 + K with hi₀
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
  -- both sides as `Φ`-values of the coefficient-pair multisets
  have htw : ∀ G : ℕ,
      twistSeq p (fun z => (mulCombine p Φ hΦ x y).coeff (((m : ℚ) + z) / (a : ℚ)))
          j dig G
        = Φ (mulPairs p x y (((m : ℚ) + -fracVal p (gapDig j G dig)) / (a : ℚ))) :=
    fun G => twistSeq_eq_neg_fracVal_gapDig p _ _ _ _
  rw [htw, htw]
  exact congrArg Φ (mulPairs_transport hxs hys hK hn₀ hi₀ hn₀n' hn₀n hdigits hTx hTy m)

/-! ### The closure theorems -/

/-- **Convolution combinations at a common slice width**: the support carry estimate
gives `S_{a, b₁+b₂+1, c₁+c₂}`, and the slices inherit the product periodicity data
`(max(M₁,M₂) + (K + n₀), lcm(N₁,N₂))`, independently of `Φ`. -/
theorem isUP_mulCombine_of_common_width
    (Φ : Multiset (𝔽ᵃ_[p] × 𝔽ᵃ_[p]) → 𝔽ᵃ_[p]) (hΦ : Φ 0 = 0)
    {x y : HahnSeries ℚ (𝔽ᵃ_[p])} {a : ℕ+}
    {b₁ b₂ c₁ c₂ : ℕ} {M₁ M₂ N₁ N₂ : ℕ+}
    (hxs : x.support ⊆ Sabc p a b₁ c₁)
    (hxp : ∀ mi : ℤ, -(b₁ : ℤ) ≤ mi →
      IsTwistPeriodic p (fun z => x.coeff (((mi : ℚ) + z) / (a : ℚ))) c₁ M₁ N₁)
    (hys : y.support ⊆ Sabc p a b₂ c₂)
    (hyp : ∀ mi : ℤ, -(b₂ : ℤ) ≤ mi →
      IsTwistPeriodic p (fun z => y.coeff (((mi : ℚ) + z) / (a : ℚ))) c₂ M₂ N₂) :
    IsUP p (mulCombine p Φ hΦ x y) := by
  refine ⟨a, b₁ + b₂ + 1, c₁ + c₂, ?_, _, N₁.lcm N₂,
    fun m _ => isTwistPeriodic_mulCombine_slice Φ hΦ hxs hxp hys hyp m⟩
  intro g hg
  rw [HahnSeries.mem_support, coeff_mulCombine] at hg
  have hne : mulPairs p x y g ≠ 0 := fun h0 => hg (by rw [h0, hΦ])
  obtain ⟨s₁, h₁, s₂, h₂, rfl⟩ := exists_support_add_of_mulPairs_ne_zero hne
  exact Sabc_add_subset p (hxs h₁) (hys h₂)

/-- **UP is stable under convolution combinations** (`lem:up-mul-combine`): for any
function `Φ` of the coefficient-pair multiset with `Φ 0 = 0` and UP series `x`, `y`,
the series with coefficients `Φ (mulPairs x y q)` is UP.  Taking `Φ` to be the sum
of the pairwise products recovers `IsUP.mul`. -/
theorem IsUP.mulCombine {x y : HahnSeries ℚ (𝔽ᵃ_[p])} (hx : IsUP p x) (hy : IsUP p y)
    (Φ : Multiset (𝔽ᵃ_[p] × 𝔽ᵃ_[p]) → 𝔽ᵃ_[p]) (hΦ : Φ 0 = 0) :
    IsUP p (mulCombine p Φ hΦ x y) := by
  obtain ⟨a, b, c, hxs, M, N, hxp⟩ := hx
  obtain ⟨a', b', c', hys, M', N', hyp⟩ := hy
  obtain ⟨b₁, c₁, M₁, hs₁, hp₁⟩ := SliceWitness.width_mul a' ⟨hxs, hxp⟩
  obtain ⟨b₂, c₂, M₂, hs₂, hp₂⟩ := SliceWitness.width_mul a ⟨hys, hyp⟩
  rw [mul_comm a a'] at hs₂ hp₂
  exact isUP_mulCombine_of_common_width Φ hΦ hs₁ hp₁ hs₂ hp₂

end TrustworthyKedlaya.UP
