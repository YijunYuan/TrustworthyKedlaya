/-
Copyright (c) 2026 Shanwen Wang, Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import TrustworthyKedlaya.Lp.NewtonSlope
public import Mathlib.SetTheory.Ordinal.Family
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# `𝕃_p` is algebraically closed

The transfinite Newton recursion (Wang-Yuan, Theorem 2.8; Kedlaya 2001b, Proposition 2):
every polynomial over `𝕃_[p]` of positive degree has a root, so `𝕃_[p]` is algebraically
closed.

The argument is by contradiction.  Assume `f` has no root at all.  Then at every
approximation `r` the shifted polynomial `f(T + r)` has a nonzero constant term, so it has
a last Newton slope `stepSlope f r`, its residue polynomial has a nonzero root
`stepDigit f r` in `𝔽ᵃ_[p]` (algebraically closed), and the Newton step
(`TrustworthyKedlaya.pAdicHahnSeries.lastSlope_lt_lastSlope_taylor`,
`val_lt_val_taylor_coeff_zero`) improves the approximation by the one-term series
`stepTerm f r = [stepDigit] p^stepSlope`.

We iterate the step transfinitely: `newtonApprox f α` is defined by well-founded recursion
on the ordinal `α` as the Hahn series whose canonical coefficient function collects the
digits of *all* previous stages (`histDigits`), each digit `stepDigit` sitting at position
`stepSlope`.  This uniform definition handles zero, successor and limit stages at once;
it is well-formed because the step slopes increase strictly along the recursion
(`SlopeMono`, established inductively), which keeps the digit positions strictly
increasing and the support well-ordered.  At a successor stage the sum of digits differs
from the previous stage by exactly one term (`newtonApprox_succ`), which is the Newton
step; at any stage the tail beyond stage `β` has valuation exactly `stepSlope` of stage
`β` (`val_newtonApprox_sub`), so the shift-stability lemmas transport the invariants
through limits.

Consequently `α ↦ v_p(f(newtonApprox f α))` is a strictly increasing, hence injective,
map from the ordinals into `ℚ` — contradicting that `Ordinal` is not a small type
(`not_small_ordinal`).  This replaces the cardinality count "no `ℵ₁`-chain in `ℚ`" of the
paper proof.

## Main declarations

- `TrustworthyKedlaya.pAdicHahnSeries.fromCoeff_add_of_disjoint_support`: addition of
  `p`-adic Hahn series with disjointly supported coefficient functions is coefficientwise
  (no carries), the summation device for the limit stages;
- `TrustworthyKedlaya.pAdicHahnSeries.newtonApprox`: the transfinite Newton approximation;
- `TrustworthyKedlaya.pAdicHahnSeries.exists_eval_eq_zero`: every polynomial over `𝕃_[p]`
  of positive degree has a root;
- `TrustworthyKedlaya.pAdicHahnSeries.isAlgClosed`: `𝕃_[p]` is algebraically closed.
-/

@[expose] public section

namespace TrustworthyKedlaya.pAdicHahnSeries

open Polynomial WittVector

variable {p : ℕ} [hp : Fact (Nat.Prime p)]

/-! ### Coefficientwise addition on disjoint supports

For general sums of `p`-adic Hahn series only the dominated-position rule
`coeff_add_of_le_val` holds (carries!).  But when the two canonical coefficient functions
have disjoint supports, the sum of the canonical (Teichmüller) representatives is again a
Teichmüller series, so the coefficient functions simply add. -/

/-- Rebuilding from equal coefficient functions gives equal series. -/
theorem fromCoeff_congr {s₁ s₂ : ℚ → Fpbar p} (h : s₁ = s₂)
    (h₁ : (Function.support s₁).IsPWO) (h₂ : (Function.support s₂).IsPWO) :
    fromCoeff s₁ h₁ = fromCoeff s₂ h₂ := by
  subst h; rfl

/-- Addition of `p`-adic Hahn series with **disjointly supported** coefficient functions
is coefficientwise: no carries can occur. -/
theorem fromCoeff_add_of_disjoint_support (s₁ s₂ : ℚ → Fpbar p)
    (h₁ : (Function.support s₁).IsPWO) (h₂ : (Function.support s₂).IsPWO)
    (h₁₂ : (Function.support (s₁ + s₂)).IsPWO)
    (hd : ∀ x, s₁ x = 0 ∨ s₂ x = 0) :
    fromCoeff s₁ h₁ + fromCoeff s₂ h₂ = fromCoeff (s₁ + s₂) h₁₂ := by
  have hlift : LiftedPAdicHahnSeries.fromCoeff s₁ h₁ + LiftedPAdicHahnSeries.fromCoeff s₂ h₂
      = LiftedPAdicHahnSeries.fromCoeff (s₁ + s₂) h₁₂ := by
    apply HahnSeries.ext
    funext x
    rw [HahnSeries.coeff_add]
    change teichmuller p (s₁ x) + teichmuller p (s₂ x) = teichmuller p ((s₁ + s₂) x)
    rcases hd x with h | h <;> simp [h, teichmuller_zero]
  simp only [fromCoeff]
  rw [← map_add, hlift]

/-- The valuation of `fromCoeff s` is the least point of the support of `s`. -/
theorem val_fromCoeff_eq (s : ℚ → Fpbar p) (hs : (Function.support s).IsPWO)
    {x₀ : ℚ} (h0 : s x₀ ≠ 0) (hmin : ∀ y, y < x₀ → s y = 0) :
    val p (fromCoeff s hs) = (x₀ : WithTop ℚ) := by
  have hc : (fromCoeff s hs).coeff = s := coeff_of_fromCoeff_eq_self s hs
  have hne : fromCoeff s hs ≠ 0 := by
    intro h
    have h0' : (fromCoeff s hs).coeff x₀ = s x₀ := congrFun hc x₀
    rw [h, coeff_zero_eq] at h0'
    exact h0 h0'.symm
  have hle : val p (fromCoeff s hs) ≤ (x₀ : WithTop ℚ) :=
    val_le_of_coeff_ne_zero (by rw [hc]; exact h0)
  have hcoe : ((valQ (fromCoeff s hs) : ℚ) : WithTop ℚ) = val p (fromCoeff s hs) :=
    coe_valQ hne
  have hq_ne : s (valQ (fromCoeff s hs)) ≠ 0 := by
    have h := coeff_val_ne_zero (x := fromCoeff s hs) hcoe.symm
    rwa [hc] at h
  have hqle : valQ (fromCoeff s hs) ≤ x₀ := by
    rw [← hcoe] at hle
    exact_mod_cast hle
  have hxle : x₀ ≤ valQ (fromCoeff s hs) := not_lt.mp fun hlt => hq_ne (hmin _ hlt)
  rw [← hcoe, le_antisymm hqle hxle]

/-! ### The Newton step data -/

variable (f : Polynomial 𝕃_[p])

/-- The **slope** of the Newton step at approximation `r`: the last Newton slope of
`f(T + r)`. -/
noncomputable def stepSlope (r : 𝕃_[p]) : ℚ := lastSlope (Polynomial.taylor r f)

open Classical in
/-- The **digit** of the Newton step at approximation `r`: a root in `𝔽ᵃ_[p]` of the
residue polynomial of `f(T + r)` (junk value `0` if none exists). -/
noncomputable def stepDigit (r : 𝕃_[p]) : Fpbar p :=
  if h : ∃ c, (residuePoly (Polynomial.taylor r f)).eval c = 0 then h.choose else 0

/-- The **increment** of the Newton step at approximation `r`: the one-term series
`[stepDigit f r] p^(stepSlope f r)`. -/
noncomputable def stepTerm (r : 𝕃_[p]) : 𝕃_[p] := single (stepSlope f r) (stepDigit f r)

/-! ### Histories and their digit sums

A *history* below an ordinal `α` is a family `H : ∀ β < α, 𝕃_[p]` of approximations; the
recursion feeds each stage the full history of the previous stages.  Provided the step
slopes are strictly monotone along the history (`SlopeMono`), the step digits sit at
strictly increasing positions, so they form a legitimate coefficient function
(`histDigits`) and can be summed into a single series (`histSum`). -/

/-- Strict monotonicity of the step slopes along a history: the well-formedness condition
for summing the increments of a history into a single series. -/
def SlopeMono (α : Ordinal.{0}) (H : ∀ β, β < α → 𝕃_[p]) : Prop :=
  ∀ β₁ (h₁ : β₁ < α) β₂ (h₂ : β₂ < α), β₁ < β₂ →
    stepSlope f (H β₁ h₁) < stepSlope f (H β₂ h₂)

open Classical in
/-- The coefficient function collecting the digits of a history: value
`stepDigit f (H β)` at position `stepSlope f (H β)`, and `0` elsewhere. -/
noncomputable def histDigits (α : Ordinal.{0}) (H : ∀ β, β < α → 𝕃_[p]) : ℚ → Fpbar p :=
  fun x =>
    if h : ∃ β, ∃ hβ : β < α, stepSlope f (H β hβ) = x then
      stepDigit f (H h.choose h.choose_spec.choose)
    else 0

theorem histDigits_stepSlope {α : Ordinal.{0}} {H : ∀ β, β < α → 𝕃_[p]}
    (hw : SlopeMono f α H) {β : Ordinal.{0}} (hβ : β < α) :
    histDigits f α H (stepSlope f (H β hβ)) = stepDigit f (H β hβ) := by
  have hex : ∃ γ, ∃ hγ : γ < α, stepSlope f (H γ hγ) = stepSlope f (H β hβ) := ⟨β, hβ, rfl⟩
  have key : ∀ γ (hγ : γ < α), stepSlope f (H γ hγ) = stepSlope f (H β hβ) →
      stepDigit f (H γ hγ) = stepDigit f (H β hβ) := by
    intro γ hγ hEq
    rcases lt_trichotomy γ β with h | h | h
    · exact absurd hEq (ne_of_lt (hw _ hγ _ hβ h))
    · subst h; rfl
    · exact absurd hEq.symm (ne_of_lt (hw _ hβ _ hγ h))
  simp only [histDigits]
  rw [dif_pos hex]
  exact key _ _ hex.choose_spec.choose_spec

theorem histDigits_eq_zero {α : Ordinal.{0}} {H : ∀ β, β < α → 𝕃_[p]} {x : ℚ}
    (hx : ∀ β (hβ : β < α), stepSlope f (H β hβ) ≠ x) : histDigits f α H x = 0 := by
  simp only [histDigits]
  exact dif_neg fun ⟨β, hβ, hEq⟩ => hx β hβ hEq

theorem support_histDigits_subset (α : Ordinal.{0}) (H : ∀ β, β < α → 𝕃_[p]) :
    Function.support (histDigits f α H) ⊆
      Set.range fun β : {β : Ordinal.{0} // β < α} => stepSlope f (H β.1 β.2) := by
  intro x hx
  simp only [Function.mem_support] at hx
  by_contra hmem
  refine hx (histDigits_eq_zero f fun β hβ hEq => hmem ?_)
  exact ⟨⟨β, hβ⟩, hEq⟩

theorem isPWO_support_histDigits (α : Ordinal.{0}) (H : ∀ β, β < α → 𝕃_[p])
    (hw : SlopeMono f α H) : (Function.support (histDigits f α H)).IsPWO := by
  refine Set.IsPWO.mono (Set.IsWF.isPWO ?_) (support_histDigits_subset f α H)
  refine (Set.wellFoundedOn_range).mpr ?_
  refine Subrelation.wf (r := InvImage (· < ·)
    (Subtype.val : {β : Ordinal.{0} // β < α} → Ordinal.{0})) ?_ (InvImage.wf _ Ordinal.lt_wf)
  intro a b hab
  have hab' : stepSlope f (H a.1 a.2) < stepSlope f (H b.1 b.2) := hab
  change a.1 < b.1
  by_contra hle
  push Not at hle
  rcases eq_or_lt_of_le hle with h | h
  · obtain rfl : b = a := Subtype.ext h
    exact absurd hab' (lt_irrefl _)
  · exact absurd (hw b.1 b.2 a.1 a.2 h) (lt_asymm hab')

open Classical in
/-- The digit sum of a history: the series whose canonical coefficient function collects
the digits of the history (junk value `0` if the slopes are not strictly monotone). -/
noncomputable def histSum (α : Ordinal.{0}) (H : ∀ β, β < α → 𝕃_[p]) : 𝕃_[p] :=
  if hw : SlopeMono f α H then
    fromCoeff (histDigits f α H) (isPWO_support_histDigits f α H hw)
  else 0

/-! ### The transfinite Newton approximation -/

/-- The transfinite Newton approximation: stage `α` is the digit sum of the full history
of previous stages.  At a successor this adds one Newton step to the previous stage
(`newtonApprox_succ`); at a limit it sums all previous increments. -/
noncomputable def newtonApprox : Ordinal.{0} → 𝕃_[p] :=
  Ordinal.lt_wf.fix fun α IH => histSum f α IH

theorem newtonApprox_def (α : Ordinal.{0}) :
    newtonApprox f α = histSum f α fun β _ => newtonApprox f β :=
  WellFounded.fix_eq _ _ _

/-- The history of Newton approximations below `α`. -/
noncomputable abbrev approxHist (α : Ordinal.{0}) : ∀ β, β < α → 𝕃_[p] :=
  fun β _ => newtonApprox f β

/-- Well-formedness at stage `α`: the step slopes of the Newton approximations are
strictly monotone below `α`.  Established for every `α` in
`newtonApprox_strictMono_data`. -/
def ApproxMono (α : Ordinal.{0}) : Prop := SlopeMono f α (approxHist f α)

theorem ApproxMono.mono {f : Polynomial 𝕃_[p]} {α σ : Ordinal.{0}}
    (hw : ApproxMono f α) (hσ : σ ≤ α) : ApproxMono f σ :=
  fun β₁ h₁ β₂ h₂ hlt => hw β₁ (h₁.trans_le hσ) β₂ (h₂.trans_le hσ) hlt

theorem ApproxMono.slope_lt {f : Polynomial 𝕃_[p]} {α : Ordinal.{0}}
    (hw : ApproxMono f α) {β₁ β₂ : Ordinal.{0}} (h₁ : β₁ < α) (h₂ : β₂ < α) (hlt : β₁ < β₂) :
    stepSlope f (newtonApprox f β₁) < stepSlope f (newtonApprox f β₂) :=
  hw β₁ h₁ β₂ h₂ hlt

/-- The digit function of the Newton history below `α`. -/
noncomputable abbrev approxDigits (α : Ordinal.{0}) : ℚ → Fpbar p :=
  histDigits f α (approxHist f α)

theorem newtonApprox_eq_fromCoeff {α : Ordinal.{0}} (hw : ApproxMono f α) :
    newtonApprox f α
      = fromCoeff (approxDigits f α) (isPWO_support_histDigits f α (approxHist f α) hw) := by
  rw [newtonApprox_def]
  exact dif_pos hw

theorem approxDigits_stepSlope {α : Ordinal.{0}} (hw : ApproxMono f α) {β : Ordinal.{0}}
    (hβ : β < α) :
    approxDigits f α (stepSlope f (newtonApprox f β)) = stepDigit f (newtonApprox f β) :=
  histDigits_stepSlope f hw hβ

theorem approxDigits_eq_zero {α : Ordinal.{0}} {x : ℚ}
    (hx : ∀ γ, γ < α → stepSlope f (newtonApprox f γ) ≠ x) :
    approxDigits f α x = 0 :=
  histDigits_eq_zero f hx

/-! ### The tail decomposition

For `β < α` (with well-formedness at `α`), the digit functions of stages `β` and `α`
agree strictly below position `stepSlope f (newtonApprox f β)` and the tail difference is
supported at positions `≥` that slope, with a nonzero digit exactly there.  Hence stage
`α` splits as stage `β` plus a tail of valuation exactly the stage-`β` slope. -/

theorem approxDigits_lt_of_ne_zero {α β : Ordinal.{0}} (hβ : β < α) (hwα : ApproxMono f α)
    {x : ℚ} (hx : approxDigits f β x ≠ 0) : x < stepSlope f (newtonApprox f β) := by
  by_contra hge
  push Not at hge
  refine hx (approxDigits_eq_zero f fun γ hγ hEq => ?_)
  have h := hwα.slope_lt (hγ.trans hβ) hβ hγ
  rw [hEq] at h
  exact absurd h (not_lt.mpr hge)

theorem exists_index_of_tailDigits_ne_zero {α β : Ordinal.{0}} (hβ : β < α)
    (hwα : ApproxMono f α) {x : ℚ} (hx : approxDigits f α x - approxDigits f β x ≠ 0) :
    ∃ γ, β ≤ γ ∧ γ < α ∧ stepSlope f (newtonApprox f γ) = x := by
  have hwβ : ApproxMono f β := hwα.mono hβ.le
  by_cases hex : ∃ γ, ∃ hγ : γ < α, stepSlope f (newtonApprox f γ) = x
  · obtain ⟨γ, hγ, hEq⟩ := hex
    rcases lt_or_ge γ β with h | h
    · exfalso
      apply hx
      have h1 : approxDigits f α x = stepDigit f (newtonApprox f γ) :=
        hEq ▸ approxDigits_stepSlope f hwα hγ
      have h2 : approxDigits f β x = stepDigit f (newtonApprox f γ) :=
        hEq ▸ approxDigits_stepSlope f hwβ h
      rw [sub_eq_zero]
      exact h1.trans h2.symm
    · exact ⟨γ, h, hγ, hEq⟩
  · exfalso
    apply hx
    push Not at hex
    have h1 : approxDigits f α x = 0 := approxDigits_eq_zero f fun γ hγ => hex γ hγ
    have h2 : approxDigits f β x = 0 :=
      approxDigits_eq_zero f fun γ hγ => hex γ (hγ.trans hβ)
    rw [sub_eq_zero]
    exact h1.trans h2.symm

theorem stepSlope_le_of_tailDigits_ne_zero {α β : Ordinal.{0}} (hβ : β < α)
    (hwα : ApproxMono f α) {x : ℚ} (hx : approxDigits f α x - approxDigits f β x ≠ 0) :
    stepSlope f (newtonApprox f β) ≤ x := by
  obtain ⟨γ, hβγ, hγ, hEq⟩ := exists_index_of_tailDigits_ne_zero f hβ hwα hx
  rcases eq_or_lt_of_le hβγ with rfl | h
  · exact le_of_eq hEq
  · exact hEq ▸ (hwα.slope_lt hβ hγ h).le

theorem tailDigits_at_stepSlope {α β : Ordinal.{0}} (hβ : β < α) (hwα : ApproxMono f α) :
    approxDigits f α (stepSlope f (newtonApprox f β))
        - approxDigits f β (stepSlope f (newtonApprox f β))
      = stepDigit f (newtonApprox f β) := by
  have h1 := approxDigits_stepSlope f hwα hβ
  have h2 : approxDigits f β (stepSlope f (newtonApprox f β)) = 0 := by
    refine approxDigits_eq_zero f fun γ hγ => ?_
    exact (hwα.slope_lt (hγ.trans hβ) hβ hγ).ne
  simp only [h1, h2, sub_zero]

theorem isPWO_support_tailDigits {α β : Ordinal.{0}} (hβ : β < α) (hwα : ApproxMono f α) :
    (Function.support (approxDigits f α - approxDigits f β)).IsPWO := by
  refine Set.IsPWO.mono ((isPWO_support_histDigits f α _ hwα).union
    (isPWO_support_histDigits f β _ (hwα.mono hβ.le))) ?_
  intro x hx
  simp only [Function.mem_support, Pi.sub_apply] at hx
  simp only [Set.mem_union, Function.mem_support]
  by_contra h
  push Not at h
  refine hx ?_
  rw [sub_eq_zero]
  exact h.1.trans h.2.symm

theorem newtonApprox_sub_eq {α β : Ordinal.{0}} (hβ : β < α) (hwα : ApproxMono f α) :
    newtonApprox f α - newtonApprox f β
      = fromCoeff (approxDigits f α - approxDigits f β) (isPWO_support_tailDigits f hβ hwα)
    := by
  have hwβ : ApproxMono f β := hwα.mono hβ.le
  have hdisj : ∀ x, approxDigits f β x = 0 ∨ (approxDigits f α - approxDigits f β) x = 0 := by
    intro x
    by_cases h : approxDigits f β x = 0
    · exact Or.inl h
    · refine Or.inr ?_
      by_contra hd
      rw [Pi.sub_apply] at hd
      exact absurd (approxDigits_lt_of_ne_zero f hβ hwα h)
        (not_lt.mpr (stepSlope_le_of_tailDigits_ne_zero f hβ hwα hd))
  have hfun : approxDigits f β + (approxDigits f α - approxDigits f β) = approxDigits f α := by
    funext x
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  have hkey : fromCoeff (approxDigits f α) (isPWO_support_histDigits f α _ hwα)
      = fromCoeff (approxDigits f β) (isPWO_support_histDigits f β _ hwβ)
        + fromCoeff (approxDigits f α - approxDigits f β)
            (isPWO_support_tailDigits f hβ hwα) := by
    rw [fromCoeff_add_of_disjoint_support _ _ _ _
      (hfun.symm ▸ isPWO_support_histDigits f α _ hwα) hdisj]
    exact (fromCoeff_congr hfun _ _).symm
  rw [newtonApprox_eq_fromCoeff f hwα, newtonApprox_eq_fromCoeff f hwβ, hkey]
  ring

/-! ### The Newton step under the no-root hypothesis

From here on we assume `f` has positive degree and **no root at all**; the recursion then
never terminates, and each stage strictly improves the previous ones. -/

variable {f}

theorem taylor_ne_zero_of_eval_ne_zero (hroot : ∀ r : 𝕃_[p], f.eval r ≠ 0) (r : 𝕃_[p]) :
    Polynomial.taylor r f ≠ 0 := fun h =>
  hroot r (by rw [← Polynomial.taylor_coeff_zero (r := r), h, Polynomial.coeff_zero])

theorem taylor_coeff_zero_ne_zero (hroot : ∀ r : 𝕃_[p], f.eval r ≠ 0) (r : 𝕃_[p]) :
    (Polynomial.taylor r f).coeff 0 ≠ 0 := by
  rw [Polynomial.taylor_coeff_zero]
  exact hroot r

theorem taylor_natDegree_ne_zero (hdeg : f.natDegree ≠ 0) (r : 𝕃_[p]) :
    (Polynomial.taylor r f).natDegree ≠ 0 := by
  rw [Polynomial.natDegree_taylor]
  exact hdeg

theorem residuePoly_taylor_degree_ne_zero (hdeg : f.natDegree ≠ 0)
    (hroot : ∀ r : 𝕃_[p], f.eval r ≠ 0) (r : 𝕃_[p]) :
    (residuePoly (Polynomial.taylor r f)).degree ≠ 0 := by
  obtain ⟨k, hk1, hkn, hkne⟩ := exists_residuePoly_coeff_ne_zero
    (taylor_ne_zero_of_eval_ne_zero hroot r) (taylor_natDegree_ne_zero hdeg r)
    (taylor_coeff_zero_ne_zero hroot r)
  intro hdeg0
  have hk := Polynomial.le_degree_of_ne_zero hkne
  rw [hdeg0] at hk
  have h1 : ((k : ℕ) : WithBot ℕ) ≤ ((0 : ℕ) : WithBot ℕ) := by exact_mod_cast hk
  have h2 : k ≤ 0 := by exact_mod_cast h1
  omega

theorem stepDigit_isRoot (hdeg : f.natDegree ≠ 0) (hroot : ∀ r : 𝕃_[p], f.eval r ≠ 0)
    (r : 𝕃_[p]) : (residuePoly (Polynomial.taylor r f)).eval (stepDigit f r) = 0 := by
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_root (residuePoly (Polynomial.taylor r f))
    (residuePoly_taylor_degree_ne_zero hdeg hroot r)
  have hex : ∃ c, (residuePoly (Polynomial.taylor r f)).eval c = 0 := ⟨c, hc⟩
  simp only [stepDigit]
  rw [dif_pos hex]
  exact hex.choose_spec

theorem stepDigit_ne_zero (hdeg : f.natDegree ≠ 0) (hroot : ∀ r : 𝕃_[p], f.eval r ≠ 0)
    (r : 𝕃_[p]) : stepDigit f r ≠ 0 := by
  intro h0
  have h := stepDigit_isRoot hdeg hroot r
  rw [h0, ← Polynomial.coeff_zero_eq_eval_zero] at h
  exact residuePoly_coeff_zero_ne_zero (taylor_coeff_zero_ne_zero hroot r) h

/-- The Newton step strictly increases the slope (Wang-Yuan, Proposition 2.7(2)). -/
theorem stepSlope_lt_step (hdeg : f.natDegree ≠ 0) (hroot : ∀ r : 𝕃_[p], f.eval r ≠ 0)
    (r : 𝕃_[p]) : stepSlope f r < stepSlope f (r + stepTerm f r) := by
  have hP := taylor_ne_zero_of_eval_ne_zero hroot r
  have hn := taylor_natDegree_ne_zero hdeg r
  have h0 := taylor_coeff_zero_ne_zero hroot r
  obtain ⟨q, hq1, hqn, hqne⟩ :=
    exists_taylor_residuePoly_coeff_ne_zero hP hn h0 (stepDigit f r)
  have hQ0 : (Polynomial.taylor (single (lastSlope (Polynomial.taylor r f)) (stepDigit f r))
      (Polynomial.taylor r f)).coeff 0 ≠ 0 := by
    rw [Polynomial.taylor_taylor, Polynomial.taylor_coeff_zero]
    exact hroot _
  have hkey := lastSlope_lt_lastSlope_taylor h0 (stepDigit_isRoot hdeg hroot r)
    hq1 hqn hqne hQ0
  rw [Polynomial.taylor_taylor,
    add_comm (single (lastSlope (Polynomial.taylor r f)) (stepDigit f r)) r] at hkey
  exact hkey

/-- The Newton step strictly increases the valuation of the value
(Wang-Yuan, Proposition 2.7(1)). -/
theorem val_eval_lt_step (hdeg : f.natDegree ≠ 0) (hroot : ∀ r : 𝕃_[p], f.eval r ≠ 0)
    (r : 𝕃_[p]) : val p (f.eval r) < val p (f.eval (r + stepTerm f r)) := by
  have h0 := taylor_coeff_zero_ne_zero hroot r
  have hkey := val_lt_val_taylor_coeff_zero h0 (stepDigit_isRoot hdeg hroot r)
  rw [Polynomial.taylor_taylor] at hkey
  simp only [Polynomial.taylor_coeff_zero] at hkey
  rw [add_comm (single (lastSlope (Polynomial.taylor r f)) (stepDigit f r)) r] at hkey
  exact hkey

/-- Shifting by any tail of valuation at least the current slope cannot decrease the
slope (Wang-Yuan, Lemma 2.4; the limit-stage transport). -/
theorem stepSlope_le_shift (hdeg : f.natDegree ≠ 0) (hroot : ∀ r : 𝕃_[p], f.eval r ≠ 0)
    (r z : 𝕃_[p]) (hz : (stepSlope f r : WithTop ℚ) ≤ val p z) :
    stepSlope f r ≤ stepSlope f (r + z) := by
  have hP := taylor_ne_zero_of_eval_ne_zero hroot r
  have hn := taylor_natDegree_ne_zero hdeg r
  have h0 := taylor_coeff_zero_ne_zero hroot r
  have hz0 : (Polynomial.taylor z (Polynomial.taylor r f)).coeff 0 ≠ 0 := by
    rw [Polynomial.taylor_taylor, Polynomial.taylor_coeff_zero]
    exact hroot _
  have hkey := lastSlope_le_lastSlope_taylor hP hn h0 hz hz0
  rw [Polynomial.taylor_taylor, add_comm z r] at hkey
  exact hkey

/-- Shifting by any tail of valuation at least the current slope cannot decrease the
valuation of the value (Wang-Yuan, Lemma 2.4; the limit-stage transport). -/
theorem val_eval_le_shift (hroot : ∀ r : 𝕃_[p], f.eval r ≠ 0)
    (r z : 𝕃_[p]) (hz : (stepSlope f r : WithTop ℚ) ≤ val p z) :
    val p (f.eval r) ≤ val p (f.eval (r + z)) := by
  have h0 := taylor_coeff_zero_ne_zero hroot r
  have hkey := le_val_eval_of_lastSlope_le h0 hz
  rw [Polynomial.taylor_coeff_zero, Polynomial.taylor_eval, add_comm z r] at hkey
  exact hkey

/-! ### The invariants of the recursion -/

/-- The valuation of the tail beyond stage `β` is exactly the stage-`β` slope. -/
theorem val_newtonApprox_sub (hdeg : f.natDegree ≠ 0) (hroot : ∀ r : 𝕃_[p], f.eval r ≠ 0)
    {α β : Ordinal.{0}} (hβ : β < α) (hwα : ApproxMono f α) :
    val p (newtonApprox f α - newtonApprox f β)
      = (stepSlope f (newtonApprox f β) : WithTop ℚ) := by
  rw [newtonApprox_sub_eq f hβ hwα]
  refine val_fromCoeff_eq _ _ ?_ ?_
  · rw [Pi.sub_apply, tailDigits_at_stepSlope f hβ hwα]
    exact stepDigit_ne_zero hdeg hroot _
  · intro y hy
    rw [Pi.sub_apply]
    by_contra h
    exact absurd (stepSlope_le_of_tailDigits_ne_zero f hβ hwα h) (not_le.mpr hy)

/-- At a successor stage the recursion adds exactly one Newton step. -/
theorem newtonApprox_succ {α β : Ordinal.{0}} (hβ : β < α) (hsucc : Order.succ β = α)
    (hwα : ApproxMono f α) :
    newtonApprox f α = newtonApprox f β + stepTerm f (newtonApprox f β) := by
  have hone : fromCoeff (approxDigits f α - approxDigits f β)
      (isPWO_support_tailDigits f hβ hwα) = stepTerm f (newtonApprox f β) := by
    apply ext_coeff
    rw [coeff_of_fromCoeff_eq_self]
    simp only [stepTerm]
    rw [coeff_single]
    funext x
    rw [Pi.sub_apply]
    by_cases hx : x = stepSlope f (newtonApprox f β)
    · rw [if_pos hx, hx]
      exact tailDigits_at_stepSlope f hβ hwα
    · rw [if_neg hx]
      by_contra h
      obtain ⟨γ, hβγ, hγ, hEq⟩ := exists_index_of_tailDigits_ne_zero f hβ hwα h
      have hγβ : γ ≤ β := by
        rw [← hsucc] at hγ
        exact Order.lt_succ_iff.mp hγ
      exact hx (by rw [← hEq, le_antisymm hγβ hβγ])
  have hsub := newtonApprox_sub_eq f hβ hwα
  rw [hone] at hsub
  rw [← hsub]
  ring

/-- The two strict-monotonicity invariants of the transfinite Newton recursion, proved by
one uniform transfinite induction: along the stages, both the step slope and the
valuation of the value strictly increase. -/
theorem newtonApprox_strictMono_data (hdeg : f.natDegree ≠ 0)
    (hroot : ∀ r : 𝕃_[p], f.eval r ≠ 0) (α : Ordinal.{0}) :
    ∀ β, β < α →
      stepSlope f (newtonApprox f β) < stepSlope f (newtonApprox f α) ∧
      val p (f.eval (newtonApprox f β)) < val p (f.eval (newtonApprox f α)) := by
  induction α using WellFoundedLT.induction with
  | ind α IH =>
    intro β hβ
    have hwle : ∀ σ, σ ≤ α → ApproxMono f σ := by
      intro σ hσ γ₁ h₁ γ₂ h₂ hlt
      exact (IH γ₂ (h₂.trans_le hσ) γ₁ hlt).1
    have hwα : ApproxMono f α := hwle α le_rfl
    rcases eq_or_lt_of_le (Order.succ_le_of_lt hβ) with hsucc | hlt
    · have hstep := newtonApprox_succ hβ hsucc hwα
      constructor
      · rw [hstep]
        exact stepSlope_lt_step hdeg hroot _
      · rw [hstep]
        exact val_eval_lt_step hdeg hroot _
    · have h1 := IH (Order.succ β) hlt β (Order.lt_succ β)
      have hz : (stepSlope f (newtonApprox f (Order.succ β)) : WithTop ℚ)
          ≤ val p (newtonApprox f α - newtonApprox f (Order.succ β)) :=
        le_of_eq (val_newtonApprox_sub hdeg hroot hlt hwα).symm
      have hcomb : newtonApprox f (Order.succ β)
          + (newtonApprox f α - newtonApprox f (Order.succ β)) = newtonApprox f α := by
        ring
      constructor
      · refine h1.1.trans_le ?_
        have h2 := stepSlope_le_shift hdeg hroot (newtonApprox f (Order.succ β)) _ hz
        rwa [hcomb] at h2
      · refine h1.2.trans_le ?_
        have h2 := val_eval_le_shift hroot (newtonApprox f (Order.succ β)) _ hz
        rwa [hcomb] at h2

/-! ### Termination and the main results -/

/-- If `f` (of positive degree) had no root, the valuations `v_p(f(newtonApprox f α))`
would embed the ordinals strictly monotonically into `ℚ` — impossible, since `Ordinal` is
not a small type. -/
theorem no_root_false (hdeg : f.natDegree ≠ 0) (hroot : ∀ r : 𝕃_[p], f.eval r ≠ 0) :
    False := by
  have hmono : StrictMono fun α : Ordinal.{0} => valQ (f.eval (newtonApprox f α)) := by
    intro β α hβα
    have h := (newtonApprox_strictMono_data hdeg hroot α β hβα).2
    rw [← coe_valQ (hroot (newtonApprox f β)), ← coe_valQ (hroot (newtonApprox f α))] at h
    exact_mod_cast h
  exact not_small_ordinal.{0} (small_of_injective hmono.injective)

variable (f)

/-- **Every polynomial of positive degree over `𝕃_p` has a root** (Wang-Yuan,
Theorem 2.8; Kedlaya 2001b, Proposition 2): the transfinite Newton recursion must reach a
root at some (countable) stage. -/
theorem exists_eval_eq_zero (hdeg : f.natDegree ≠ 0) : ∃ r : 𝕃_[p], f.eval r = 0 := by
  by_contra h
  push Not at h
  exact no_root_false hdeg h

/-- **`𝕃_p` is algebraically closed** (Wang-Yuan, Theorem 2.8; Kedlaya 2001b,
Proposition 2). -/
instance isAlgClosed : IsAlgClosed (𝕃_[p]) := by
  refine IsAlgClosed.of_exists_root _ fun P _ hirr => ?_
  obtain ⟨r, hr⟩ := exists_eval_eq_zero P hirr.natDegree_pos.ne'
  exact ⟨r, hr⟩

end TrustworthyKedlaya.pAdicHahnSeries
