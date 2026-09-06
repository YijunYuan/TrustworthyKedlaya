/-
Copyright (c) 2026 Shanwen Wang, Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

import TrustworthyKedlaya.MainResults
import TrustworthyKedlaya.Kedlaya.TowerEmbedding
import TrustworthyKedlaya.Kedlaya.TwistPeriodicity

/-!
# Definitional-equality guards

`TrustworthyKedlaya.UP` re-states `Sabc`, `Tc` and `twistSeq` so that the uniform
periodicity machinery can live *below* `MainResults.lean` in the import graph.  The
`example`s here pin the copies to the originals by `rfl`, and pin `UP.IsUP` to the
exact conclusion of `kedlaya_2001a_theorem15`: if either side drifts, this
file stops elaborating and the build fails.
-/

namespace TrustworthyKedlaya

variable (p : ℕ) [Fact (Nat.Prime p)]

example (a : ℕ+) (b c : ℕ) : UP.Sabc p a b c = Sabc p a b c := rfl

example (c : ℕ) : UP.Tc p c = Tc p c := rfl

example (f : ℚ → 𝔽ᵃ_[p]) (j : ℕ) (b : ℕ →₀ ℕ) (n : ℕ) :
    UP.twistSeq p f j b n = twistSeq p f j b n := rfl

example : UP.intHahnEmbedding p = intHahnEmbedding p := rfl

example (x : HahnSeries ℚ (𝔽ᵃ_[p])) :
    UP.IsUP p x ↔
      (∃ a : ℕ+, ∃ b c : ℕ,
        ((x.support ⊆ Sabc p a b c) ∧
          (∃ M N : ℕ+, ∀ m : ℤ, m ≥ -(b : ℤ) →
              let fm : ℚ → 𝔽ᵃ_[p] := fun z => x.coeff (((m : ℚ) + z) / (a : ℚ))
              ∀ (j : ℕ) (dig : ℕ →₀ ℕ), 0 < j → (∀ i, dig i < p) →
                (dig.sum fun _ v => v) ≤ c →
                ∀ n : ℕ, M ≤ n →
                  twistSeq p fm j dig (n + N) = twistSeq p fm j dig n))) :=
  Iff.rfl

end TrustworthyKedlaya
