module

import Rlib

open Rlib

/-- The half-and-half mixture of two policies is within `1` of the first in `ℓ¹`. -/
example (π π' : StationaryPolicy Bool Bool) (s : Bool) :
    ∑ a, |(MDP.mixPolicy (1 / 2) π π' s a).toReal - (π s a).toReal| ≤ 1 := by
  have h := MDP.sum_abs_mixPolicy_sub_le (α := 1 / 2) ⟨by norm_num, by norm_num⟩ π π' s
  linarith

/-- At `α = 0` the mixture is the first policy. -/
example (π π' : StationaryPolicy Bool Bool) (s a : Bool) :
    (MDP.mixPolicy 0 π π' s a).toReal = (π s a).toReal := by
  rw [MDP.mixPolicy_toReal ⟨le_rfl, zero_le_one⟩]
  ring
