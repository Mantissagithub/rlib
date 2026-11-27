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

/-- CPI starts from the initial policy. -/
example (m : MDP Bool Bool) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (μ : PMF Bool)
    (G : StationaryPolicy Bool Bool → StationaryPolicy Bool Bool)
    (π₀ : StationaryPolicy Bool Bool) :
    m.cpiPolicy hγ0 hγ1 μ G 1 π₀ 0 = π₀ :=
  rfl
