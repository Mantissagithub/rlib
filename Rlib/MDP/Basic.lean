module

public import Rlib.Probability.Expectation

/-! # Markov decision processes and one-step values -/

@[expose] public section

namespace Rlib

/-- An MDP with all actions available and expected immediate rewards. -/
structure MDP (S A : Type*) where
  transition : S → A → PMF S
  reward : S → A → ℝ

/-- A stationary randomized policy chooses an action distribution at each state. -/
abbrev StationaryPolicy (S A : Type*) := S → PMF A

namespace MDP

variable {S A : Type*}

/-- The immediate reward plus the discounted expected continuation value. -/
noncomputable def oneStepActionValue [Fintype S] (m : MDP S A)
    (γ : ℝ) (v : S → ℝ) (s : S) (a : A) : ℝ :=
  m.reward s a + γ * expect (m.transition s a) v

/-- The one-step action value averaged under a stationary randomized policy. -/
noncomputable def oneStepValue [Fintype S] [Fintype A] (m : MDP S A)
    (π : StationaryPolicy S A) (γ : ℝ) (v : S → ℝ) (s : S) : ℝ :=
  expect (π s) (m.oneStepActionValue γ v s)

/-- A zero continuation leaves only the immediate reward. -/
@[simp] theorem oneStepActionValue_zero [Fintype S] (m : MDP S A)
    (γ : ℝ) (s : S) (a : A) :
    m.oneStepActionValue γ (fun _ => 0) s a = m.reward s a := by
  simp [oneStepActionValue]

end MDP
end Rlib
