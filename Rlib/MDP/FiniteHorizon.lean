module

public import Rlib.MDP.Basic
public import Mathlib.Data.Fin.Tuple.Basic

/-! # Finite trajectories and discounted returns under a fixed policy -/

@[expose] public section

noncomputable section

namespace Rlib

/-- Each step records its action and successor state; the initial state is supplied separately. -/
abbrev FiniteTrajectory (S A : Type*) (n : ℕ) := Fin n → A × S

/-- An infinite sequence of actions and successor states, with a separate initial state. -/
abbrev InfiniteTrajectory (S A : Type*) := ℕ → A × S

namespace InfiniteTrajectory

variable {S A : Type*}

/-- The first `n` steps of an infinite trajectory. -/
def «prefix» (n : ℕ) (ω : InfiniteTrajectory S A) : FiniteTrajectory S A n :=
  fun i => ω i

/-- The state where step `n` takes its action. -/
def stateBefore (s : S) (ω : InfiniteTrajectory S A) : ℕ → S
  | 0 => s
  | n + 1 => (ω n).2

end InfiniteTrajectory

namespace MDP

variable {S A : Type*}

/-- Sample `n` actions and transitions under a stationary randomized policy. -/
def trajectoryLaw (m : MDP S A) (π : StationaryPolicy S A) :
    (n : ℕ) → S → PMF (FiniteTrajectory S A n)
  | 0, _ => PMF.pure Fin.elim0
  | n + 1, s => (π s).bind fun a => (m.transition s a).bind fun s' =>
      (m.trajectoryLaw π n s').map (Fin.cons (a, s'))

/-- Sum `n` discounted stored expected rewards along a trajectory, without sampling reward noise. -/
def discountedReturn (m : MDP S A) (γ : ℝ) :
    (n : ℕ) → S → FiniteTrajectory S A n → ℝ
  | 0, _, _ => 0
  | n + 1, s, t => m.reward s (t 0).1 +
      γ * m.discountedReturn γ n (t 0).2 (Fin.tail t)

/-- The expectation of the discounted path return under the sampled trajectory law. -/
def expectedReturn [Fintype S] [Fintype A] (m : MDP S A)
    (π : StationaryPolicy S A) (γ : ℝ) (n : ℕ) (s : S) : ℝ :=
  expect (m.trajectoryLaw π n s) (m.discountedReturn γ n s)

/-- An empty trajectory earns zero reward. -/
@[simp] theorem expectedReturn_zero [Fintype S] [Fintype A] (m : MDP S A)
    (π : StationaryPolicy S A) (γ : ℝ) : m.expectedReturn π γ 0 = fun _ => 0 := by
  funext s
  simp [expectedReturn, discountedReturn]

/-- One more sampled step satisfies the fixed-policy Bellman recursion. -/
theorem expectedReturn_succ [Fintype S] [Fintype A] (m : MDP S A)
    (π : StationaryPolicy S A) (γ : ℝ) (n : ℕ) :
    m.expectedReturn π γ (n + 1) = m.oneStepValue π γ (m.expectedReturn π γ n) := by
  funext s
  unfold oneStepValue oneStepActionValue expectedReturn
  simp [trajectoryLaw, expect_bind, expect_map, discountedReturn, expect_add, expect_mul]

/-- Expected finite returns are iterates of the fixed-policy operator starting at zero. -/
theorem expectedReturn_eq_iterate [Fintype S] [Fintype A] (m : MDP S A)
    (π : StationaryPolicy S A) (γ : ℝ) (n : ℕ) :
    m.expectedReturn π γ n = (m.oneStepValue π γ)^[n] (fun _ => 0) := by
  induction n with
  | zero => simp
  | succ n ih => rw [expectedReturn_succ, ih, Function.iterate_succ_apply']

end MDP
end Rlib
