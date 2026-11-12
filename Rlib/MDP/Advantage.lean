module

public import Rlib.MDP.PolicyEvaluation

/-! # Action values and advantages of a stationary policy -/

@[expose] public section

noncomputable section

namespace Rlib.MDP

variable {S A : Type*} [Fintype S] [Fintype A]

/-- The value of taking an action and then following a stationary policy. -/
def policyActionValue (m : MDP S A) (π : StationaryPolicy S A) {γ : ℝ} (hγ0 : 0 ≤ γ)
    (hγ1 : γ < 1) (s : S) (a : A) : ℝ :=
  m.oneStepActionValue γ (m.policyValue π hγ0 hγ1) s a

/-- How much better an action is than the policy's average action at a state. -/
def advantage (m : MDP S A) (π : StationaryPolicy S A) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (s : S) (a : A) : ℝ :=
  m.policyActionValue π hγ0 hγ1 s a - m.policyValue π hγ0 hγ1 s

/-- Averaging a policy's action values over its own action choice gives its state value. -/
theorem expect_policyActionValue (m : MDP S A) (π : StationaryPolicy S A) {γ : ℝ}
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (s : S) :
    expect (π s) (m.policyActionValue π hγ0 hγ1 s) = m.policyValue π hγ0 hγ1 s :=
  congrFun (m.oneStepValue_policyValue π hγ0 hγ1) s

/-- A policy's advantages average to zero under its own action choice. -/
theorem expect_advantage (m : MDP S A) (π : StationaryPolicy S A) {γ : ℝ}
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (s : S) :
    expect (π s) (m.advantage π hγ0 hγ1 s) = 0 := by
  have h : m.advantage π hγ0 hγ1 s =
      fun a => m.policyActionValue π hγ0 hγ1 s a + (-1) * m.policyValue π hγ0 hγ1 s := by
    funext a
    simp only [advantage]
    ring
  rw [h, expect_add, expect_mul, expect_const, expect_policyActionValue]
  ring

/-- A policy's action values satisfy the Bellman equation for action values under that
policy. -/
theorem policyActionValue_eq (m : MDP S A) (π : StationaryPolicy S A) {γ : ℝ}
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (s : S) (a : A) :
    m.policyActionValue π hγ0 hγ1 s a =
      m.reward s a + γ * expect (m.transition s a)
        (fun t => expect (π t) (m.policyActionValue π hγ0 hγ1 t)) := by
  simp only [expect_policyActionValue]
  rfl

end Rlib.MDP
