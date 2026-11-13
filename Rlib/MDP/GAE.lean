module

public import Rlib.MDP.Advantage
public import Rlib.MDP.FiniteHorizon

/-! # Generalized advantage estimation

Generalized advantage estimation sums discounted temporal-difference errors along a trajectory
with weights `c ^ l`, where `c = γ * λ`. With `λ = 0` it is the one-step error, with `λ = 1` it
telescopes to a Monte Carlo return, and with the exact policy value it is an unbiased estimate of
the advantage for every `λ` and horizon.
-/

@[expose] public section

noncomputable section

namespace Rlib.MDP

variable {S A : Type*}

/-- The temporal-difference error of a value estimate `V` on one transition. -/
def tdError (m : MDP S A) (V : S → ℝ) (γ : ℝ) (s : S) (a : A) (s' : S) : ℝ :=
  m.reward s a + γ * V s' - V s

/-- Generalized advantage estimation over `n` steps of a trajectory, with step weight `c`. -/
def generalizedAdvantage (m : MDP S A) (V : S → ℝ) (γ c : ℝ) :
    (n : ℕ) → S → FiniteTrajectory S A n → ℝ
  | 0, _, _ => 0
  | n + 1, s, t => m.tdError V γ s (t 0).1 (t 0).2 +
      c * m.generalizedAdvantage V γ c n (t 0).2 (Fin.tail t)

/-- The state reached after all `n` steps of a trajectory. -/
def finalState : (n : ℕ) → S → FiniteTrajectory S A n → S
  | 0, s, _ => s
  | n + 1, _, t => finalState n (t 0).2 (Fin.tail t)

/-- With `λ = 0`, generalized advantage estimation is the first temporal-difference error. -/
theorem generalizedAdvantage_zero (m : MDP S A) (V : S → ℝ) (γ : ℝ) (n : ℕ) (s : S)
    (t : FiniteTrajectory S A (n + 1)) :
    m.generalizedAdvantage V γ 0 (n + 1) s t = m.tdError V γ s (t 0).1 (t 0).2 := by
  simp [generalizedAdvantage]

/-- With `λ = 1`, generalized advantage estimation telescopes to the discounted return plus the
discounted value of the final state minus the value of the start state. -/
theorem generalizedAdvantage_one (m : MDP S A) (V : S → ℝ) (γ : ℝ) :
    ∀ (n : ℕ) (s : S) (t : FiniteTrajectory S A n),
      m.generalizedAdvantage V γ γ n s t =
        m.discountedReturn γ n s t + γ ^ n * V (finalState n s t) - V s
  | 0, s, t => by simp [generalizedAdvantage, discountedReturn, finalState]
  | n + 1, s, t => by
    simp only [generalizedAdvantage, discountedReturn, finalState, tdError,
      generalizedAdvantage_one m V γ n]
    ring

variable [Fintype S] [Fintype A]

/-- With the exact policy value, the expected temporal-difference error of an action is its
advantage. -/
theorem expect_tdError (m : MDP S A) (π : StationaryPolicy S A) {γ : ℝ} (hγ0 : 0 ≤ γ)
    (hγ1 : γ < 1) (s : S) (a : A) :
    expect (m.transition s a) (m.tdError (m.policyValue π hγ0 hγ1) γ s a) =
      m.advantage π hγ0 hγ1 s a := by
  have h : m.tdError (m.policyValue π hγ0 hγ1) γ s a = fun s' =>
      (m.reward s a - m.policyValue π hγ0 hγ1 s) + γ * m.policyValue π hγ0 hγ1 s' := by
    funext s'
    simp only [tdError]
    ring
  rw [h, expect_add, expect_const, expect_mul]
  simp only [advantage, policyActionValue, oneStepActionValue]
  ring

/-- With the exact policy value, generalized advantage estimation from a state has expectation
zero under the policy's trajectory law, for every step weight and horizon. -/
theorem expect_generalizedAdvantage (m : MDP S A) (π : StationaryPolicy S A) {γ : ℝ}
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (c : ℝ) :
    ∀ (n : ℕ) (s : S), expect (m.trajectoryLaw π n s)
      (m.generalizedAdvantage (m.policyValue π hγ0 hγ1) γ c n s) = 0
  | 0, s => by simp [trajectoryLaw, generalizedAdvantage]
  | n + 1, s => by
    have hinner (a : A) (s' : S) : expect (m.trajectoryLaw π n s') (fun t =>
        m.tdError (m.policyValue π hγ0 hγ1) γ s a s' +
          c * m.generalizedAdvantage (m.policyValue π hγ0 hγ1) γ c n s' t) =
        m.tdError (m.policyValue π hγ0 hγ1) γ s a s' := by
      rw [expect_add, expect_const, expect_mul, expect_generalizedAdvantage m π hγ0 hγ1 c n s',
        mul_zero, add_zero]
    simp only [trajectoryLaw, expect_bind, expect_map, generalizedAdvantage,
      Fin.cons_zero, Fin.tail_cons, hinner, expect_tdError]
    exact m.expect_advantage π hγ0 hγ1 s

/-- **Generalized advantage estimation is unbiased with the exact value.** Taking action `a` at
state `s` and then following `π` for `n` more steps, the expected generalized advantage estimate
with the exact policy value is the advantage of `a`, for every step weight `c = γ * λ`. -/
theorem expect_generalizedAdvantage_action (m : MDP S A) (π : StationaryPolicy S A) {γ : ℝ}
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (c : ℝ) (n : ℕ) (s : S) (a : A) :
    expect (m.transition s a) (fun s' => expect (m.trajectoryLaw π n s') fun t =>
      m.generalizedAdvantage (m.policyValue π hγ0 hγ1) γ c (n + 1) s (Fin.cons (a, s') t)) =
        m.advantage π hγ0 hγ1 s a := by
  simp only [generalizedAdvantage, Fin.cons_zero, Fin.tail_cons, expect_add, expect_mul,
    expect_const, expect_generalizedAdvantage m π hγ0 hγ1 c n, mul_zero, add_zero]
  exact m.expect_tdError π hγ0 hγ1 s a

end Rlib.MDP
