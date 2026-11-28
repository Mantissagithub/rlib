module

import Rlib

open Rlib

/-- The KL penalty is zero exactly at the old policy, so it is the only distribution with zero
divergence from a softmax policy. -/
example (θ : Bool → Bool → ℝ) (p : PMF Bool) (h : kl p (softmaxPolicy θ true) = 0) :
    p = softmaxPolicy θ true :=
  eq_of_kl_eq_zero p _ (MDP.softmaxPolicy_ne_zero θ true) h

/-- The exact KL-penalized PPO step from a softmax policy is itself a KL-penalized PPO step. -/
example (m : MDP Bool Bool) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (θ : Bool → Bool → ℝ) :
    m.IsKLPenaltyStep hγ0 hγ1 2 (softmaxPolicy θ)
      (softmaxPolicy fun s a => θ s a + m.advantage (softmaxPolicy θ) hγ0 hγ1 s a / 2) :=
  (m.eq_softmaxPolicy_iff_isKLPenaltyStep hγ0 hγ1 θ two_pos _).mpr rfl
