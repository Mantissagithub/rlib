module

import Rlib

open Rlib

/-- Policy mirror descent starts from the initial scores. -/
example (m : MDP Bool Bool) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (η : ℕ → ℝ)
    (θ₀ : Bool → Bool → ℝ) : m.pmdScores hγ0 hγ1 η θ₀ 0 = θ₀ :=
  rfl

/-- With constant step `η / (1 - γ)`, policy mirror descent is natural policy gradient. -/
example (m : MDP Bool Bool) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (η : ℝ)
    (θ₀ : Bool → Bool → ℝ) (k : ℕ) :
    m.pmdScores hγ0 hγ1 (fun _ => η / (1 - γ)) θ₀ k = m.npgScores hγ0 hγ1 η θ₀ k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [MDP.pmdScores, MDP.npgScores, ih]
