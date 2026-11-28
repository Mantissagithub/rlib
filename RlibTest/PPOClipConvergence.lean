module

import Rlib

open Rlib

/-- PPO-Clip starts from the initial scores. -/
example (m : MDP Bool Bool) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (K : ℕ → ℕ)
    (D : ℕ → Bool → Option Bool) (θ₀ : Bool → Bool → ℝ) :
    m.ppoClipScores hγ0 hγ1 1 (1 / 5) K D θ₀ 0 = θ₀ :=
  rfl

/-- With batches that alternate between the two actions at every state, PPO-Clip converges to
values at least those of every stationary policy. -/
example (m : MDP Bool Bool) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hr : ∀ s a, m.reward s a ∈ Set.Icc (0 : ℝ) 1) (θ₀ : Bool → Bool → ℝ) :
    ∃ V : Bool → ℝ, (∀ s, Filter.Tendsto (fun t => m.policyValue
        (softmaxPolicy (m.ppoClipScores hγ0 hγ1 1 (1 / 5) (fun _ => 1)
          (fun t _ => some (decide (t % 2 = 0))) θ₀ t)) hγ0 hγ1 s) Filter.atTop (nhds (V s))) ∧
      ∀ (π : StationaryPolicy Bool Bool) s, m.policyValue π hγ0 hγ1 s ≤ V s := by
  refine m.ppoClip_tendsto_optimal hγ0 hγ1 hr one_pos (by norm_num) _ (fun _ => le_rfl) _
    (fun s a N => ?_) θ₀
  cases a
  · exact ⟨2 * N + 1, by omega, by simp⟩
  · exact ⟨2 * N, by omega, by simp⟩
