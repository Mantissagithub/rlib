module

import Rlib

open Rlib

/-- With the exact model and no bonus, optimistic value iteration dominates the optimal values
(Agarwal, Jiang, Kakade, and Sun, Lemma 7.4). -/
example {S A : Type} [Fintype S] [Fintype A] [Nonempty A] (M : EpisodicMDP S A)
    (hr : ∀ h s a, M.reward h s a ∈ Set.Icc (0 : ℝ) 1) (H h : ℕ) (s : S) :
    M.optValue H h s ≤ M.ucbValue M.transition (fun _ _ _ => 0) H h s :=
  M.optValue_le_ucbValue hr _ _ H (fun h _ s a => by simp) h s

/-- The value of any policy is at most `V*`, which is at most the horizon. -/
example {S A : Type} [Fintype S] [Fintype A] [Nonempty A] (M : EpisodicMDP S A)
    (hr : ∀ h s a, M.reward h s a ∈ Set.Icc (0 : ℝ) 1) (π : EpisodicPolicy S A) (H : ℕ) (s : S) :
    M.value π H 0 s ≤ H := by
  have h1 := M.value_le_optValue π H 0 s
  have h2 := M.optValue_le (fun h s a => (hr h s a).2) (Nat.zero_le H) s
  simp at h2
  linarith

/-- Agarwal, Jiang, Kakade, and Sun, Lemma 7.5, for trajectories in `Bool × Bool`. -/
example (τ : ℕ → ℕ → Bool × Bool) (H K : ℕ) :
    ∑ k ∈ Finset.range K, ∑ h ∈ Finset.range H, 1 / Real.sqrt (visitCount τ k h (τ k h)) ≤
      2 * H * Real.sqrt (4 * K) := by
  simpa using sum_one_div_sqrt_visitCount_le τ H K

/-- Every episode of UCB-VI starts at the start state. -/
example {S A : Type} [Fintype S] [Fintype A] [Nonempty A] [DecidableEq S] [DecidableEq A]
    (M : EpisodicMDP S A) (H : ℕ) (L : ℝ) (s₀ : S) (samples : ℕ → S → A → ℕ → S) (k : ℕ) :
    (M.ucbviTrajectory H L s₀ samples k 0).1 = s₀ := by
  rw [M.ucbviTrajectory_eq]
  rfl

open MeasureTheory in
/-- Resampling one coordinate of a product of two fair coins. -/
example (ν : Bool → PMF Bool) (G : (Bool → Bool) → Bool → ℝ)
    (hG : ∀ ω z y, G (Function.update ω true z) y = G ω y) :
    ∫ ω, G ω (ω true) ∂(Measure.pi fun i => (ν i).toMeasure) =
      ∫ ω, expect (ν true) (G ω) ∂(Measure.pi fun i => (ν i).toMeasure) :=
  integral_pi_resample ν true G hG

open MeasureTheory in
/-- The first state of every episode is the start state, whatever the draws. -/
example {S A : Type} [Fintype S] [Fintype A] [Nonempty A] [DecidableEq S] [DecidableEq A]
    [MeasurableSpace S] [MeasurableSingletonClass S] (M : EpisodicMDP S A) (H K : ℕ) (L : ℝ)
    (s₀ : S) {k : ℕ} (hk : k < K) (f : S → ℝ) :
    ∫ ω, f (M.ucbviTrajectory H L s₀ (EpisodicMDP.tapeSamples ω) k 0).1 ∂M.tapeLaw H K =
      f s₀ := by
  have h := M.integral_ucbviTrajectory_eq_stateDist L s₀ hk 0 (Nat.zero_le H)
    (fun _ s => f s) (fun _ _ _ _ => rfl)
  rw [h]
  simp [EpisodicMDP.stateDist]

open MeasureTheory in
/-- Agarwal, Jiang, Kakade, and Sun, Theorem 7.1, for UCB-VI on pre-drawn successors. -/
example {S A : Type} [Fintype S] [Fintype A] [Nonempty A] [DecidableEq S] [DecidableEq A]
    [MeasurableSpace S] [MeasurableSingletonClass S] (M : EpisodicMDP S A)
    (hr : ∀ h s a, M.reward h s a ∈ Set.Icc (0 : ℝ) 1) (H K : ℕ) (hH : 0 < H) (s₀ : S) :
    ∫ ω, ∑ k ∈ Finset.range K, (M.optValue H 0 s₀ - M.value (M.ucbviPolicyAt H
        (Real.log (2 * (H * Fintype.card S * Fintype.card A * K) / (1 / 2))) s₀
        (EpisodicMDP.tapeSamples ω) k) H 0 s₀) ∂M.tapeLaw H K ≤
      20 * H ^ 2 * Fintype.card S * Real.sqrt (Fintype.card A * K *
          Real.log (2 * (H * Fintype.card S * Fintype.card A * K) / (1 / 2))) +
        2 * H ^ 2 * Fintype.card S * Fintype.card A + 2 * (1 / 2) * K * H :=
  M.regret_ucbvi_le' hr hH s₀ (by norm_num) (by norm_num)
