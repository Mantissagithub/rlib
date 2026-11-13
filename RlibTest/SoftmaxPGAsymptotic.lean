module

import Rlib

open Rlib

private noncomputable def model : MDP Unit Bool where
  transition _ _ := PMF.pure ()
  reward _ a := if a then 1 else 0

private theorem value_zero : model.policyValue (softmaxPolicy fun _ _ => (0 : ℝ))
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) = fun _ => 1 := by
  symm
  apply MDP.eq_policyValue_of_fixedPoint
  funext s
  have h (b : Bool) : (softmaxPolicy (fun _ _ => (0 : ℝ)) s b).toReal = 1 / 2 := by
    rw [softmaxPolicy_apply]
    norm_num [Fintype.sum_bool]
  simp only [MDP.oneStepValue, MDP.oneStepActionValue, expect, Fintype.sum_bool, h, model]
  norm_num

/-- Even the large step size `η = 5` never lowers the value. -/
example (t : ℕ) : 1 ≤ model.policyValue (softmaxPolicy (model.pgScores
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) (fun _ => 1) 5 (fun _ _ => 0) t))
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) () := by
  have h := model.monotone_policyValue_pg (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    (μ := fun _ => 1) (fun _ => zero_le_one) (by norm_num : (0 : ℝ) ≤ 5) (fun _ _ => 0) ()
    (Nat.zero_le t)
  simp only [MDP.pgScores, value_zero] at h
  exact h

/-- With Mei et al.'s step size the gradient entry of the rewarding action vanishes. -/
example : Filter.Tendsto (fun t => model.softmaxGradient (softmaxPolicy (model.pgScores
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) (fun _ => 1) ((1 - 1 / 2) ^ 3 / 8)
      (fun _ _ => 0) t)) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) (fun _ => 1) () true)
    Filter.atTop (nhds 0) :=
  model.tendsto_softmaxGradient_pg (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    (fun _ a => by cases a <;> norm_num [model]) (fun _ => zero_le_one) (by simp) (by norm_num)
    le_rfl (fun _ _ => 0) () true

/-- Agarwal et al., Lemma C.11: the advantage of the unrewarding action is `-V / 2 ≤ -1 / 2`
along the iteration, so its score tends to `-∞`. -/
example : Filter.Tendsto (fun t => model.pgScores (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num) (fun _ => 1) ((1 - 1 / 2) ^ 3 / 8) (fun _ _ => 0) t () false)
    Filter.atTop Filter.atBot := by
  refine model.tendsto_pgScores_atBot (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    (fun _ a => by cases a <;> norm_num [model]) (fun _ => zero_le_one) (by simp)
    (by norm_num) (fun _ _ => 0) one_pos (ε := 1 / 2) (by norm_num) (T := 0) fun t _ => ?_
  have h := model.monotone_policyValue_pg (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    (μ := fun _ => 1) (fun _ => zero_le_one) (by norm_num : (0 : ℝ) ≤ (1 - 1 / 2) ^ 3 / 8)
    (fun _ _ => 0) () (Nat.zero_le t)
  simp only [MDP.pgScores, value_zero] at h
  set V := model.policyValue (softmaxPolicy (model.pgScores (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num) (fun _ => 1) ((1 - 1 / 2) ^ 3 / 8) (fun _ _ => 0) t))
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  change model.oneStepActionValue (1 / 2) V () false - V () ≤ -(1 / 2)
  have hq : model.oneStepActionValue (1 / 2) V () false = 1 / 2 * V () := by
    simp only [MDP.oneStepActionValue, model, expect_pure]
    norm_num
  rw [hq]
  linarith
