module

import Rlib

open Rlib

private noncomputable def model : MDP Unit Bool where
  transition _ _ := PMF.pure ()
  reward _ a := if a then 2 else 0

private noncomputable def best : StationaryPolicy Unit Bool := fun _ => PMF.pure true

private theorem value_best :
    model.policyValue best (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) = fun _ => 4 := by
  symm
  apply MDP.eq_policyValue_of_fixedPoint
  funext s
  simp only [MDP.oneStepValue, MDP.oneStepActionValue, best, model, expect_pure]
  norm_num

private theorem value_zero : model.policyValue (softmaxPolicy fun _ _ => (0 : ℝ))
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) = fun _ => 2 := by
  symm
  apply MDP.eq_policyValue_of_fixedPoint
  funext s
  have h (b : Bool) : (softmaxPolicy (fun _ _ => (0 : ℝ)) s b).toReal = 1 / 2 := by
    rw [softmaxPolicy_apply]
    norm_num [Fintype.sum_bool]
  simp only [MDP.oneStepValue, MDP.oneStepActionValue, expect, Fintype.sum_bool, h, model]
  norm_num

/-- One step of natural policy gradient from uniform scores does not lower the value. -/
example : 2 ≤ model.policyValue
    (softmaxPolicy (model.npgScores (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) 1
      (fun _ _ => 0) 1)) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) () := by
  have h := model.policyValue_npg_mono (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    (fun _ _ => 0) one_pos () (Nat.zero_le 1)
  simp only [MDP.npgScores, value_zero] at h
  exact h

/-- After `100` steps with step size one, the gap to the best policy is at most
`(log 2 + 8) / 50`. -/
example : 4 - model.policyValue
    (softmaxPolicy (model.npgScores (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) 1
      (fun _ _ => 0) 100)) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) () ≤
    (Real.log 2 + 8) / 50 := by
  have h := model.policyValue_sub_npg_le_of_abs_reward_le (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num) (R := 2) (fun _ a => by cases a <;> norm_num [model]) one_pos best
    (by norm_num : 0 < 100) ()
  rw [value_best] at h
  convert h using 1
  norm_num
