module

import Rlib

open Rlib

private noncomputable def model : MDP Unit Bool where
  transition _ _ := PMF.pure ()
  reward _ a := if a then 1 else 0

private theorem softmax_zero (s : Unit) (b : Bool) :
    (softmaxPolicy (fun _ _ => (0 : ℝ)) s b).toReal = 1 / 2 := by
  rw [softmaxPolicy_apply]
  norm_num [Fintype.sum_bool]

private theorem value_zero : model.policyValue (softmaxPolicy fun _ _ => (0 : ℝ))
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) = fun _ => 1 := by
  symm
  apply MDP.eq_policyValue_of_fixedPoint
  funext s
  simp only [MDP.oneStepValue, MDP.oneStepActionValue, expect, Fintype.sum_bool, softmax_zero,
    model]
  norm_num

private theorem visit_one : model.discountedVisitation (softmaxPolicy fun _ _ => (0 : ℝ))
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) () () = 1 := by
  simpa using model.sum_discountedVisitation (softmaxPolicy fun _ _ => (0 : ℝ))
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) ()

/-- A step of size `1 / 100` toward the rewarding action strictly raises the value above `1`. -/
example : 1 < model.policyValue (softmaxPolicy fun _ a => if a then (1 / 100 : ℝ) else 0)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) () := by
  have h := model.policyValue_softmax_line_ge (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    (K := 1) (fun _ a => by cases a <;> norm_num [model]) (fun _ _ => 0)
    (fun _ a => if a then 1 else 0) (fun _ a => by cases a <;> norm_num) ()
    (t := 1 / 100) (by norm_num)
  have hgain : model.directionalGain (softmaxPolicy fun _ _ => (0 : ℝ))
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) (fun _ a => if a then 1 else 0) () =
      1 / 4 := by
    simp only [MDP.directionalGain, Fintype.univ_unit, Finset.sum_singleton, Fintype.sum_bool,
      softmax_zero, MDP.advantage, MDP.policyActionValue]
    rw [visit_one, value_zero]
    simp only [MDP.oneStepActionValue, model, expect_pure]
    norm_num
  rw [hgain, value_zero] at h
  norm_num at h
  linarith
