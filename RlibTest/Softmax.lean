module

import Rlib

open Rlib

private noncomputable def model : MDP Unit Bool where
  transition _ _ := PMF.pure ()
  reward _ a := if a then 2 else 0

private theorem softmax_zero (s : Unit) (b : Bool) :
    (softmaxPolicy (fun _ _ => (0 : ℝ)) s b).toReal = 1 / 2 := by
  rw [softmaxPolicy_apply]
  norm_num [Fintype.sum_bool]

private theorem value_zero : model.policyValue (softmaxPolicy fun _ _ => (0 : ℝ))
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) = fun _ => 2 := by
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

example : HasDerivAt (fun t => model.policyValue (softmaxPolicy fun s a =>
    (0 : ℝ) + t * (if s = () ∧ a = true then 1 else 0)) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num) ()) 1 0 := by
  convert model.hasDerivAt_policyValue_softmax_single (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num) (fun _ _ => 0) () () true using 1
  rw [visit_one, softmax_zero]
  simp only [MDP.advantage, MDP.policyActionValue, value_zero]
  simp only [MDP.oneStepActionValue, model, expect_pure]
  norm_num
