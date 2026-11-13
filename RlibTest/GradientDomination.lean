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

private theorem value_best : model.policyValue (fun _ => PMF.pure true)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) = fun _ => 4 := by
  symm
  apply MDP.eq_policyValue_of_fixedPoint
  funext s
  simp only [MDP.oneStepValue, MDP.oneStepActionValue, model, expect_pure]
  norm_num

private theorem visit_one (π : StationaryPolicy Unit Bool) :
    model.weightedVisitation π (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) (fun _ => 1) () =
      1 := by
  simpa [MDP.weightedVisitation] using
    model.sum_discountedVisitation π (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) ()

/-- Gradient domination at the uniform policy: the gap `4 - 2` to the best policy forces the
gradient entry of the rewarding action to be at least one. -/
example : 1 ≤ |model.softmaxGradient (softmaxPolicy fun _ _ => (0 : ℝ))
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) (fun _ => 1) () true| := by
  have h := model.sum_sub_policyValue_le_sum_abs_softmaxGradient
    (softmaxPolicy fun _ _ => (0 : ℝ)) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    (μ := fun _ => 1) (ρ := fun _ => 1) (fun _ => zero_le_one) (fun _ => zero_le_one)
    (fun _ => true) (c := 1 / 2) (C := 1) (by norm_num)
    (fun s => (softmax_zero s true).ge)
    (fun s => by rw [visit_one, visit_one, one_mul])
  simp only [Fintype.univ_unit, Finset.sum_singleton, value_best, value_zero] at h
  linarith
