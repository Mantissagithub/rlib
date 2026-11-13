module

import Rlib

open Rlib

private noncomputable def coin : PMF Bool :=
  PMF.ofFintype (fun _ => ENNReal.ofReal (1 / 2)) (by
    rw [Fintype.sum_bool]
    norm_num [← ENNReal.ofReal_add])

private noncomputable def model : MDP Unit Bool where
  transition _ _ := PMF.pure ()
  reward _ a := if a then 2 else 0

private noncomputable def uniform : StationaryPolicy Unit Bool := fun _ => coin

private theorem value_eq :
    model.policyValue uniform (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) = fun _ => 2 := by
  symm
  apply MDP.eq_policyValue_of_fixedPoint
  funext s
  norm_num [MDP.oneStepValue, MDP.oneStepActionValue, model, uniform, coin, expect,
    Fintype.sum_bool, PMF.ofFintype_apply]

private noncomputable def always : StationaryPolicy Unit Bool := fun _ => PMF.pure true

private theorem advantage_true :
    model.advantage uniform (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) () true = 1 := by
  simp only [MDP.advantage, MDP.policyActionValue, value_eq]
  norm_num [MDP.oneStepActionValue, model]

example : ppoClip (1 / 5) 2 1 = 6 / 5 := by norm_num [ppoClip]
example : ppoClip (1 / 5) (11 / 10) 1 = 11 / 10 := by norm_num [ppoClip]
example : ppoClip (1 / 5) (1 / 2) (-1) = -4 / 5 := by norm_num [ppoClip]
example : ppoClip (1 / 5) (1 / 2) 1 = 1 / 2 := by norm_num [ppoClip]

private theorem advantage_false :
    model.advantage uniform (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) () false = -1 := by
  simp only [MDP.advantage, MDP.policyActionValue, value_eq]
  norm_num [MDP.oneStepActionValue, model]

private theorem visit_one :
    model.discountedVisitation uniform (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) () () =
      1 := by
  simpa using model.sum_discountedVisitation uniform
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) ()

example : model.surrogate uniform always (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) () =
    1 := by
  rw [MDP.surrogate_eq _ _ _ _ _ (fun s a _ => by simp [uniform, coin, PMF.ofFintype_apply])]
  simp only [Fintype.univ_unit, Finset.sum_singleton, visit_one, one_mul, always, expect_pure]
  exact advantage_true

example : model.clippedSurrogate uniform always (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    (1 / 5) () = 1 / 5 := by
  simp only [MDP.clippedSurrogate, Fintype.univ_unit, Finset.sum_singleton, visit_one, one_mul]
  simp only [expect, Fintype.sum_bool, MDP.policyRatio, advantage_true, advantage_false]
  norm_num [uniform, always, coin, PMF.ofFintype_apply, PMF.pure_apply, ppoClip]
