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

example : model.advantage uniform (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) () true = 1 := by
  simp only [MDP.advantage, MDP.policyActionValue, value_eq]
  norm_num [MDP.oneStepActionValue, model]

example :
    model.advantage uniform (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) () false = -1 := by
  simp only [MDP.advantage, MDP.policyActionValue, value_eq]
  norm_num [MDP.oneStepActionValue, model]

example : expect (uniform ())
    (model.advantage uniform (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) ()) = 0 :=
  model.expect_advantage uniform _ _ ()
