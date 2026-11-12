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

example : model.policyValue uniform (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) () ≤
    model.policyValue always (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) () :=
  model.policyValue_le_of_expect_advantage_nonneg uniform always _ _
    (fun s => by cases s; simp only [always, expect_pure]; linarith [advantage_true]) ()

example : model.policyValue always (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) () -
    model.policyValue uniform (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) () = 2 := by
  have h := congrFun (model.policyValue_sub_policyValue uniform always
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)) ()
  rw [Pi.sub_apply] at h
  rw [h]
  have hval : (model.withReward (model.advantage uniform (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num))).policyValue always (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) =
        fun _ => 2 := by
    symm
    apply MDP.eq_policyValue_of_fixedPoint
    funext s
    cases s
    simp only [MDP.oneStepValue, MDP.oneStepActionValue, MDP.withReward, always, expect_pure,
      expect_const]
    linarith [advantage_true]
  rw [hval]
