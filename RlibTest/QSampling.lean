module

import Rlib

open Rlib

private noncomputable def coin : PMF Bool :=
  PMF.ofFintype (fun _ => ENNReal.ofReal (1 / 2)) (by
    rw [Fintype.sum_bool]
    norm_num [← ENNReal.ofReal_add])

private noncomputable def model : MDP Bool Unit where
  transition _ _ := coin
  reward _ _ := 1

private def q : Bool → Unit → ℝ := fun s _ => if s then 2 else 0

private theorem model_qBellmanOperator :
    model.qBellmanOperator (1 / 2) q false () = 3 / 2 := by
  norm_num [MDP.qBellmanOperator, MDP.oneStepActionValue, model, coin, q, qMax, expect,
    Fintype.sum_bool]

example : ‖qLearningUpdate (1 / 2) (1 / 2) q false () (1, true) -
    model.qBellmanUpdate (1 / 2) (1 / 2) q (false, ())‖ = 1 / 4 := by
  rw [MDP.norm_qLearningUpdate_sub_qBellmanUpdate, model_qBellmanOperator]
  norm_num [qLearningTarget, qMax, q]

example : expect (model.transition false ())
    (fun t => qLearningUpdate (1 / 2) (1 / 2) q false () (model.reward false (), t) false ()) =
      3 / 4 := by
  rw [MDP.expect_qLearningUpdate_apply_same]
  norm_num [MDP.qBellmanUpdate, model_qBellmanOperator, q]
