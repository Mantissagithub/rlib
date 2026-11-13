module

import Rlib

open Rlib

private noncomputable def model : MDP Unit Bool where
  transition _ _ := PMF.pure ()
  reward _ a := if a then 1 else 0

private theorem value_best : model.policyValue (fun _ => PMF.pure true)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) = fun _ => 2 := by
  symm
  apply MDP.eq_policyValue_of_fixedPoint
  funext s
  simp only [MDP.oneStepValue, MDP.oneStepActionValue, model, expect_pure]
  norm_num

/-- Agarwal et al., Theorem 10: exact softmax policy gradient with `η = (1 - γ) ^ 3 / 8` reaches
the optimal value `2` of the two-action example in the limit. -/
example : model.pgLimitValue (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) (fun _ => 1)
    ((1 - 1 / 2) ^ 3 / 8) (fun _ _ => 0) () = 2 := by
  have hr : ∀ s a, model.reward s a ∈ Set.Icc (0 : ℝ) 1 := fun _ a => by
    cases a <;> norm_num [model]
  apply le_antisymm
  · refine ciSup_le fun t => ?_
    refine model.policyValue_le_of_oneStepActionValue_le _ (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num) (v := fun _ => 2) (fun s a => ?_) ()
    cases a <;> norm_num [MDP.oneStepActionValue, model, expect_pure]
  · have h := model.policyValue_le_pgLimitValue (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
      hr (fun _ => one_pos) (by simp) (by norm_num) le_rfl (fun _ _ => 0)
      (fun _ => PMF.pure true) ()
    rwa [value_best] at h
