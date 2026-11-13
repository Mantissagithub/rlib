module

import Rlib

open Rlib

private def rewards : Fin 4 → ℝ := ![1, 0, 0, 1]

private theorem rewards_mean : sampleMean rewards = 1 / 2 := by
  simp [sampleMean, rewards, Fin.sum_univ_succ]; norm_num

private theorem rewards_std : groupStd rewards = 1 / 2 := by
  rw [groupStd, rewards_mean, show (sampleMean fun i => (rewards i - 1 / 2) ^ 2) = (1 / 2) ^ 2 by
    simp [sampleMean, rewards, Fin.sum_univ_succ]; norm_num]
  exact Real.sqrt_sq (by norm_num)

example : groupAdvantage rewards 0 = 1 := by
  rw [groupAdvantage, rewards_mean, rewards_std]
  norm_num [rewards]

example : groupAdvantage rewards 1 = -1 := by
  rw [groupAdvantage, rewards_mean, rewards_std]
  norm_num [rewards]

example : groupAdvantage (fun i => 2 * rewards i + 1) 0 = 1 := by
  rw [groupAdvantage_affine rewards (by norm_num : (0 : ℝ) < 2), groupAdvantage, rewards_mean,
    rewards_std]
  norm_num [rewards]

example : sampleMean (fun i => groupAdvantage rewards i ^ 2) = 1 :=
  sampleMean_groupAdvantage_sq rewards (by rw [rewards_std]; norm_num)

example (β : ℝ) : grpoObjective (1 / 5) β (fun _ => 1) (fun _ => 1) rewards = 0 :=
  grpoObjective_one (by norm_num) β rewards

example : 0 < klEstimator 2 := by
  refine lt_of_le_of_ne (klEstimator_nonneg (by norm_num)) fun h => ?_
  have := (klEstimator_eq_zero_iff (by norm_num : (0 : ℝ) < 2)).1 h.symm
  norm_num at this
