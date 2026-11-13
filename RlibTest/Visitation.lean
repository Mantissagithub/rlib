module

import Rlib

open Rlib

private noncomputable def chain : MDP Bool Unit where
  transition _ _ := PMF.pure false
  reward _ _ := 0

private noncomputable def only : StationaryPolicy Bool Unit := fun _ => PMF.pure ()

private theorem visit_true :
    chain.discountedVisitation only (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) true true =
      1 / 2 := by
  have h : (chain.withReward fun t _ => if t = true then (1 : ℝ) else 0).policyValue only
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) = fun t => if t = true then 1 else 0 := by
    symm
    apply MDP.eq_policyValue_of_fixedPoint
    funext t
    cases t <;> norm_num [MDP.oneStepValue, MDP.oneStepActionValue, MDP.withReward, chain, only]
  simp only [MDP.discountedVisitation, h]
  norm_num

private theorem visit_false :
    chain.discountedVisitation only (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) true false =
      1 / 2 := by
  have h : (chain.withReward fun t _ => if t = false then (1 : ℝ) else 0).policyValue only
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) = fun t => if t = false then 2 else 1 := by
    symm
    apply MDP.eq_policyValue_of_fixedPoint
    funext t
    cases t <;> norm_num [MDP.oneStepValue, MDP.oneStepActionValue, MDP.withReward, chain, only]
  simp only [MDP.discountedVisitation, h]
  norm_num

example : ∑ s, chain.discountedVisitation only (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    true s = 1 :=
  chain.sum_discountedVisitation only _ _ true

example :
    chain.discountedVisitation only (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) true true +
      chain.discountedVisitation only (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) true false =
        1 := by
  rw [visit_true, visit_false]
  norm_num
