module

import Rlib

open Rlib
open scoped Topology

private def constantPath : InfiniteTrajectory Unit Unit := fun _ => ((), ())

example : Examples.oneState.infiniteReturn (1 / 2) () constantPath = 4 := by
  simp only [MDP.infiniteReturn, Examples.oneState, tsum_mul_right]
  rw [tsum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)]
  norm_num

example (m : MDP Bool Unit) (s : Bool) (ω : InfiniteTrajectory Bool Unit) :
    m.infiniteReturn 0 s ω = m.reward s (ω 0).1 := by
  simp [MDP.infiniteReturn, InfiniteTrajectory.stateBefore, zero_pow_eq]

private noncomputable def changing : MDP Bool Unit where
  transition _ _ := PMF.pure true
  reward s _ := if s then 3 else 1

private def changingPath : InfiniteTrajectory Bool Unit := fun _ => ((), true)

example : changing.discountedReturn (1 / 2) 2 false (changingPath.prefix 2) = 5 / 2 := by
  norm_num [MDP.discountedReturn, InfiniteTrajectory.prefix, changingPath, changing, Fin.tail]

example : changing.infiniteReturn (1 / 2) false changingPath = 4 := by
  have hs := (changing.summable_norm_discountedReward (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num) false changingPath).of_norm
  rw [MDP.infiniteReturn, hs.tsum_eq_zero_add]
  simp only [InfiniteTrajectory.stateBefore, changingPath, changing, Bool.false_eq_true,
    ↓reduceIte, pow_zero, one_mul, pow_succ, mul_assoc, tsum_mul_right]
  rw [tsum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)]
  norm_num

example : Filter.Tendsto (Examples.oneState.expectedReturn Examples.stay (1 / 2))
    Filter.atTop (𝓝 (fun _ => (4 : ℝ))) := by
  have hv : Examples.oneState.policyValue Examples.stay
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) = fun _ => 4 := by
    symm
    apply MDP.eq_policyValue_of_fixedPoint
    funext s
    norm_num [MDP.oneStepValue, MDP.oneStepActionValue, Examples.oneState, Examples.stay]
  simpa only [hv] using Examples.oneState.tendsto_expectedReturn Examples.stay
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
