module

import Rlib

open Rlib MeasureTheory

example : (∫ ω, Examples.oneState.infiniteReturn (1 / 2) () ω
    ∂Examples.oneState.pathMeasure Examples.stay ()) = 4 := by
  have hv : Examples.oneState.policyValue Examples.stay
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) = fun _ => 4 := by
    symm
    apply MDP.eq_policyValue_of_fixedPoint
    funext s
    norm_num [MDP.oneStepValue, MDP.oneStepActionValue, Examples.oneState, Examples.stay]
  rw [MDP.integral_infiniteReturn_eq_policyValue _ _ (by norm_num) (by norm_num), hv]

private noncomputable def nextState : PMF Bool :=
  PMF.ofFintype (fun s => ENNReal.ofReal (if s then 1 / 4 else 3 / 4)) (by
    rw [Fintype.sum_bool]
    norm_num [← ENNReal.ofReal_add])

private noncomputable def stateDependent : MDP Bool Unit where
  transition s _ := if s then PMF.pure false else nextState
  reward s _ := if s then 4 else 0

private noncomputable def onlyAction : StationaryPolicy Bool Unit := fun _ => PMF.pure ()

private theorem stateDependent_value : stateDependent.policyValue onlyAction
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) =
      fun b => if b then (40 / 9 : ℝ) else 8 / 9 := by
  symm
  apply MDP.eq_policyValue_of_fixedPoint
  funext b
  cases b <;> norm_num [MDP.oneStepValue, MDP.oneStepActionValue, stateDependent,
    onlyAction, expect, nextState, Fintype.sum_bool, PMF.pure_apply]

example : (∫ ω, stateDependent.infiniteReturn (1 / 2) false ω
    ∂stateDependent.pathMeasure onlyAction false) = 8 / 9 := by
  rw [MDP.integral_infiniteReturn_eq_policyValue _ _ (by norm_num) (by norm_num),
    stateDependent_value]
  norm_num

example : (∫ ω, stateDependent.infiniteReturn (1 / 2) true ω
    ∂stateDependent.pathMeasure onlyAction true) = 40 / 9 := by
  rw [MDP.integral_infiniteReturn_eq_policyValue _ _ (by norm_num) (by norm_num),
    stateDependent_value]
  norm_num
