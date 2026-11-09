module

import Rlib

open Rlib

example : Examples.oneState.expectedReturn Examples.stay (1 / 2) 2 () = 3 := by
  norm_num [MDP.expectedReturn_succ, MDP.expectedReturn_zero, MDP.oneStepValue,
    MDP.oneStepActionValue, Examples.oneState, Examples.stay]

private noncomputable def nextState : PMF Bool :=
  PMF.ofFintype (fun s => ENNReal.ofReal (if s then 1 / 4 else 3 / 4)) (by
    rw [Fintype.sum_bool]
    norm_num [← ENNReal.ofReal_add])

private noncomputable def stochastic : MDP Bool Unit where
  transition _ _ := nextState
  reward s _ := if s then 4 else 0

private noncomputable def onlyAction : StationaryPolicy Bool Unit := fun _ => PMF.pure ()

example : stochastic.expectedReturn onlyAction (1 / 2) 2 false = 1 / 2 := by
  norm_num [MDP.expectedReturn_succ, MDP.expectedReturn_zero, MDP.oneStepValue,
    MDP.oneStepActionValue, stochastic, onlyAction, nextState, expect, Fintype.sum_bool]

example : stochastic.trajectoryLaw onlyAction 2 false
    (Fin.cons ((), true) (Fin.cons ((), false) Fin.elim0)) = 3 / 16 := by
  simp only [MDP.trajectoryLaw, onlyAction, stochastic, PMF.pure_bind, PMF.map,
    Function.comp_apply, PMF.bind_bind]
  norm_num [nextState, PMF.bind_apply, tsum_fintype, PMF.pure_apply,
    ← ENNReal.ofReal_mul, Fin.cons_inj]
  norm_num [ENNReal.ofReal_div_of_pos]

private noncomputable def stateDependent : MDP Bool Unit where
  transition s _ := if s then PMF.pure false else nextState
  reward s _ := if s then 4 else 0

example : stateDependent.trajectoryLaw onlyAction 2 false
    (Fin.cons ((), true) (Fin.cons ((), false) Fin.elim0)) = 1 / 4 := by
  simp only [MDP.trajectoryLaw, onlyAction, stateDependent, PMF.pure_bind, PMF.map,
    Function.comp_apply, PMF.bind_bind]
  norm_num [nextState, PMF.bind_apply, tsum_fintype, PMF.pure_apply,
    ← ENNReal.ofReal_mul, Fin.cons_inj]
  norm_num [ENNReal.ofReal_div_of_pos]
