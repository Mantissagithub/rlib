module

import Rlib

open Rlib

private noncomputable def model : MDP Unit Bool where
  transition _ _ := PMF.pure ()
  reward _ a := if a then 2 else 0

example :
    model.qBellmanSweep 1 (1 / 2) (fun _ _ => 0) [((), true), ((), false)] () false = 1 := by
  norm_num [MDP.qBellmanSweep, MDP.qBellmanUpdate, MDP.qBellmanOperator, MDP.oneStepActionValue,
    model, qMax, Function.uncurry]

example :
    model.qBellmanSweep 1 (1 / 2) (fun _ _ => 0) [((), false), ((), true)] () false = 0 := by
  norm_num [MDP.qBellmanSweep, MDP.qBellmanUpdate, MDP.qBellmanOperator, MDP.oneStepActionValue,
    model, qMax, Function.uncurry]
