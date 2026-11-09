module

import Rlib

example : Rlib.Examples.oneState.valueIteration (1 / 2) (fun _ => 0) 2 () = 3 := by
  norm_num [Rlib.MDP.valueIteration_succ, Rlib.MDP.valueIteration_zero,
    Rlib.MDP.optimalityOperator, Rlib.MDP.oneStepActionValue, Rlib.Examples.oneState]
