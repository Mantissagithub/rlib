module

import Rlib

example :
    let m : Rlib.MDP Unit Bool :=
      { transition := fun _ _ => PMF.pure ()
        reward := fun _ a => if a then -1 else -2 }
    m.optimalityOperator 0 (fun _ => 0) () = -1 := by
  norm_num [Rlib.MDP.optimalityOperator, Rlib.MDP.oneStepActionValue]
