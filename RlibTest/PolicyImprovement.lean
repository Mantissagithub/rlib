module

import Rlib

example : (fun _ : Unit => (-4 : ℝ)) ≤ fun _ => -2 := by
  let m : Rlib.MDP Unit Bool :=
    { transition := fun _ _ => PMF.pure ()
      reward := fun _ a => if a then -1 else -2 }
  let πold : Rlib.StationaryPolicy Unit Bool := fun _ => PMF.pure false
  let πnew : Rlib.StationaryPolicy Unit Bool := fun _ => PMF.pure true
  have hv : m.oneStepValue πold (1 / 2) (fun _ => -4) = fun _ => -4 := by
    funext s
    norm_num [Rlib.MDP.oneStepValue, Rlib.MDP.oneStepActionValue, m, πold]
  have hgreedy : m.oneStepValue πnew (1 / 2) (fun _ => -4) =
      m.optimalityOperator (1 / 2) (fun _ => -4) := by
    funext s
    norm_num [Rlib.MDP.oneStepValue, Rlib.MDP.optimalityOperator,
      Rlib.MDP.oneStepActionValue, m, πnew]
  have hw : m.oneStepValue πnew (1 / 2) (fun _ => -2) = fun _ => -2 := by
    funext s
    norm_num [Rlib.MDP.oneStepValue, Rlib.MDP.oneStepActionValue, m, πnew]
  exact m.policy_improvement πold πnew (by norm_num) (by norm_num)
    (fun _ => -4) (fun _ => -2) hv hgreedy hw
