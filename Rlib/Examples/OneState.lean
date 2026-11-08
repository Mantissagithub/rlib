module

public import Rlib.MDP.Basic
public import Mathlib.Tactic.NormNum

/-! # A deterministic one-state example -/

@[expose] public section

namespace Rlib.Examples

/-- The sole action returns to the sole state and pays a reward of two. -/
noncomputable def oneState : MDP Unit Unit where
  transition _ _ := PMF.pure ()
  reward _ _ := 2

/-- The only action is chosen with probability one. -/
noncomputable def stay : StationaryPolicy Unit Unit := fun _ => PMF.pure ()

/-- With discount one half and continuation four, the one-step value is four. -/
theorem oneState_value :
    oneState.oneStepValue stay (1 / 2) (fun _ => 4) () = 4 := by
  norm_num [MDP.oneStepValue, MDP.oneStepActionValue, oneState, stay]

end Rlib.Examples
