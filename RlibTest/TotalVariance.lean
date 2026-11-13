module

import Rlib

open Rlib

private noncomputable def fair : PMF Bool :=
  PMF.ofFintype (fun _ => ENNReal.ofReal (1 / 2)) (by
    rw [Fintype.sum_bool]
    norm_num [← ENNReal.ofReal_add])

/-- A two-state chain that moves to a fair coin flip and pays one in state `true`. -/
private noncomputable def model : MDP Bool Unit where
  transition _ _ := fair
  reward s _ := if s then 1 else 0

/-- Agarwal, Jiang, Kakade, and Sun, Lemma 2.12, for the only policy of the chain. -/
example (π : StationaryPolicy Bool Unit) (s : Bool) :
    (model.withReward fun s a => Real.sqrt (model.transitionVar
      (model.policyValue π (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)) s a)
      ).policyActionValue π (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) s () ≤
      Real.sqrt (2 / (1 - 1 / 2) ^ 3) :=
  model.policyActionValue_withReward_sqrt_transitionVar_le_two π (by norm_num) (by norm_num)
    (fun s _ => by cases s <;> norm_num [model]) s ()

/-- The total variance bound `1 / (1 - γ) ^ 2 = 4` for the same chain. -/
example (π : StationaryPolicy Bool Unit) (s : Bool) :
    (model.withReward (model.transitionVar
      (model.policyValue π (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)))
      ).policyActionValue π (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) s () ≤ 4 := by
  have h := model.policyActionValue_withReward_transitionVar_le π
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) (fun s _ => by cases s <;> norm_num [model]) s ()
  norm_num at h
  exact h
