module

import Rlib

open Rlib

private noncomputable def coin : PMF Bool :=
  PMF.ofFintype (fun _ => ENNReal.ofReal (1 / 2)) (by
    rw [Fintype.sum_bool]
    norm_num [← ENNReal.ofReal_add])

private noncomputable def model : MDP Unit Bool where
  transition _ _ := PMF.pure ()
  reward _ a := if a then 2 else 0

private noncomputable def uniform : StationaryPolicy Unit Bool := fun _ => coin

private theorem value_eq :
    model.policyValue uniform (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) = fun _ => 2 := by
  symm
  apply MDP.eq_policyValue_of_fixedPoint
  funext s
  norm_num [MDP.oneStepValue, MDP.oneStepActionValue, model, uniform, coin, expect,
    Fintype.sum_bool, PMF.ofFintype_apply]

private theorem advantage_true :
    model.advantage uniform (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) () true = 1 := by
  simp only [MDP.advantage, MDP.policyActionValue, value_eq]
  norm_num [MDP.oneStepActionValue, model]

example (V : Unit → ℝ) (t : FiniteTrajectory Unit Bool 1) :
    model.generalizedAdvantage V (1 / 2) (1 / 2) 1 () t =
      model.discountedReturn (1 / 2) 1 () t + (1 / 2) ^ 1 * V (MDP.finalState 1 () t) - V () :=
  model.generalizedAdvantage_one V (1 / 2) 1 () t

example (V : Unit → ℝ) (t : FiniteTrajectory Unit Bool 3) :
    model.generalizedAdvantage V (1 / 2) 0 3 () t = model.tdError V (1 / 2) () (t 0).1 (t 0).2 :=
  model.generalizedAdvantage_zero V (1 / 2) 2 () t

example : expect (model.transition () true) (fun s' => expect (model.trajectoryLaw uniform 3 s')
    fun t => model.generalizedAdvantage (model.policyValue uniform
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)) (1 / 2) (1 / 4) (3 + 1) ()
        (Fin.cons (true, s') t)) = 1 := by
  rw [MDP.expect_generalizedAdvantage_action]
  exact advantage_true
