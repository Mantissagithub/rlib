module

import Rlib

private noncomputable def negativeRewards : Rlib.MDP Unit Bool :=
  { transition := fun _ _ => PMF.pure ()
    reward := fun _ a => if a then -1 else -2 }

private theorem negativeRewards_value (a : Bool) :
    negativeRewards.policyValue (fun _ => PMF.pure a)
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) =
    fun _ => if a then -2 else -4 := by
  symm
  apply negativeRewards.eq_policyValue_of_fixedPoint
  funext s
  cases a <;> norm_num [Rlib.MDP.oneStepValue, Rlib.MDP.oneStepActionValue, negativeRewards]

private theorem negativeRewards_greedy (v : Unit → ℝ) :
    negativeRewards.greedyPolicy (1 / 2) v = fun _ => true := by
  funext s
  have h := congrFun (negativeRewards.oneStepValue_greedyPolicy (1 / 2) v) s
  have hmax : negativeRewards.oneStepActionValue (1 / 2) v s true ≤
      negativeRewards.optimalityOperator (1 / 2) v s :=
    Finset.le_sup' _ (Finset.mem_univ true)
  cases ha : negativeRewards.greedyPolicy (1 / 2) v s with
  | false =>
    rw [← h] at hmax
    simp only [Rlib.MDP.oneStepValue, Rlib.expect_pure, ha] at hmax
    norm_num [Rlib.MDP.oneStepActionValue, negativeRewards] at hmax
    linarith
  | true => rfl

example : negativeRewards.policyValue
    (fun s => PMF.pure (negativeRewards.policyIteration
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) (fun _ => false) 0 s))
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) = fun _ => -4 := by
  simpa using negativeRewards_value false

example : negativeRewards.policyIteration
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) (fun _ => false) 1 =
    fun _ => true := by
  rw [Rlib.MDP.policyIteration_succ]
  exact negativeRewards_greedy _

example : negativeRewards.policyValue
    (fun s => PMF.pure (negativeRewards.policyIteration
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) (fun _ => false) 1 s))
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) = fun _ => -2 := by
  rw [Rlib.MDP.policyIteration_succ, negativeRewards_greedy]
  exact negativeRewards_value true

example (k : ℕ) : negativeRewards.policyIteration
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) (fun _ => false) (k + 1) =
    fun _ => true := by
  rw [Rlib.MDP.policyIteration_succ]
  exact negativeRewards_greedy _

private noncomputable def tiedRewards : Rlib.MDP Unit Bool :=
  { transition := fun _ _ => PMF.pure ()
    reward := fun _ _ => -1 }

private theorem tiedRewards_value (p : Unit → Bool) :
    tiedRewards.policyValue (fun s => PMF.pure (p s))
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) = fun _ => -2 := by
  symm
  apply tiedRewards.eq_policyValue_of_fixedPoint
  funext s
  norm_num [Rlib.MDP.oneStepValue, Rlib.MDP.oneStepActionValue, tiedRewards]

example : tiedRewards.policyIteration
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) (fun _ => false) 2 =
    tiedRewards.policyIteration (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num) (fun _ => false) 1 := by
  apply tiedRewards.policyIteration_stable_of_value_eq
  rw [tiedRewards_value, tiedRewards_value]
