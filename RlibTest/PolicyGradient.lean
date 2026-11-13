module

import Rlib

open Rlib Filter Topology

private noncomputable def σ (t : ℝ) : ℝ := Real.exp t / (Real.exp t + 1)

private theorem σ_pos (t : ℝ) : 0 < σ t := by
  unfold σ
  positivity

private theorem σ_lt_one (t : ℝ) : σ t < 1 := by
  unfold σ
  rw [div_lt_one (by positivity)]
  linarith

private theorem σ_zero : σ 0 = 1 / 2 := by
  norm_num [σ]

private theorem hasDerivAt_σ : HasDerivAt σ (1 / 4) 0 := by
  have h := (Real.hasDerivAt_exp 0).div ((Real.hasDerivAt_exp 0).add_const 1)
    (by positivity : Real.exp 0 + 1 ≠ 0)
  convert h using 1
  · funext t
    simp [σ]
  · norm_num

private noncomputable def policy (t : ℝ) : StationaryPolicy Unit Bool := fun _ =>
  PMF.ofFintype (fun b => ENNReal.ofReal (if b then σ t else 1 - σ t)) (by
    rw [Fintype.sum_bool]
    simp only [↓reduceIte, Bool.false_eq_true]
    rw [← ENNReal.ofReal_add (σ_pos t).le (by linarith [σ_lt_one t])]
    simp)

private theorem policy_apply (t : ℝ) (s : Unit) (b : Bool) :
    (policy t s b).toReal = if b then σ t else 1 - σ t := by
  simp only [policy, PMF.ofFintype_apply]
  split_ifs
  · exact ENNReal.toReal_ofReal (σ_pos t).le
  · exact ENNReal.toReal_ofReal (by linarith [σ_lt_one t])

private noncomputable def model : MDP Unit Bool where
  transition _ _ := PMF.pure ()
  reward _ a := if a then 2 else 0

private theorem value_zero :
    model.policyValue (policy 0) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) = fun _ => 2 := by
  symm
  apply MDP.eq_policyValue_of_fixedPoint
  funext s
  simp only [MDP.oneStepValue, MDP.oneStepActionValue, expect, Fintype.sum_bool, policy_apply,
    σ_zero, model]
  norm_num

private theorem visit_one :
    model.discountedVisitation (policy 0) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) () () =
      1 := by
  simpa using model.sum_discountedVisitation (policy 0)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) ()

example : HasDerivAt (fun t => model.policyValue (policy t)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) ()) 1 0 := by
  have h := model.hasDerivAt_policyValue policy (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    (fun _ b => if b then 1 / 4 else -(1 / 4)) (fun s b => by
      simp only [policy_apply]
      cases b
      · simpa using hasDerivAt_σ.const_sub 1
      · simpa using hasDerivAt_σ) ()
  convert h using 1
  simp only [Fintype.univ_unit, Finset.sum_singleton, visit_one, one_mul, Fintype.sum_bool,
    MDP.advantage, MDP.policyActionValue, value_zero]
  simp only [MDP.oneStepActionValue, model, expect_pure]
  norm_num
