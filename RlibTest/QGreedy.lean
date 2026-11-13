module

import Rlib

open Rlib

private noncomputable def model : MDP Unit Bool where
  transition _ _ := PMF.pure ()
  reward _ a := if a then 1 else 0

private def qstar : Unit → Bool → ℝ := fun _ a => if a then 2 else 1

private theorem qMax_qstar (s : Unit) : qMax qstar s = 2 := by
  apply le_antisymm
  · exact Finset.sup'_le _ _ fun a _ => by cases a <;> norm_num [qstar]
  · exact le_trans (by norm_num [qstar]) (Finset.le_sup' (qstar s) (Finset.mem_univ true))

private theorem qstar_fixed : model.qBellmanOperator (1 / 2) qstar = qstar := by
  funext s a
  simp only [MDP.qBellmanOperator, MDP.oneStepActionValue]
  cases a <;> norm_num [model, qstar, qMax_qstar]

/-- Agarwal, Jiang, Kakade, and Sun, Lemma 1.11: a table within `1 / 10` of `Q*` has a greedy
policy within `2 / 5` of the optimal value `2`. -/
example (q : Unit → Bool → ℝ) (hq : ‖q - qstar‖ ≤ 1 / 10) :
    2 - 2 / 5 ≤ model.policyValue (MDP.qGreedyPolicy q) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num) () := by
  have h := model.qMax_sub_policyValue_qGreedyPolicy_le (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num) qstar_fixed hq ()
  rw [qMax_qstar] at h
  norm_num at h ⊢
  linarith
