module

import Rlib

open Rlib

private noncomputable def model (top : ℝ) : MDP Unit Bool where
  transition _ _ := PMF.pure ()
  reward _ a := if a then top else 0

private def qStar (top : ℝ) : Unit → Bool → ℝ := fun _ a => if a then 2 * top else top

private theorem qStar_fixed (top : ℝ) (htop : 0 ≤ top) :
    (model top).qBellmanOperator (1 / 2) (qStar top) = qStar top := by
  funext s a
  have hmax : qMax (qStar top) () = 2 * top := by
    apply le_antisymm
    · refine Finset.sup'_le _ _ fun b _ => ?_
      cases b
      · show top ≤ 2 * top
        linarith
      · exact le_rfl
    · exact Finset.le_sup' (qStar top ()) (Finset.mem_univ true)
  cases a
  · simp [MDP.qBellmanOperator, MDP.oneStepActionValue, model, qStar, hmax]
  · simp [MDP.qBellmanOperator, MDP.oneStepActionValue, model, qStar, hmax]
    ring

example : ‖qStar 3 - qStar 2‖ ≤ 2 := by
  have h := MDP.norm_sub_le_of_qBellmanOperator_fixed (model 2) (model 3) (by norm_num)
    (by norm_num) (qStar_fixed 2 (by norm_num)) (qStar_fixed 3 (by norm_num))
  have hgap : ‖(model 3).qBellmanOperator (1 / 2) (qStar 2) -
      (model 2).qBellmanOperator (1 / 2) (qStar 2)‖ ≤ 1 := by
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun s =>
      (pi_norm_le_iff_of_nonneg zero_le_one).2 fun a => ?_
    cases a <;> norm_num [MDP.qBellmanOperator, MDP.oneStepActionValue, model]
  refine h.trans ?_
  linarith [div_le_div_of_nonneg_right hgap (by norm_num : (0 : ℝ) ≤ 1 - 1 / 2)]
