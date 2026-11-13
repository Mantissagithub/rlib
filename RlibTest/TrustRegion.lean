module

import Rlib

open Rlib

private noncomputable def coin : PMF Bool :=
  PMF.ofFintype (fun _ => ENNReal.ofReal (1 / 2)) (by
    rw [Fintype.sum_bool]
    norm_num [← ENNReal.ofReal_add])

private noncomputable def steer : MDP Bool Bool where
  transition _ a := PMF.pure a
  reward s _ := if s then 1 else 0

private noncomputable def uniform : StationaryPolicy Bool Bool := fun _ => coin

private noncomputable def always : StationaryPolicy Bool Bool := fun _ => PMF.pure true

private theorem distance (t : Bool) :
    ∑ a, |(always t a).toReal - (uniform t a).toReal| ≤ 1 := by
  norm_num [Fintype.sum_bool, always, uniform, coin, PMF.ofFintype_apply, PMF.pure_apply]

example (s₀ : Bool) :
    ∑ s, |steer.discountedVisitation always (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) s₀ s -
      steer.discountedVisitation uniform (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) s₀ s| ≤
        1 := by
  have h := steer.sum_abs_discountedVisitation_sub_le_of_le uniform always
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) distance s₀
  norm_num at h ⊢
  linarith

example (s₀ : Bool) {ε : ℝ}
    (hε : ∀ s, |expect (always s) (steer.advantage uniform (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num) s)| ≤ ε) :
    steer.surrogate uniform always (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) s₀ - ε ≤
      (1 - 1 / 2) * (steer.policyValue always (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) s₀ -
        steer.policyValue uniform (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) s₀) := by
  have h := steer.surrogate_sub_le uniform always (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    (fun s a _ => by simp [uniform, coin, PMF.ofFintype_apply]) hε distance s₀
  norm_num at h ⊢
  linarith
