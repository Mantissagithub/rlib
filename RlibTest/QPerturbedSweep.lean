module

import Rlib

open Rlib

private noncomputable def model : MDP Unit Bool where
  transition _ _ := PMF.pure ()
  reward _ a := if a then 2 else 0

private def qStar : Unit → Bool → ℝ := fun _ a => if a then 4 else 2

private theorem qStar_fixed : model.qBellmanOperator (1 / 2) qStar = qStar := by
  funext s a
  cases a <;> norm_num [MDP.qBellmanOperator, MDP.oneStepActionValue, model, qStar, qMax]

private noncomputable def visits : List ((Unit × Bool) × ℝ) :=
  [(((), true), 1 / 2), (((), false), -1 / 2)]

example : model.qPerturbedSweep 1 (1 / 2) qStar visits () false = 7 / 4 := by
  norm_num [MDP.qPerturbedSweep, MDP.qPerturbedUpdate, MDP.qBellmanUpdate,
    MDP.qBellmanOperator, MDP.oneStepActionValue, model, qStar, qMax, visits,
    Function.uncurry, Pi.single_apply]

example : ‖model.qPerturbedSweep 1 (1 / 2) qStar visits - qStar‖ ≤ 1 := by
  have h := model.norm_qPerturbedSweep_sub_le (ε := 1 / 2) (by norm_num) le_rfl
    (by norm_num) (by norm_num) (by norm_num) qStar qStar qStar_fixed visits
    (by intro v hv; simp [visits] at hv; rcases hv with rfl | rfl <;> norm_num)
    (by rintro ⟨⟨⟩, b⟩; cases b <;> simp [visits])
  norm_num at h
  exact h
