module

import Rlib

open Rlib

private def q : Bool → Bool → ℝ :=
  fun s a => if s then (if a then -4 else -8) else (if a then -3 else -6)

example : qLearningUpdate (1 / 2) (1 / 2) q false false (-1, true) false false = -9 / 2 := by
  norm_num [qLearningTarget, qMax, q]

example : qLearningUpdate (1 / 2) (1 / 2) q false false (-1, true) false true = -3 := by
  rw [qLearningUpdate_apply_ne _ _ _ _ _ _ _ _ (by decide)]
  simp [q]

example : qLearningUpdate (1 / 2) (1 / 2) q false false (-1, true) true false = -8 := by
  rw [qLearningUpdate_apply_ne _ _ _ _ _ _ _ _ (by decide)]
  simp [q]
