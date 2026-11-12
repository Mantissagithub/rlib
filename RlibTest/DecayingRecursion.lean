module

import Rlib

open Rlib Filter Topology

private noncomputable def x : ℕ → ℝ
  | 0 => 5
  | n + 1 => (1 - 1 / 2) * x n + 1 / 2 * (1 / ((n : ℝ) + 1))

private theorem x_nonneg (n : ℕ) : 0 ≤ x n := by
  induction n with
  | zero => norm_num [x]
  | succ n ih =>
    rw [x]
    positivity

example : Tendsto x atTop (𝓝 0) :=
  tendsto_zero_of_le_one_sub_mul_add (a := fun _ => 1 / 2) x_nonneg (fun _ => by norm_num)
    (fun _ => by norm_num) (by rw [summable_const_iff]; norm_num)
    (by simpa using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)) (fun n => le_of_eq rfl)

private noncomputable def W : ℕ → ℝ
  | 0 => 3
  | n + 1 => (1 - 1 / 2) * W n + 1 / 2 * (-1 / 2) ^ n

example : Tendsto W atTop (𝓝 0) :=
  tendsto_zero_of_eq_one_sub_mul_add_of_tendsto_sum (a := fun _ => 1 / 2)
    (w := fun n => (-1 / 2) ^ n)
    (fun _ => by norm_num) (fun _ => by norm_num) (by rw [summable_const_iff]; norm_num)
    ((summable_geometric_of_abs_lt_one (by norm_num [abs_of_neg])).mul_left
      (1 / 2)).hasSum.tendsto_sum_nat
    (fun _ => rfl)
