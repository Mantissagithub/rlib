module

import Rlib

open Rlib

private def observations : Fin 3 → ℝ × Bool := ![(-2, false), (1, false), (4, true)]

private def rows (s a : Bool) : Fin 3 → ℝ × Bool :=
  if s then
    if a then fun _ => (8, true) else fun _ => (5, false)
  else
    if a then fun _ => (-3, true) else observations

private noncomputable def estimated : MDP Bool Bool := MDP.ofSamples rows

example : estimated.reward false false = 1 := by
  norm_num [estimated, MDP.ofSamples, rows, sampleMean, observations, Fin.sum_univ_succ]

example : (estimated.transition false false false).toReal = 2 / 3 := by
  change ((empiricalPMF (fun i => (rows false false i).2)) false).toReal = _
  rw [empiricalPMF_apply_toReal]
  simp only [sampleMean, Fin.sum_univ_succ]
  norm_num [rows, observations]

example : (estimated.transition false false true).toReal = 1 / 3 := by
  change ((empiricalPMF (fun i => (rows false false i).2)) true).toReal = _
  rw [empiricalPMF_apply_toReal]
  simp only [sampleMean, Fin.sum_univ_succ]
  norm_num [rows, observations]

example : estimated.oneStepActionValue (1 / 2) (fun s => if s then 6 else 3)
    false false = 3 := by
  rw [estimated, MDP.oneStepActionValue_ofSamples]
  simp only [sampleMean, Fin.sum_univ_succ]
  norm_num [rows, observations]

example : estimated.reward false true = -3 := by
  simp [estimated, MDP.ofSamples, rows]

example : estimated.reward true false = 5 := by
  simp [estimated, MDP.ofSamples, rows]

example : estimated.reward true true = 8 := by
  simp [estimated, MDP.ofSamples, rows]

example : (estimated.transition false true true).toReal = 1 := by
  change ((empiricalPMF (fun i => (rows false true i).2)) true).toReal = _
  rw [empiricalPMF_apply_toReal]
  simp [rows]

example : (estimated.transition true false true).toReal = 0 := by
  change ((empiricalPMF (fun i => (rows true false i).2)) true).toReal = _
  rw [empiricalPMF_apply_toReal]
  simp [rows]

example : (estimated.transition true true true).toReal = 1 := by
  change ((empiricalPMF (fun i => (rows true true i).2)) true).toReal = _
  rw [empiricalPMF_apply_toReal]
  simp [rows]

example : sampleMean (fun _ : Fin 1 => (-7 : ℝ)) = -7 := by simp

open scoped Classical in
example (x : Fin 3 → ℕ) (t : ℕ) :
    ((empiricalPMF x) t).toReal = sampleMean (fun i => if x i = t then 1 else 0) := by
  rw [empiricalPMF_apply_toReal]
  congr 1
  funext i
  split_ifs <;> rfl

example : (MDP.ofSamples (fun s a (_ : Fin 1) => (-((s + a : ℕ) : ℝ), s))).reward 2 3 = -5 := by
  norm_num [MDP.ofSamples]
