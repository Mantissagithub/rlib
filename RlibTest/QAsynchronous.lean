module

import Rlib

open Rlib Filter Topology

private noncomputable def model : MDP Unit Bool where
  transition _ _ := PMF.pure ()
  reward _ a := if a then 2 else 0

private def qStar : Unit → Bool → ℝ := fun _ a => if a then 4 else 2

private theorem qStar_fixed : model.qBellmanOperator (1 / 2) qStar = qStar := by
  funext s a
  cases a <;> norm_num [MDP.qBellmanOperator, MDP.oneStepActionValue, model, qStar, qMax]

private noncomputable def turns (n : ℕ) (_ : Unit) (a : Bool) : ℝ :=
  if a = decide (n % 2 = 0) then 1 / 2 else 0

private theorem turns_not_summable (s : Unit) (a : Bool) : ¬Summable fun n => turns n s a := by
  intro h
  have hsub : Tendsto (fun k : ℕ => 2 * k + (if a then 0 else 1)) atTop atTop :=
    tendsto_atTop_mono (fun k => by simp only [id]; split_ifs <;> omega) tendsto_id
  have hconst : (fun k : ℕ => turns (2 * k + (if a then 0 else 1)) s a) = fun _ => 1 / 2 := by
    funext k
    cases a <;> simp [turns, Nat.add_mod]
  have hlim := h.tendsto_atTop_zero.comp hsub
  rw [Function.comp_def, hconst] at hlim
  have := tendsto_nhds_unique hlim tendsto_const_nhds
  norm_num at this

example (q₀ : Unit → Bool → ℝ) :
    Tendsto (model.qAsyncIteration turns (1 / 2) (fun _ _ _ => 0) q₀) atTop (𝓝 qStar) := by
  refine model.tendsto_qAsyncIteration (fun n s a => ?_) (fun n s a => ?_) turns_not_summable
    (by norm_num) (by norm_num) _ (fun _ _ => ⟨0, by simp⟩) q₀ qStar qStar_fixed
    ⟨‖q₀ - qStar‖ + ‖qStar‖, fun n => ?_⟩
  · unfold turns
    split_ifs <;> norm_num
  · unfold turns
    split_ifs <;> norm_num
  · have h := model.norm_qAsyncIteration_sub_le (β := turns) (E := 0) (fun n s a => by
      unfold turns; split_ifs <;> norm_num) (fun n s a => by unfold turns; split_ifs <;> norm_num)
      (by norm_num) (by norm_num) (fun _ _ _ => 0) (fun _ => by simp) q₀ qStar qStar_fixed n
    rw [zero_div, max_eq_left (norm_nonneg _)] at h
    calc
      _ = ‖(model.qAsyncIteration turns (1 / 2) (fun _ _ _ => 0) q₀ n - qStar) + qStar‖ := by
        rw [sub_add_cancel]
      _ ≤ _ := (norm_add_le _ _).trans (by linarith)
