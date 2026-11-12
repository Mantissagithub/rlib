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

private noncomputable def step (n : ℕ) : ℝ := 1 / ((n : ℝ) + 2)

private theorem step_pos (n : ℕ) : 0 < step n := by
  unfold step
  positivity

private theorem log_le_sum_step (n : ℕ) :
    Real.log (((n : ℝ) + 2) / 2) ≤ ∑ k ∈ Finset.range n, step k := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hsplit : Real.log ((((n + 1 : ℕ) : ℝ) + 2) / 2) =
        Real.log (((n : ℝ) + 2) / 2) + Real.log (((n : ℝ) + 3) / ((n : ℝ) + 2)) := by
      rw [← Real.log_mul (by positivity) (by positivity)]
      congr 1
      push_cast
      field_simp
      ring
    have hlog : Real.log (((n : ℝ) + 3) / ((n : ℝ) + 2)) ≤ step n := by
      refine (Real.log_le_sub_one_of_pos (by positivity)).trans_eq ?_
      unfold step
      field_simp
      ring
    linarith

private theorem step_not_summable : ¬Summable step := by
  rw [not_summable_iff_tendsto_nat_atTop_of_nonneg fun n => (step_pos n).le]
  refine tendsto_atTop_mono log_le_sum_step (Real.tendsto_log_atTop.comp ?_)
  refine Tendsto.atTop_div_const (by norm_num) ?_
  exact tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop

private def sign (n : ℕ) (_ : Unit) (_ : Bool) : ℝ := (-1) ^ n

example (q₀ : Unit → Bool → ℝ) :
    Tendsto (model.qSyncIteration step (1 / 2) sign q₀) atTop (𝓝 qStar) := by
  refine model.tendsto_qSyncIteration_of_tendsto_sum (fun n => (step_pos n).le)
    (fun n => ?_) step_not_summable (by norm_num) (by norm_num) sign (fun _ _ => ?_) q₀ qStar
    qStar_fixed
  · unfold step
    rw [div_le_one (by positivity)]
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  · have hanti : Antitone step := fun i j hij => by
      unfold step
      gcongr
    have hzero : Tendsto step atTop (𝓝 0) := by
      refine ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
        (tendsto_add_atTop_nat 1)).congr fun n => ?_
      simp only [Function.comp, step]
      push_cast
      ring
    obtain ⟨c, hc⟩ := hanti.tendsto_alternating_series_of_tendsto_zero hzero
    exact ⟨c, by simpa [sign, mul_comm] using hc⟩
