module

import Rlib
import Mathlib.Probability.Independence.Basic

open Rlib MeasureTheory ProbabilityTheory Filter Topology

private noncomputable def coin : PMF Bool :=
  PMF.ofFintype (fun _ => ENNReal.ofReal (1 / 2)) (by
    rw [Fintype.sum_bool]
    norm_num [← ENNReal.ofReal_add])

private noncomputable def μ : Measure Bool := coin.toMeasure

private instance : IsProbabilityMeasure μ := by
  unfold μ
  infer_instance

@[instance_reducible]
private def level : ℕ → MeasurableSpace Bool
  | 0 => ⊥
  | _ + 1 => inferInstance

private def ℱ : Filtration ℕ (inferInstance : MeasurableSpace Bool) where
  seq := level
  mono' i j hij := by
    rcases i with _ | i
    · exact bot_le
    · rcases j with _ | j
      · omega
      · exact le_rfl
  le' n := by
    rcases n with _ | n
    · exact bot_le
    · exact le_rfl

private noncomputable def model : MDP Unit Unit where
  transition _ _ := PMF.pure ()
  reward _ _ := 0

private def observe (ω : Bool) (n : ℕ) (_ : Unit) (_ : Unit) : ℝ × Unit :=
  (if n = 0 then (if ω then 1 else -1) else 0, ())

private noncomputable def step (n : ℕ) : ℝ := 1 / ((n : ℝ) + 2)

private theorem step_pos (n : ℕ) : 0 < step n := by
  unfold step
  positivity

private theorem step_le_one (n : ℕ) : step n ≤ 1 := by
  unfold step
  rw [div_le_one (by positivity)]
  linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]

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

private theorem sum_step_sq_le (n : ℕ) :
    ∑ k ∈ Finset.range n, step k ^ 2 ≤ 1 - 1 / ((n : ℝ) + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have h : step n ^ 2 ≤ 1 / ((n : ℝ) + 1) - 1 / ((n : ℝ) + 2) := by
      unfold step
      rw [div_pow, one_pow, show 1 / ((n : ℝ) + 1) - 1 / ((n : ℝ) + 2) =
        1 / (((n : ℝ) + 1) * ((n : ℝ) + 2)) by field_simp; ring]
      apply one_div_le_one_div_of_le (by positivity)
      nlinarith
    rw [show (((n + 1 : ℕ) : ℝ) + 1) = (n : ℝ) + 2 by push_cast; ring]
    linarith

private theorem step_sq_summable : Summable fun n => step n ^ 2 :=
  summable_of_sum_range_le (c := 1) (fun n => sq_nonneg _) fun n =>
    (sum_step_sq_le n).trans (by linarith [show 0 ≤ 1 / ((n : ℝ) + 1) by positivity])

example : ∀ᵐ ω ∂μ,
    Tendsto (qLearningSync step (1 / 2) (observe ω) (fun _ _ => 0)) atTop (𝓝 (fun _ _ => 0)) := by
  refine model.ae_tendsto_qLearningSync_of_indep (ℱ := ℱ) (R := 1) (fun n => (step_pos n).le)
    step_le_one step_not_summable step_sq_summable (by norm_num) (by norm_num) observe
    ?_ ?_ ?_ ?_ ?_ _ _ ?_
  · intro n s a
    change Measurable[⊤] _
    exact measurable_from_top
  · intro n s a
    rcases n with _ | n
    · exact indep_bot_right _
    · have hconst : (fun ω => observe ω (n + 1) s a) = fun _ => ((0 : ℝ), ()) := by
        funext ω
        simp [observe]
      rw [hconst, MeasurableSpace.comap_const]
      exact indep_bot_left _
  · intro n s a
    rcases n with _ | n
    · simp [observe, model, μ, coin, PMF.integral_eq_sum, PMF.ofFintype_apply]
    · simp [observe, model]
  · intro n s a
    have hsnd : (fun ω => (observe ω n s a).2) = fun _ => () := rfl
    rw [hsnd, Measure.map_const, measure_univ, one_smul]
    simp [model, PMF.toMeasure_pure]
  · intro ω n _ _
    unfold observe
    split_ifs <;> norm_num
  · funext s a
    simp [MDP.qBellmanOperator, MDP.oneStepActionValue, model, qMax]
