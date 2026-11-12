module

import Rlib

open Rlib MeasureTheory ProbabilityTheory
open scoped ENNReal

private noncomputable def fair : PMF Bool :=
  PMF.ofFintype (fun _ => (1 / 2 : ℝ≥0∞)) (by
    rw [Fintype.sum_bool, one_div, ← two_mul, ENNReal.mul_inv_cancel] <;> norm_num)

private noncomputable def μ : Measure (Fin 4 → Bool) :=
  Measure.pi (fun _ => fair.toMeasure)

private instance : IsProbabilityMeasure μ := by unfold μ; infer_instance

private noncomputable def reward (b : Bool) : ℝ :=
  ({true} : Set Bool).indicator (fun _ => 1) b

private noncomputable def population : MDP Bool Unit where
  reward _ _ := 1 / 2
  transition _ _ := fair

private noncomputable def observations (ω : Fin 4 → Bool) (_ : Bool) (_ : Unit)
    (i : Fin 4) : ℝ × Bool := (reward (ω i), ω i)

private theorem independent_coordinates : iIndepFun (fun (i : Fin 4) (ω : Fin 4 → Bool) => ω i) μ :=
  iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)

private theorem coordinate_law (i : Fin 4) :
    μ.map (fun ω => ω i) = fair.toMeasure :=
  (measurePreserving_eval (fun _ : Fin 4 => fair.toMeasure) i).map_eq

private theorem reward_measurable : Measurable reward :=
  measurable_const.indicator (measurableSet_singleton true)

private theorem reward_mean (i : Fin 4) : ∫ ω, reward (ω i) ∂μ = 1 / 2 := by
  rw [← integral_map (measurable_pi_apply i).aemeasurable reward_measurable.aestronglyMeasurable,
    coordinate_law]
  unfold reward
  rw [integral_indicator_const (1 : ℝ) (measurableSet_singleton true), smul_eq_mul,
    mul_one, measureReal_def, PMF.toMeasure_apply_singleton fair true (measurableSet_singleton true)]
  norm_num [fair, PMF.ofFintype_apply]

private noncomputable def sample (b : Bool) : ℝ × Bool := (reward b, b)

private theorem sample_measurable : Measurable sample := measurable_of_countable _

private def q : Bool → Unit → ℝ := fun s _ => if s then 1 else 0

example : μ.real {ω | (1 / 2 : ℝ) ≤
    ‖(MDP.ofSamples (observations ω)).qBellmanOperator (1 / 2) q -
      population.qBellmanOperator (1 / 2) q‖} ≤
      Fintype.card Bool * Fintype.card Unit *
        (2 * Real.exp (-((3 + 1 : ℝ) * (1 / 2) ^ 2) / (2 * (1 + 1 / 2 * ‖q‖) ^ 2))) := by
  refine MDP.measure_norm_ofSamples_qBellmanOperator_sub_le population observations
    (by norm_num) one_pos q (fun s a => ?_) (fun s a i => ?_) (fun s a i => ?_)
    (fun s a i => reward_mean i) (fun s a i => coordinate_law i) (by norm_num)
  · exact independent_coordinates.comp (fun _ => sample) (fun _ => sample_measurable)
  · exact sample_measurable.comp_aemeasurable (measurable_pi_apply i).aemeasurable
  · refine ae_of_all μ fun ω => ?_
    change |reward (ω i)| ≤ 1
    cases h : ω i <;> norm_num [reward, h]
