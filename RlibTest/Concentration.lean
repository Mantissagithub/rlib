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

example : μ.real {ω | (1 / 2 : ℝ) ≤
    |(MDP.ofSamples (observations ω)).reward false () - (1 / 2 : ℝ)|} ≤
    2 * Real.exp (-2) := by
  have h := MDP.measure_abs_ofSamples_reward_sub_le population observations false ()
    (independent_coordinates.comp (fun _ => reward) (fun _ => reward_measurable))
    (fun i => reward_measurable.comp_aemeasurable (measurable_pi_apply i).aemeasurable)
    (fun i => ae_of_all μ (fun ω => by
      change reward (ω i) ∈ Set.Icc (0 : ℝ) 1
      cases h : ω i <;> norm_num [reward, h]))
    (fun i => reward_mean i) (ε := 1 / 2) (by norm_num)
  norm_num [population] at h ⊢
  exact h

example : μ.real {ω | (1 / 2 : ℝ) ≤
    |((MDP.ofSamples (observations ω)).transition false () true).toReal -
      (1 / 2 : ℝ)|} ≤ 2 * Real.exp (-2) := by
  have h := MDP.measure_abs_ofSamples_transition_sub_le population observations false () true
    independent_coordinates (fun i => (measurable_pi_apply i).aemeasurable)
    coordinate_law (ε := 1 / 2) (by norm_num)
  norm_num [population, fair, PMF.ofFintype_apply] at h ⊢
  exact h

example : 2 * Real.exp (-2) < 1 := by
  rw [Real.exp_neg, ← div_eq_mul_inv]
  apply (div_lt_iff₀ (Real.exp_pos 2)).2
  have h := Real.add_one_le_exp (2 : ℝ)
  linarith
