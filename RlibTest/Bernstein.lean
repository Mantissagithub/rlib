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

private theorem independent_coordinates :
    iIndepFun (fun (i : Fin 4) (ω : Fin 4 → Bool) => ω i) μ :=
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
    mul_one, measureReal_def,
    PMF.toMeasure_apply_singleton fair true (measurableSet_singleton true)]
  norm_num [fair, PMF.ofFintype_apply]

private theorem reward_coord_meas (i : Fin 4) :
    AEMeasurable (fun ω : Fin 4 → Bool => reward (ω i)) μ :=
  reward_measurable.comp_aemeasurable (measurable_pi_apply i).aemeasurable

private theorem reward_dev (b : Bool) : (reward b - 1 / 2) ^ 2 = 1 / 4 := by
  cases b <;> norm_num [reward]

/-- Bernstein's inequality for four fair coins: the sample mean is at least `1 / 2` away from
`1 / 2` with probability at most `2 * exp (-3 / 2)`. -/
example : μ.real {ω | (1 / 2 : ℝ) ≤ |sampleMean (fun i => reward (ω i)) - 1 / 2|} ≤
    2 * Real.exp (-3 / 2) := by
  have h := measure_abs_sampleMean_sub_le_bernstein (n := 3) (X := fun i ω => reward (ω i))
    (independent_coordinates.comp (fun _ => reward) (fun _ => reward_measurable))
    reward_coord_meas
    (M := 1 / 2) (σ2 := 1 / 4) (θ := 1 / 2) (by norm_num) (by norm_num)
    (fun (i : Fin 4) => ae_of_all μ fun ω => by cases ω i <;> norm_num [reward])
    reward_mean
    (fun (i : Fin 4) => by simp only [reward_dev, integral_const]; simp)
    (ε := 1 / 2) (by norm_num)
  convert h using 3
  norm_num
