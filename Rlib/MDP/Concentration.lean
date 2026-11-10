module

public import Rlib.MDP.Empirical
public import Rlib.Probability.Concentration

/-! # Pointwise concentration of empirical MDP estimates

These bounds assume independent samples at the specified state and action. They do not assert
independence of samples from a policy trajectory. Rewards and successors within a pair may depend
on each other. Reward concentration requires normalized observations in `[0,1]`.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Rlib.MDP

variable {Ω S A : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n : ℕ}

/-- The empirical reward at one state and action concentrates around its population mean. -/
theorem measure_abs_ofSamples_reward_sub_le (m : MDP S A)
    (D : Ω → S → A → Fin (n + 1) → ℝ × S) (s : S) (a : A)
    (hindep : iIndepFun (fun i ω => (D ω s a i).1) μ)
    (hmeas : ∀ i, AEMeasurable (fun ω => (D ω s a i).1) μ)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, (D ω s a i).1 ∈ Set.Icc (0 : ℝ) 1)
    (hmean : ∀ i, ∫ ω, (D ω s a i).1 ∂μ = m.reward s a)
    {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ |(ofSamples (D ω)).reward s a - m.reward s a|} ≤
      2 * Real.exp (-2 * (n + 1 : ℝ) * ε ^ 2) :=
  measure_abs_sampleMean_sub_le hindep hmeas hbound hmean hε

omit [IsProbabilityMeasure μ] in
private theorem integral_singleton_of_map_eq [MeasurableSpace S] [MeasurableSingletonClass S]
    {Y : Ω → S} (hY : AEMeasurable Y μ) (p : PMF S)
    (hlaw : μ.map Y = p.toMeasure) (t : S) :
    ∫ ω, ({t} : Set S).indicator (fun _ => (1 : ℝ)) (Y ω) ∂μ = (p t).toReal := by
  rw [← integral_map hY ((measurable_const.indicator (measurableSet_singleton t)).aestronglyMeasurable),
    hlaw, integral_indicator_const (1 : ℝ) (measurableSet_singleton t), smul_eq_mul,
    mul_one, measureReal_def,
    PMF.toMeasure_apply_singleton p t (measurableSet_singleton t)]

/-- Each real empirical transition mass concentrates around its population probability.
No finite state or action type is required. -/
theorem measure_abs_ofSamples_transition_sub_le [MeasurableSpace S]
    [MeasurableSingletonClass S] (m : MDP S A)
    (D : Ω → S → A → Fin (n + 1) → ℝ × S) (s : S) (a : A) (t : S)
    (hindep : iIndepFun (fun i ω => (D ω s a i).2) μ)
    (hmeas : ∀ i, AEMeasurable (fun ω => (D ω s a i).2) μ)
    (hlaw : ∀ i, μ.map (fun ω => (D ω s a i).2) = (m.transition s a).toMeasure)
    {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ |((ofSamples (D ω)).transition s a t).toReal -
      (m.transition s a t).toReal|} ≤
      2 * Real.exp (-2 * (n + 1 : ℝ) * ε ^ 2) := by
  classical
  let f : S → ℝ := ({t} : Set S).indicator (fun _ => 1)
  have hf : Measurable f := measurable_const.indicator (measurableSet_singleton t)
  have h := measure_abs_sampleMean_sub_le (hindep.comp (fun _ => f) (fun _ => hf))
    (fun i => hf.comp_aemeasurable (hmeas i))
    (fun i => ae_of_all μ (fun ω => by
      simp only [Function.comp_def, f, Set.indicator_apply, Set.mem_singleton_iff]
      split_ifs <;> norm_num))
    (fun i => integral_singleton_of_map_eq (hmeas i) (m.transition s a) (hlaw i) t) hε
  simpa only [ofSamples, empiricalPMF_apply_toReal, Function.comp_def, f,
    Set.indicator_apply, Set.mem_singleton_iff] using h

end Rlib.MDP
