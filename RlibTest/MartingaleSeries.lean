module

import Rlib

open Rlib MeasureTheory Filter Topology

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

private def w (n : ℕ) (ω : Bool) : ℝ := if n = 0 then (if ω then 1 else -1) else 0

example (α : ℕ → ℝ) (hα : Summable fun n => α n ^ 2) :
    ∀ᵐ ω ∂μ, ∃ c, Tendsto (fun n => ∑ k ∈ Finset.range n, α k * w k ω) atTop (𝓝 c) := by
  refine ae_tendsto_sum_mul_of_condExp_eq_zero (ℱ := ℱ) (C := 1) ?_ ?_ ?_ hα
  · intro n
    change StronglyMeasurable[⊤] (w n)
    exact measurable_from_top.stronglyMeasurable
  · intro n
    refine Eventually.of_forall fun ω => ?_
    unfold w
    split_ifs <;> norm_num
  · intro n
    rcases n with _ | n
    · change μ[w 0 | ⊥] =ᵐ[μ] 0
      rw [condExp_bot]
      refine Eventually.of_forall fun _ => ?_
      simp [μ, w, coin, PMF.integral_eq_sum, PMF.ofFintype_apply]
    · have hw : w (n + 1) = 0 := by
        funext ω
        simp [w]
      rw [hw, condExp_zero]
