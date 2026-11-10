module

public import Rlib.MDP.InfiniteHorizon
public import Rlib.MDP.TrajectoryMeasure
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Expected infinite discounted returns under the canonical trajectory law -/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped Topology

namespace Rlib.MDP

variable {S A : Type*} [Fintype S] [Fintype A]
  [MeasurableSpace S] [MeasurableSpace A]
  [MeasurableSingletonClass S] [MeasurableSingletonClass A]

private theorem measurable_discountedReturn_prefix (m : MDP S A) (γ : ℝ) (n : ℕ) (s : S) :
    Measurable (fun ω : InfiniteTrajectory S A => m.discountedReturn γ n s (ω.prefix n)) := by
  have hpref : Measurable (InfiniteTrajectory.prefix (S := S) (A := A) n) :=
    measurable_pi_iff.mpr fun i => measurable_pi_apply (i : ℕ)
  exact (measurable_of_finite (m.discountedReturn γ n s)).comp hpref

private theorem integral_discountedReturn_prefix (m : MDP S A) (π : StationaryPolicy S A)
    (γ : ℝ) (s : S) (n : ℕ) :
    (∫ ω, m.discountedReturn γ n s (ω.prefix n) ∂m.pathMeasure π s) =
      m.expectedReturn π γ n s := by
  have hpref : Measurable (InfiniteTrajectory.prefix (S := S) (A := A) n) :=
    measurable_pi_iff.mpr fun i => measurable_pi_apply (i : ℕ)
  have hret : Measurable (m.discountedReturn γ n s) := measurable_of_finite _
  rw [← integral_map (μ := m.pathMeasure π s)
    (f := m.discountedReturn γ n s) hpref.aemeasurable hret.aestronglyMeasurable,
    map_prefix_pathMeasure, integral_toMeasure_eq_expect]
  rfl

private theorem aestronglyMeasurable_infiniteReturn (m : MDP S A)
    {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (s : S)
    (μ : Measure (InfiniteTrajectory S A)) : AEStronglyMeasurable (m.infiniteReturn γ s) μ := by
  exact aestronglyMeasurable_of_tendsto_ae Filter.atTop
    (fun n => (measurable_discountedReturn_prefix m γ n s).aestronglyMeasurable)
    (Filter.Eventually.of_forall (m.tendsto_discountedReturn hγ0 hγ1 s))

/-- Infinite discounted returns are integrable under the canonical trajectory probability law. -/
theorem integrable_infiniteReturn (m : MDP S A) (π : StationaryPolicy S A)
    {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (s : S) :
    Integrable (m.infiniteReturn γ s) (m.pathMeasure π s) := by
  exact (integrable_const (‖m.reward‖ / (1 - γ))).mono'
    (aestronglyMeasurable_infiniteReturn m hγ0 hγ1 s _)
    (Filter.Eventually.of_forall (m.norm_infiniteReturn_le hγ0 hγ1 s))

/-- The expected infinite sum of stored rewards equals the policy's Bellman value. -/
theorem integral_infiniteReturn_eq_policyValue (m : MDP S A) (π : StationaryPolicy S A)
    {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (s : S) :
    (∫ ω, m.infiniteReturn γ s ω ∂m.pathMeasure π s) = m.policyValue π hγ0 hγ1 s := by
  have hlim := tendsto_integral_of_dominated_convergence
    (μ := m.pathMeasure π s) (fun _ => ‖m.reward‖ / (1 - γ))
    (fun n => (measurable_discountedReturn_prefix m γ n s).aestronglyMeasurable)
    (integrable_const _)
    (fun n => Filter.Eventually.of_forall fun ω =>
      m.norm_discountedReturn_le hγ0 hγ1 n s (ω.prefix n))
    (Filter.Eventually.of_forall (m.tendsto_discountedReturn hγ0 hγ1 s))
  simp only [integral_discountedReturn_prefix] at hlim
  exact tendsto_nhds_unique hlim ((tendsto_pi_nhds.mp (m.tendsto_expectedReturn π hγ0 hγ1)) s)

end Rlib.MDP
