module

public import Rlib.MDP.QSynchronous
public import Rlib.Probability.MartingaleSeries

/-! # Almost sure convergence of sampled synchronous Q-learning

Observations are random. The realized target error of each entry must be known at the next
time and have zero conditional mean given the current time. Deriving that condition from a
sampling model for the observations is left to later work.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology

namespace Rlib.MDP

variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty A]

/-- The gap between the sampled target and the exact Bellman Q target at step `n`. -/
def qLearningSyncError (m : MDP S A) (α : ℕ → ℝ) (γ : ℝ)
    (observations : ℕ → S → A → ℝ × S) (q₀ : S → A → ℝ) (n : ℕ) (s : S) (a : A) : ℝ :=
  qLearningTarget γ (qLearningSync α γ observations q₀ n) (observations n s a) -
    m.qBellmanOperator γ (qLearningSync α γ observations q₀ n) s a

/-- With rewards bounded by `R`, realized target errors are bounded by a constant that depends
only on the model, the discount, the reward bound, and the initial table. -/
theorem abs_qLearningSyncError_le (m : MDP S A) {α : ℕ → ℝ} {γ R : ℝ}
    (hα0 : ∀ n, 0 ≤ α n) (hα1 : ∀ n, α n ≤ 1) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (observations : ℕ → S → A → ℝ × S) (hR : ∀ n s a, |(observations n s a).1| ≤ R)
    (q₀ : S → A → ℝ) (n : ℕ) (s : S) (a : A) :
    |m.qLearningSyncError α γ observations q₀ n s a| ≤
      R + ‖m.qBellmanOperator γ 0‖ + 2 * γ * max ‖q₀‖ (R / (1 - γ)) := by
  set K := max ‖q₀‖ (R / (1 - γ))
  set q := qLearningSync α γ observations q₀ n
  have hq : ‖q‖ ≤ K := norm_qLearningSync_le hα0 hα1 hγ0 hγ1 observations hR q₀ n
  have hmax : |qMax q (observations n s a).2| ≤ K := by
    have := (norm_le_pi_norm (qMax q) (observations n s a).2).trans (norm_qMax_le q)
    rw [Real.norm_eq_abs] at this
    exact this.trans hq
  have htarget : |qLearningTarget γ q (observations n s a)| ≤ R + γ * K := by
    unfold qLearningTarget
    refine (abs_add_le _ _).trans (add_le_add (hR n s a) ?_)
    rw [abs_mul, abs_of_nonneg hγ0]
    exact mul_le_mul_of_nonneg_left hmax hγ0
  have hB : |m.qBellmanOperator γ q s a| ≤ ‖m.qBellmanOperator γ 0‖ + γ * K := by
    have hdiff : ‖m.qBellmanOperator γ q - m.qBellmanOperator γ 0‖ ≤ γ * K := by
      have h := m.norm_qBellmanOperator_sub_le γ q 0
      rw [Real.norm_of_nonneg hγ0, sub_zero] at h
      exact h.trans (mul_le_mul_of_nonneg_left hq hγ0)
    have h := (norm_le_pi_norm (m.qBellmanOperator γ q s) a).trans
      (norm_le_pi_norm (m.qBellmanOperator γ q) s)
    rw [Real.norm_eq_abs] at h
    exact h.trans ((norm_le_insert' _ _).trans (by linarith))
  unfold qLearningSyncError
  refine (abs_sub _ _).trans ?_
  change |qLearningTarget γ q (observations n s a)| + |m.qBellmanOperator γ q s a| ≤ _
  linarith

/-- **Almost sure convergence of synchronous Q-learning.** Suppose rewards are bounded, step
sizes lie in `[0, 1]`, are not summable, and have summable squares, and the discount lies in
`[0, 1)`. If each realized target error is measurable at the next time and has zero conditional
mean given the current time, then synchronous Q-learning converges almost surely to the Bellman
Q fixed point. -/
theorem ae_tendsto_qLearningSync {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {ℱ : Filtration ℕ m0} (m : MDP S A) {α : ℕ → ℝ} {γ R : ℝ}
    (hα0 : ∀ n, 0 ≤ α n) (hα1 : ∀ n, α n ≤ 1) (hαsum : ¬Summable α)
    (hαsq : Summable fun n => α n ^ 2) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (observations : Ω → ℕ → S → A → ℝ × S)
    (hR : ∀ ω n s a, |(observations ω n s a).1| ≤ R) (q₀ r : S → A → ℝ)
    (hr : m.qBellmanOperator γ r = r)
    (hmeas : ∀ n s a,
      StronglyMeasurable[ℱ (n + 1)] fun ω => m.qLearningSyncError α γ (observations ω) q₀ n s a)
    (hmean : ∀ n s a,
      μ[fun ω => m.qLearningSyncError α γ (observations ω) q₀ n s a | ℱ n] =ᵐ[μ] 0) :
    ∀ᵐ ω ∂μ, Tendsto (qLearningSync α γ (observations ω) q₀) atTop (𝓝 r) := by
  have hsums : ∀ᵐ ω ∂μ, ∀ s a, ∃ c, Tendsto (fun n => ∑ k ∈ Finset.range n,
      α k * m.qLearningSyncError α γ (observations ω) q₀ k s a) atTop (𝓝 c) := by
    refine ae_all_iff.2 fun s => ae_all_iff.2 fun a => ?_
    exact ae_tendsto_sum_mul_of_condExp_eq_zero (fun n => hmeas n s a)
      (fun n => Eventually.of_forall fun ω =>
        m.abs_qLearningSyncError_le hα0 hα1 hγ0 hγ1 (observations ω) (hR ω) q₀ n s a)
      (fun n => hmean n s a) hαsq
  filter_upwards [hsums] with ω hω
  rw [m.qLearningSync_eq_qSyncIteration]
  exact m.tendsto_qSyncIteration_of_tendsto_sum hα0 hα1 hαsum hγ0 hγ1 _ hω q₀ r hr

end Rlib.MDP
