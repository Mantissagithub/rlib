module

public import Rlib.MDP.QLearning
public import Rlib.Analysis.DecayingRecursion

/-! # Synchronous Q iterations with decaying step sizes

Every state-action entry is updated at every step. Step sizes may change with the step count,
and each update target may differ from the exact Bellman Q target by a supplied error.
-/

@[expose] public section

noncomputable section

open Filter Topology

namespace Rlib

variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty A]

/-- Synchronous Q-learning: every entry moves toward the target from its own observation. -/
def qLearningSync (α : ℕ → ℝ) (γ : ℝ) (observations : ℕ → S → A → ℝ × S)
    (q₀ : S → A → ℝ) : ℕ → S → A → ℝ
  | 0 => q₀
  | n + 1 => fun s a =>
    qLearningSync α γ observations q₀ n s a +
      α n * (qLearningTarget γ (qLearningSync α γ observations q₀ n) (observations n s a) -
        qLearningSync α γ observations q₀ n s a)

namespace MDP

/-- Mix every entry with its exact Bellman Q target plus the supplied target error. -/
def qSyncIteration (m : MDP S A) (α : ℕ → ℝ) (γ : ℝ) (e : ℕ → S → A → ℝ)
    (q₀ : S → A → ℝ) : ℕ → S → A → ℝ
  | 0 => q₀
  | n + 1 => fun s a =>
    (1 - α n) * m.qSyncIteration α γ e q₀ n s a +
      α n * (m.qBellmanOperator γ (m.qSyncIteration α γ e q₀ n) s a + e n s a)

/-- Synchronous Q-learning is the synchronous Bellman Q iteration with its realized target
errors. -/
theorem qLearningSync_eq_qSyncIteration (m : MDP S A) (α : ℕ → ℝ) (γ : ℝ)
    (observations : ℕ → S → A → ℝ × S) (q₀ : S → A → ℝ) :
    qLearningSync α γ observations q₀ =
      m.qSyncIteration α γ
        (fun n s a => qLearningTarget γ (qLearningSync α γ observations q₀ n)
            (observations n s a) -
          m.qBellmanOperator γ (qLearningSync α γ observations q₀ n) s a) q₀ := by
  funext n
  induction n with
  | zero => rfl
  | succ n ih =>
    funext s a
    simp only [qLearningSync, qSyncIteration, ← ih]
    ring

/-- One synchronous step contracts the distance to a Bellman Q fixed point by
`1 - α n * (1 - γ)`, up to the step size times the target error. -/
theorem norm_qSyncIteration_succ_sub_le (m : MDP S A) {α : ℕ → ℝ} {γ : ℝ}
    (e : ℕ → S → A → ℝ) (q₀ r : S → A → ℝ) (hr : m.qBellmanOperator γ r = r) (n : ℕ)
    (hα0 : 0 ≤ α n) (hα1 : α n ≤ 1) (hγ0 : 0 ≤ γ) :
    ‖m.qSyncIteration α γ e q₀ (n + 1) - r‖ ≤
      (1 - α n * (1 - γ)) * ‖m.qSyncIteration α γ e q₀ n - r‖ + α n * ‖e n‖ := by
  set q := m.qSyncIteration α γ e q₀ n
  have hB : ‖m.qBellmanOperator γ q - r‖ ≤ γ * ‖q - r‖ := by
    have h := m.norm_qBellmanOperator_sub_le γ q r
    rwa [Real.norm_of_nonneg hγ0, hr] at h
  have hnonneg : 0 ≤ (1 - α n * (1 - γ)) * ‖q - r‖ + α n * ‖e n‖ := by
    have : 0 ≤ 1 - α n * (1 - γ) := by nlinarith
    positivity
  apply (pi_norm_le_iff_of_nonneg hnonneg).2
  intro s
  apply (pi_norm_le_iff_of_nonneg hnonneg).2
  intro a
  have hq : ‖q s a - r s a‖ ≤ ‖q - r‖ :=
    (norm_le_pi_norm ((q - r) s) a).trans (norm_le_pi_norm (q - r) s)
  have hBe : ‖m.qBellmanOperator γ q s a - r s a‖ ≤ γ * ‖q - r‖ :=
    ((norm_le_pi_norm ((m.qBellmanOperator γ q - r) s) a).trans
      (norm_le_pi_norm (m.qBellmanOperator γ q - r) s)).trans hB
  have he : ‖e n s a‖ ≤ ‖e n‖ :=
    (norm_le_pi_norm (e n s) a).trans (norm_le_pi_norm (e n) s)
  have hentry : m.qSyncIteration α γ e q₀ (n + 1) s a - r s a =
      (1 - α n) * (q s a - r s a) + α n * (m.qBellmanOperator γ q s a - r s a) +
        α n * e n s a := by
    simp only [qSyncIteration, q]
    ring
  change ‖m.qSyncIteration α γ e q₀ (n + 1) s a - r s a‖ ≤ _
  rw [hentry]
  refine norm_add₃_le.trans ?_
  rw [norm_mul, norm_mul, norm_mul, Real.norm_of_nonneg (sub_nonneg.mpr hα1),
    Real.norm_of_nonneg hα0]
  nlinarith [mul_le_mul_of_nonneg_left hq (sub_nonneg.mpr hα1),
    mul_le_mul_of_nonneg_left hBe hα0, mul_le_mul_of_nonneg_left he hα0]

/-- With step sizes in `[0, 1]` that are not summable and target errors tending to zero,
synchronous Bellman Q iterations converge to the Bellman Q fixed point. -/
theorem tendsto_qSyncIteration (m : MDP S A) {α : ℕ → ℝ} {γ : ℝ}
    (hα0 : ∀ n, 0 ≤ α n) (hα1 : ∀ n, α n ≤ 1) (hαsum : ¬Summable α)
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (e : ℕ → S → A → ℝ)
    (he : Tendsto (fun n => ‖e n‖) atTop (𝓝 0)) (q₀ r : S → A → ℝ)
    (hr : m.qBellmanOperator γ r = r) :
    Tendsto (m.qSyncIteration α γ e q₀) atTop (𝓝 r) := by
  have hγ : 0 < 1 - γ := sub_pos.mpr hγ1
  apply tendsto_iff_norm_sub_tendsto_zero.2
  refine tendsto_zero_of_le_one_sub_mul_add (a := fun n => α n * (1 - γ))
    (d := fun n => ‖e n‖ / (1 - γ)) (fun _ => norm_nonneg _)
    (fun n => mul_nonneg (hα0 n) hγ.le)
    (fun n => by nlinarith [hα0 n, hα1 n])
    (fun h => hαsum ((summable_mul_right_iff hγ.ne').1 h))
    (by simpa using he.div_const (1 - γ)) fun n => ?_
  refine (m.norm_qSyncIteration_succ_sub_le e q₀ r hr n (hα0 n) (hα1 n) hγ0).trans_eq ?_
  field_simp

/-- Synchronous Q-learning converges to the Bellman Q fixed point when its step sizes lie in
`[0, 1]` and are not summable, and its realized target errors tend to zero. -/
theorem tendsto_qLearningSync (m : MDP S A) {α : ℕ → ℝ} {γ : ℝ}
    (hα0 : ∀ n, 0 ≤ α n) (hα1 : ∀ n, α n ≤ 1) (hαsum : ¬Summable α)
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (observations : ℕ → S → A → ℝ × S) (q₀ r : S → A → ℝ)
    (hr : m.qBellmanOperator γ r = r)
    (he : Tendsto (fun n => ‖fun s a =>
        qLearningTarget γ (qLearningSync α γ observations q₀ n) (observations n s a) -
          m.qBellmanOperator γ (qLearningSync α γ observations q₀ n) s a‖) atTop (𝓝 0)) :
    Tendsto (qLearningSync α γ observations q₀) atTop (𝓝 r) := by
  rw [m.qLearningSync_eq_qSyncIteration]
  exact m.tendsto_qSyncIteration hα0 hα1 hαsum hγ0 hγ1 _ he q₀ r hr

end MDP
end Rlib
