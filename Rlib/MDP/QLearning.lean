module

public import Rlib.MDP.Empirical
public import Rlib.MDP.Optimality

/-! # Tabular Q-learning updates and the Bellman operator on action values -/

@[expose] public section

noncomputable section

namespace Rlib

variable {S A : Type*}

/-- The largest action value at a state, over all available actions. -/
def qMax [Fintype A] [Nonempty A] (q : S → A → ℝ) (s : S) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (q s)

/-- The target from an observed reward and successor state. -/
def qLearningTarget [Fintype A] [Nonempty A] (γ : ℝ) (q : S → A → ℝ)
    (observation : ℝ × S) : ℝ :=
  observation.1 + γ * qMax q observation.2

/-- Update the visited state and action by a step toward the sampled target. -/
def qLearningUpdate [Fintype A] [Nonempty A] [DecidableEq S] [DecidableEq A]
    (α γ : ℝ) (q : S → A → ℝ) (s : S) (a : A) (observation : ℝ × S) : S → A → ℝ :=
  fun t b => Function.update (Function.uncurry q) (s, a)
    (q s a + α * (qLearningTarget γ q observation - q s a)) (t, b)

/-- The updated entry moves by the step size times the target error. -/
@[simp] theorem qLearningUpdate_apply_same
    [Fintype A] [Nonempty A] [DecidableEq S] [DecidableEq A]
    (α γ : ℝ) (q : S → A → ℝ) (s : S) (a : A) (observation : ℝ × S) :
    qLearningUpdate α γ q s a observation s a =
      q s a + α * (qLearningTarget γ q observation - q s a) := by
  simp [qLearningUpdate]

/-- An update leaves any other state-action entry unchanged. -/
theorem qLearningUpdate_apply_ne [Fintype A] [Nonempty A] [DecidableEq S] [DecidableEq A]
    (α γ : ℝ) (q : S → A → ℝ) (s t : S) (a b : A) (observation : ℝ × S)
    (hne : (t, b) ≠ (s, a)) :
    qLearningUpdate α γ q s a observation t b = q t b := by
  simp [qLearningUpdate, hne]

/-- Taking the maximum over actions is nonexpansive in the sup norm. -/
theorem norm_qMax_sub_le [Fintype S] [Fintype A] [Nonempty A]
    (q p : S → A → ℝ) : ‖qMax q - qMax p‖ ≤ ‖q - p‖ := by
  have upper (q p : S → A → ℝ) (s : S) : qMax q s ≤ qMax p s + ‖q - p‖ := by
    apply Finset.sup'_le
    intro a ha
    have hd := (norm_le_pi_norm ((q - p) s) a).trans (norm_le_pi_norm (q - p) s)
    change ‖q s a - p s a‖ ≤ ‖q - p‖ at hd
    have hp : p s a ≤ qMax p s := Finset.le_sup' _ ha
    have hd' := (abs_le.mp (Real.norm_eq_abs _ ▸ hd)).2
    linarith
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg (q - p))).2
  intro s
  change ‖qMax q s - qMax p s‖ ≤ ‖q - p‖
  rw [Real.norm_eq_abs]
  have hqp := upper q p s
  have hpq := upper p q s
  rw [norm_sub_rev p q] at hpq
  exact abs_le.mpr ⟨by linarith, by linarith⟩

namespace MDP

/-- The Bellman optimality operator on action values. -/
def qBellmanOperator [Fintype S] [Fintype A] [Nonempty A]
    (m : MDP S A) (γ : ℝ) (q : S → A → ℝ) : S → A → ℝ :=
  m.oneStepActionValue γ (qMax q)

/-- Sampling a successor with the stored mean reward gives the Bellman target in expectation. -/
theorem expect_qLearningTarget [Fintype S] [Fintype A] [Nonempty A]
    (m : MDP S A) (γ : ℝ) (q : S → A → ℝ) (s : S) (a : A) :
    expect (m.transition s a) (fun t => qLearningTarget γ q (m.reward s a, t)) =
      m.qBellmanOperator γ q s a := by
  simp [qLearningTarget, qBellmanOperator, oneStepActionValue, expect_add, expect_mul]

/-- The empirical Bellman Q operator averages the observed targets. -/
theorem qBellmanOperator_ofSamples [Fintype S] [Fintype A] [Nonempty A] {n : ℕ}
    (rows : S → A → Fin (n + 1) → ℝ × S) (γ : ℝ) (q : S → A → ℝ) (s : S) (a : A) :
    (ofSamples rows).qBellmanOperator γ q s a =
      sampleMean (fun i => qLearningTarget γ q (rows s a i)) :=
  oneStepActionValue_ofSamples rows γ (qMax q) s a

/-- Maximizing the action-value update gives the state-value Bellman update. -/
theorem qMax_qBellmanOperator [Fintype S] [Fintype A] [Nonempty A]
    (m : MDP S A) (γ : ℝ) (q : S → A → ℝ) :
    qMax (m.qBellmanOperator γ q) = m.optimalityOperator γ (qMax q) :=
  rfl

/-- The Bellman Q operator changes by at most the discount norm times the sup-norm distance. -/
theorem norm_qBellmanOperator_sub_le [Fintype S] [Fintype A] [Nonempty A]
    (m : MDP S A) (γ : ℝ) (q p : S → A → ℝ) :
    ‖m.qBellmanOperator γ q - m.qBellmanOperator γ p‖ ≤ ‖γ‖ * ‖q - p‖ := by
  have hnonneg : 0 ≤ ‖γ‖ * ‖q - p‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  apply (pi_norm_le_iff_of_nonneg hnonneg).2
  intro s
  apply (pi_norm_le_iff_of_nonneg hnonneg).2
  intro a
  exact (m.norm_oneStepActionValue_sub_le γ (qMax q) (qMax p) s a).trans
    (mul_le_mul_of_nonneg_left (norm_qMax_sub_le q p) (norm_nonneg γ))

/-- A discount in `[0, 1)` makes the Bellman Q operator a contraction. -/
theorem qBellmanOperator_contractingWith [Fintype S] [Fintype A] [Nonempty A]
    (m : MDP S A) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) :
    ContractingWith ⟨γ, hγ0⟩ (m.qBellmanOperator γ) := by
  refine ⟨hγ1, LipschitzWith.of_dist_le_mul fun q p => ?_⟩
  change ‖m.qBellmanOperator γ q - m.qBellmanOperator γ p‖ ≤ γ * ‖q - p‖
  simpa only [Real.norm_of_nonneg hγ0] using m.norm_qBellmanOperator_sub_le γ q p

/-- A discount in `[0, 1)` gives a unique fixed point of the Bellman Q operator. -/
theorem existsUnique_qBellmanOperator_fixedPoint [Fintype S] [Fintype A] [Nonempty A]
    (m : MDP S A) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) :
    ∃! q : S → A → ℝ, m.qBellmanOperator γ q = q := by
  have h := m.qBellmanOperator_contractingWith hγ0 hγ1
  exact ⟨h.fixedPoint _, h.fixedPoint_isFixedPt, fun _ hq => h.fixedPoint_unique hq⟩

end MDP
end Rlib
