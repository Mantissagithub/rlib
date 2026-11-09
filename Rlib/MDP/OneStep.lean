module

public import Rlib.MDP.Basic

/-! # Monotonicity and sup-norm bounds for one-step values -/

@[expose] public section

namespace Rlib.MDP

variable {S A : Type*}

/-- A nonnegative discount makes the action value monotone in its continuation value. -/
theorem oneStepActionValue_mono [Fintype S] (m : MDP S A)
    {γ : ℝ} (hγ : 0 ≤ γ) {v w : S → ℝ} (h : v ≤ w) (s : S) (a : A) :
    m.oneStepActionValue γ v s a ≤ m.oneStepActionValue γ w s a := by
  unfold oneStepActionValue
  exact add_le_add_right (mul_le_mul_of_nonneg_left (expect_mono _ h) hγ) _

/-- A nonnegative discount makes the policy value monotone in its continuation value. -/
theorem oneStepValue_mono [Fintype S] [Fintype A] (m : MDP S A)
    (π : StationaryPolicy S A) {γ : ℝ} (hγ : 0 ≤ γ) {v w : S → ℝ} (h : v ≤ w) :
    m.oneStepValue π γ v ≤ m.oneStepValue π γ w := by
  intro s
  exact expect_mono (π s) (m.oneStepActionValue_mono hγ h s)

/-- The action value changes by at most the discount norm times the continuation distance. -/
theorem norm_oneStepActionValue_sub_le [Fintype S] (m : MDP S A)
    (γ : ℝ) (v w : S → ℝ) (s : S) (a : A) :
    ‖m.oneStepActionValue γ v s a - m.oneStepActionValue γ w s a‖ ≤ ‖γ‖ * ‖v - w‖ := by
  calc
    ‖m.oneStepActionValue γ v s a - m.oneStepActionValue γ w s a‖ =
        ‖γ‖ * ‖expect (m.transition s a) v - expect (m.transition s a) w‖ := by
      rw [oneStepActionValue, oneStepActionValue, add_sub_add_left_eq_sub, ← mul_sub, norm_mul]
    _ ≤ ‖γ‖ * ‖v - w‖ :=
      mul_le_mul_of_nonneg_left (norm_expect_sub_expect_le _ v w) (norm_nonneg γ)

/-- The policy operator changes by at most the discount norm times the continuation distance. -/
theorem norm_oneStepValue_sub_le [Fintype S] [Fintype A] (m : MDP S A)
    (π : StationaryPolicy S A) (γ : ℝ) (v w : S → ℝ) :
    ‖m.oneStepValue π γ v - m.oneStepValue π γ w‖ ≤ ‖γ‖ * ‖v - w‖ := by
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (norm_nonneg γ) (norm_nonneg (v - w)))).2
  intro s
  apply (norm_expect_sub_expect_le (π s) _ _).trans
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (norm_nonneg γ) (norm_nonneg (v - w)))).2
  intro a
  exact m.norm_oneStepActionValue_sub_le γ v w s a

end Rlib.MDP
