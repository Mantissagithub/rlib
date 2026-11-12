module

public import Rlib.MDP.QBellmanSweep

/-! # Sampled Q-learning updates compared with exact Bellman updates -/

@[expose] public section

noncomputable section

namespace Rlib.MDP

variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty A]
  [DecidableEq S] [DecidableEq A]

/-- A sampled update differs from the exact Bellman update only at the visited entry,
by the step size times the gap between the sampled and exact targets. -/
theorem qLearningUpdate_sub_qBellmanUpdate (m : MDP S A) (α γ : ℝ) (q : S → A → ℝ)
    (s : S) (a : A) (observation : ℝ × S) :
    qLearningUpdate α γ q s a observation - m.qBellmanUpdate α γ q (s, a) =
      Pi.single s (Pi.single a
        (α * (qLearningTarget γ q observation - m.qBellmanOperator γ q s a))) := by
  funext t b
  by_cases ht : t = s
  · subst t
    by_cases hb : b = a
    · subst b
      simp [qLearningUpdate, qBellmanUpdate]
      ring
    · simp [qLearningUpdate, qBellmanUpdate, hb]
  · simp [qLearningUpdate, qBellmanUpdate, ht]

/-- The sup-norm gap between a sampled update and the exact Bellman update is the step size
norm times the target gap. -/
theorem norm_qLearningUpdate_sub_qBellmanUpdate (m : MDP S A) (α γ : ℝ) (q : S → A → ℝ)
    (s : S) (a : A) (observation : ℝ × S) :
    ‖qLearningUpdate α γ q s a observation - m.qBellmanUpdate α γ q (s, a)‖ =
      ‖α‖ * ‖qLearningTarget γ q observation - m.qBellmanOperator γ q s a‖ := by
  rw [m.qLearningUpdate_sub_qBellmanUpdate, Pi.norm_single, Pi.norm_single, norm_mul]

/-- Sampling a successor with the stored mean reward makes the visited entry of the sampled
update equal the exact Bellman update in expectation. -/
theorem expect_qLearningUpdate_apply_same (m : MDP S A) (α γ : ℝ) (q : S → A → ℝ)
    (s : S) (a : A) :
    expect (m.transition s a)
        (fun t => qLearningUpdate α γ q s a (m.reward s a, t) s a) =
      m.qBellmanUpdate α γ q (s, a) s a := by
  have hmix : (fun t => qLearningUpdate α γ q s a (m.reward s a, t) s a) =
      fun t => (1 - α) * q s a + α * qLearningTarget γ q (m.reward s a, t) := by
    funext t
    rw [qLearningUpdate_apply_same]
    ring
  rw [hmix, expect_add, expect_const, expect_mul, m.expect_qLearningTarget]
  simp [qBellmanUpdate]

end Rlib.MDP
