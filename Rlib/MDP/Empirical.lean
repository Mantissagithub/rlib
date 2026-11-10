module

public import Rlib.MDP.Basic
public import Rlib.Probability.Empirical

/-! # MDP estimates from paired reward and successor observations -/

@[expose] public section

noncomputable section

namespace Rlib.MDP

variable {S A : Type*} {n : ℕ}

/-- Estimate each row from nonempty paired observations, storing the observed reward mean. -/
def ofSamples (rows : S → A → Fin (n + 1) → ℝ × S) : MDP S A where
  reward s a := sampleMean (fun i => (rows s a i).1)
  transition s a := empiricalPMF (fun i => (rows s a i).2)

/-- An empirical action value is the mean of the observed one-step targets. -/
theorem oneStepActionValue_ofSamples [Fintype S]
    (rows : S → A → Fin (n + 1) → ℝ × S) (γ : ℝ) (v : S → ℝ) (s : S) (a : A) :
    (ofSamples rows).oneStepActionValue γ v s a =
      sampleMean (fun i => (rows s a i).1 + γ * v (rows s a i).2) := by
  simp [oneStepActionValue, ofSamples, expect_empiricalPMF, sampleMean_add, sampleMean_mul]

end Rlib.MDP
