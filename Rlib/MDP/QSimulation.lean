module

public import Rlib.MDP.QLearning

/-! # Comparing Bellman Q fixed points of two models -/

@[expose] public section

noncomputable section

namespace Rlib.MDP

variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty A]

/-- **Simulation lemma for action values.** For a discount in `[0, 1)`, the Bellman Q fixed
points of two models on the same states and actions differ by at most the gap between the two
Bellman Q operators at one of the fixed points, divided by `1 - γ`. -/
theorem norm_sub_le_of_qBellmanOperator_fixed (m m' : MDP S A) {γ : ℝ} (hγ0 : 0 ≤ γ)
    (hγ1 : γ < 1) {q q' : S → A → ℝ} (hq : m.qBellmanOperator γ q = q)
    (hq' : m'.qBellmanOperator γ q' = q') :
    ‖q' - q‖ ≤ ‖m'.qBellmanOperator γ q - m.qBellmanOperator γ q‖ / (1 - γ) := by
  rw [le_div_iff₀ (sub_pos.mpr hγ1)]
  have hcontract := m'.norm_qBellmanOperator_sub_le γ q' q
  rw [Real.norm_of_nonneg hγ0, hq'] at hcontract
  have hsplit : q' - q = (q' - m'.qBellmanOperator γ q) +
      (m'.qBellmanOperator γ q - m.qBellmanOperator γ q) := by
    rw [hq]
    abel
  have htri := norm_add_le (q' - m'.qBellmanOperator γ q)
    (m'.qBellmanOperator γ q - m.qBellmanOperator γ q)
  rw [← hsplit] at htri
  linarith
end Rlib.MDP
