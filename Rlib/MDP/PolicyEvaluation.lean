module

public import Rlib.MDP.OneStep
public import Mathlib.Topology.MetricSpace.Contracting

/-! # Contraction and fixed points for policy evaluation -/

@[expose] public section

namespace Rlib.MDP

variable {S A : Type*}

/-- A discount in `[0, 1)` makes the fixed-policy operator a contraction. -/
theorem oneStepValue_contractingWith [Fintype S] [Fintype A] (m : MDP S A)
    (π : StationaryPolicy S A) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) :
    ContractingWith ⟨γ, hγ0⟩ (m.oneStepValue π γ) := by
  refine ⟨hγ1, LipschitzWith.of_dist_le_mul fun v w => ?_⟩
  change ‖m.oneStepValue π γ v - m.oneStepValue π γ w‖ ≤ γ * ‖v - w‖
  simpa only [Real.norm_of_nonneg hγ0] using
    m.norm_oneStepValue_sub_le π γ v w

/-- A discount in `[0, 1)` gives a unique solution of the fixed-policy Bellman equation. -/
theorem existsUnique_oneStepValue_fixedPoint [Fintype S] [Fintype A] (m : MDP S A)
    (π : StationaryPolicy S A) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) :
    ∃! v : S → ℝ, m.oneStepValue π γ v = v := by
  have h := m.oneStepValue_contractingWith π hγ0 hγ1
  exact ⟨h.fixedPoint _, h.fixedPoint_isFixedPt, fun _ hv => h.fixedPoint_unique hv⟩

end Rlib.MDP
