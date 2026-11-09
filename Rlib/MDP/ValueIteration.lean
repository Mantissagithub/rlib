module

public import Rlib.MDP.Optimality

/-! # Value iteration for the Bellman optimality operator -/

@[expose] public section

open scoped Topology

namespace Rlib.MDP

variable {S A : Type*}

/-- Apply the Bellman optimality operator `n` times to an initial value function. -/
noncomputable def valueIteration [Fintype S] [Fintype A] [Nonempty A]
    (m : MDP S A) (γ : ℝ) (v₀ : S → ℝ) (n : ℕ) : S → ℝ :=
  (m.optimalityOperator γ)^[n] v₀

/-- Value iteration starts at the supplied initial value function. -/
@[simp]
theorem valueIteration_zero [Fintype S] [Fintype A] [Nonempty A]
    (m : MDP S A) (γ : ℝ) (v₀ : S → ℝ) : m.valueIteration γ v₀ 0 = v₀ := by
  rfl

/-- Each step applies the Bellman optimality operator to the previous iterate. -/
theorem valueIteration_succ [Fintype S] [Fintype A] [Nonempty A]
    (m : MDP S A) (γ : ℝ) (v₀ : S → ℝ) (n : ℕ) :
    m.valueIteration γ v₀ (n + 1) = m.optimalityOperator γ (m.valueIteration γ v₀ n) := by
  exact Function.iterate_succ_apply' (m.optimalityOperator γ) n v₀

/-- The error to any Bellman fixed point is bounded by a power of the discount norm. -/
theorem norm_valueIteration_sub_le [Fintype S] [Fintype A] [Nonempty A]
    (m : MDP S A) (γ : ℝ) (v₀ v : S → ℝ) (hv : m.optimalityOperator γ v = v)
    (n : ℕ) : ‖m.valueIteration γ v₀ n - v‖ ≤ ‖γ‖ ^ n * ‖v₀ - v‖ := by
  have h : LipschitzWith ⟨‖γ‖, norm_nonneg γ⟩ (m.optimalityOperator γ) :=
    LipschitzWith.of_dist_le_mul fun w z => m.norm_optimalityOperator_sub_le γ w z
  have hbound := (h.iterate n).dist_le_mul v₀ v
  change ‖(m.optimalityOperator γ)^[n] v₀ - (m.optimalityOperator γ)^[n] v‖ ≤
    ‖γ‖ ^ n * ‖v₀ - v‖ at hbound
  simpa only [valueIteration, Function.iterate_fixed hv] using hbound

/-- With discount in `[0, 1)`, every initial value function converges to a Bellman fixed point. -/
theorem tendsto_valueIteration [Fintype S] [Fintype A] [Nonempty A]
    (m : MDP S A) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (v₀ v : S → ℝ) (hv : m.optimalityOperator γ v = v) :
    Filter.Tendsto (m.valueIteration γ v₀) Filter.atTop (𝓝 v) := by
  have h := m.optimalityOperator_contractingWith hγ0 hγ1
  rw [h.fixedPoint_unique hv]
  exact h.tendsto_iterate_fixedPoint v₀

/-- A discount in `[0, 1)` gives a unique Bellman fixed point attracting all initial values. -/
theorem existsUnique_valueIteration_limit [Fintype S] [Fintype A] [Nonempty A]
    (m : MDP S A) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) :
    ∃! v : S → ℝ, m.optimalityOperator γ v = v ∧
      ∀ v₀ : S → ℝ, Filter.Tendsto (m.valueIteration γ v₀) Filter.atTop (𝓝 v) := by
  obtain ⟨v, hv, hunique⟩ := m.existsUnique_optimalityOperator_fixedPoint hγ0 hγ1
  exact ⟨v, ⟨hv, fun v₀ => m.tendsto_valueIteration hγ0 hγ1 v₀ v hv⟩,
    fun w hw => hunique w hw.1⟩

end Rlib.MDP
