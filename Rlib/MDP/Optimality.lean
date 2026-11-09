module

public import Rlib.MDP.OneStep
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Topology.MetricSpace.Contracting
public import Mathlib.Tactic.Linarith

/-! # Contraction and fixed points for Bellman optimality -/

@[expose] public section

namespace Rlib.MDP

variable {S A : Type*}

/-- The maximum one-step action value over all available actions. -/
noncomputable def optimalityOperator [Fintype S] [Fintype A] [Nonempty A]
    (m : MDP S A) (γ : ℝ) (v : S → ℝ) (s : S) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (m.oneStepActionValue γ v s)

/-- A nonnegative discount makes the optimality operator monotone. -/
theorem optimalityOperator_mono [Fintype S] [Fintype A] [Nonempty A] (m : MDP S A)
    {γ : ℝ} (hγ : 0 ≤ γ) {v w : S → ℝ} (h : v ≤ w) :
    m.optimalityOperator γ v ≤ m.optimalityOperator γ w := by
  intro s
  exact Finset.sup'_mono_fun fun a _ => m.oneStepActionValue_mono hγ h s a

/-- The optimality operator changes by at most the discount norm times the continuation distance. -/
theorem norm_optimalityOperator_sub_le [Fintype S] [Fintype A] [Nonempty A]
    (m : MDP S A) (γ : ℝ) (v w : S → ℝ) :
    ‖m.optimalityOperator γ v - m.optimalityOperator γ w‖ ≤ ‖γ‖ * ‖v - w‖ := by
  have bound (v w : S → ℝ) (s : S) :
      m.optimalityOperator γ v s ≤ m.optimalityOperator γ w s + ‖γ‖ * ‖v - w‖ := by
    apply Finset.sup'_le
    intro a ha
    have hdiff := m.norm_oneStepActionValue_sub_le γ v w s a
    rw [Real.norm_eq_abs] at hdiff
    have hupper := (abs_le.mp hdiff).2
    have hmax : m.oneStepActionValue γ w s a ≤ m.optimalityOperator γ w s :=
      Finset.le_sup' _ ha
    linarith
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (norm_nonneg γ) (norm_nonneg (v - w)))).2
  intro s
  change ‖m.optimalityOperator γ v s - m.optimalityOperator γ w s‖ ≤ _
  rw [Real.norm_eq_abs]
  apply abs_le.mpr
  have hvw := bound v w s
  have hwv := bound w v s
  rw [norm_sub_rev w v] at hwv
  constructor <;> linarith

/-- A discount in `[0, 1)` makes the optimality operator a contraction. -/
theorem optimalityOperator_contractingWith [Fintype S] [Fintype A] [Nonempty A]
    (m : MDP S A) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) :
    ContractingWith ⟨γ, hγ0⟩ (m.optimalityOperator γ) := by
  refine ⟨hγ1, LipschitzWith.of_dist_le_mul fun v w => ?_⟩
  change ‖m.optimalityOperator γ v - m.optimalityOperator γ w‖ ≤ γ * ‖v - w‖
  simpa only [Real.norm_of_nonneg hγ0] using m.norm_optimalityOperator_sub_le γ v w

/-- A discount in `[0, 1)` gives a unique solution of the Bellman optimality equation. -/
theorem existsUnique_optimalityOperator_fixedPoint [Fintype S] [Fintype A] [Nonempty A]
    (m : MDP S A) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) :
    ∃! v : S → ℝ, m.optimalityOperator γ v = v := by
  have h := m.optimalityOperator_contractingWith hγ0 hγ1
  exact ⟨h.fixedPoint _, h.fixedPoint_isFixedPt, fun _ hv => h.fixedPoint_unique hv⟩

end Rlib.MDP
