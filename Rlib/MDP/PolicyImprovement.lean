module

public import Rlib.MDP.PolicyEvaluation
public import Rlib.MDP.Optimality
public import Mathlib.Topology.Order.OrderClosed

/-! # Greedy policies and policy improvement -/

@[expose] public section

open scoped Topology

namespace Rlib.MDP

variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty A]

/-- Averaging action values under any policy is bounded above by their maximum. -/
theorem oneStepValue_le_optimalityOperator (m : MDP S A) (π : StationaryPolicy S A)
    (γ : ℝ) (v : S → ℝ) : m.oneStepValue π γ v ≤ m.optimalityOperator γ v := by
  intro s
  calc
    m.oneStepValue π γ v s ≤ expect (π s) (fun _ => m.optimalityOperator γ v s) :=
      expect_mono _ fun a => Finset.le_sup' _ (Finset.mem_univ a)
    _ = m.optimalityOperator γ v s := expect_const _ _

/-- A deterministic policy attains the maximum one-step value at every state. -/
theorem exists_deterministic_greedy_policy (m : MDP S A) (γ : ℝ) (v : S → ℝ) :
    ∃ a : S → A,
      m.oneStepValue (fun s => PMF.pure (a s)) γ v = m.optimalityOperator γ v := by
  classical
  have h (s : S) : ∃ a : A, m.optimalityOperator γ v s = m.oneStepActionValue γ v s a := by
    obtain ⟨a, _, ha⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
      (m.oneStepActionValue γ v s)
    exact ⟨a, ha⟩
  choose a ha using h
  refine ⟨a, funext fun s => ?_⟩
  simpa only [oneStepValue, expect_pure] using (ha s).symm

/-- A policy greedy with respect to an old Bellman value has a nondecreasing Bellman value. -/
theorem policy_improvement (m : MDP S A) (πold πnew : StationaryPolicy S A)
    {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (v w : S → ℝ)
    (hv : m.oneStepValue πold γ v = v)
    (hgreedy : m.oneStepValue πnew γ v = m.optimalityOperator γ v)
    (hw : m.oneStepValue πnew γ w = w) : v ≤ w := by
  have hstart : v ≤ m.oneStepValue πnew γ v := by
    calc
      v = m.oneStepValue πold γ v := hv.symm
      _ ≤ m.optimalityOperator γ v := m.oneStepValue_le_optimalityOperator πold γ v
      _ = m.oneStepValue πnew γ v := hgreedy.symm
  have hiter (n : ℕ) : v ≤ (m.oneStepValue πnew γ)^[n] v := by
    induction n with
    | zero => exact le_rfl
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact hstart.trans (m.oneStepValue_mono πnew hγ0 ih)
  have hc := m.oneStepValue_contractingWith πnew hγ0 hγ1
  have ht : Filter.Tendsto (fun n => (m.oneStepValue πnew γ)^[n] v)
      Filter.atTop (𝓝 w) := by
    rw [hc.fixedPoint_unique hw]
    exact hc.tendsto_iterate_fixedPoint v
  exact ge_of_tendsto' ht hiter

/-- Every policy Bellman value admits a greedy policy with a nondecreasing Bellman value. -/
theorem exists_policy_improvement (m : MDP S A) (πold : StationaryPolicy S A)
    {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (v : S → ℝ)
    (hv : m.oneStepValue πold γ v = v) :
    ∃ πnew : StationaryPolicy S A, ∃ w : S → ℝ,
      m.oneStepValue πnew γ v = m.optimalityOperator γ v ∧
      m.oneStepValue πnew γ w = w ∧ v ≤ w := by
  obtain ⟨a, ha⟩ := m.exists_deterministic_greedy_policy γ v
  obtain ⟨w, hw, _⟩ := m.existsUnique_oneStepValue_fixedPoint
    (fun s => PMF.pure (a s)) hγ0 hγ1
  exact ⟨_, w, ha, hw, m.policy_improvement πold _ hγ0 hγ1 v w hv ha hw⟩

end Rlib.MDP
