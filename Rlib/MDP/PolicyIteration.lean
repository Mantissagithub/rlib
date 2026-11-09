module

public import Rlib.MDP.PolicyImprovement
public import Mathlib.Data.Fintype.Pigeonhole

/-! # Finite policy iteration and terminal Bellman optimality -/

@[expose] public section

namespace Rlib.MDP

variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty A]

/-- Repeatedly evaluate a deterministic policy and choose the fixed greedy policy for its value. -/
noncomputable def policyIteration (m : MDP S A) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (p₀ : S → A) (n : ℕ) : S → A :=
  (fun p : S → A => m.greedyPolicy γ (m.policyValue (fun s => PMF.pure (p s)) hγ0 hγ1))^[n] p₀

/-- Policy iteration starts at the supplied deterministic policy. -/
@[simp]
theorem policyIteration_zero (m : MDP S A) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (p₀ : S → A) : m.policyIteration hγ0 hγ1 p₀ 0 = p₀ := by
  rfl

/-- Each step chooses the fixed greedy policy for the previous policy's value. -/
theorem policyIteration_succ (m : MDP S A) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (p₀ : S → A) (n : ℕ) :
    m.policyIteration hγ0 hγ1 p₀ (n + 1) =
      m.greedyPolicy γ (m.policyValue
        (fun s => PMF.pure (m.policyIteration hγ0 hγ1 p₀ n s)) hγ0 hγ1) := by
  exact Function.iterate_succ_apply' _ n p₀

/-- The next iterate is greedy with respect to the current policy's Bellman value. -/
theorem oneStepValue_policyIteration_succ (m : MDP S A) {γ : ℝ}
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (p₀ : S → A) (n : ℕ) :
    m.oneStepValue (fun s => PMF.pure (m.policyIteration hγ0 hγ1 p₀ (n + 1) s)) γ
      (m.policyValue (fun s => PMF.pure (m.policyIteration hγ0 hγ1 p₀ n s)) hγ0 hγ1) =
    m.optimalityOperator γ
      (m.policyValue (fun s => PMF.pure (m.policyIteration hγ0 hγ1 p₀ n s)) hγ0 hγ1) := by
  rw [policyIteration_succ]
  exact m.oneStepValue_greedyPolicy γ _

/-- Bellman values are nondecreasing along policy iteration. -/
theorem policyValue_policyIteration_mono (m : MDP S A) {γ : ℝ}
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (p₀ : S → A) :
    Monotone (fun n => m.policyValue
      (fun s => PMF.pure (m.policyIteration hγ0 hγ1 p₀ n s)) hγ0 hγ1) := by
  apply monotone_nat_of_le_succ
  intro n
  exact m.policy_improvement _ _ hγ0 hγ1 _ _
    (m.oneStepValue_policyValue _ hγ0 hγ1)
    (m.oneStepValue_policyIteration_succ hγ0 hγ1 p₀ n)
    (m.oneStepValue_policyValue _ hγ0 hγ1)

/-- Equal consecutive values make the next two policies equal, even when actions tie. -/
theorem policyIteration_stable_of_value_eq (m : MDP S A) {γ : ℝ}
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (p₀ : S → A) (n : ℕ)
    (h : m.policyValue (fun s => PMF.pure (m.policyIteration hγ0 hγ1 p₀ (n + 1) s))
        hγ0 hγ1 =
      m.policyValue (fun s => PMF.pure (m.policyIteration hγ0 hγ1 p₀ n s)) hγ0 hγ1) :
    m.policyIteration hγ0 hγ1 p₀ (n + 2) = m.policyIteration hγ0 hγ1 p₀ (n + 1) := by
  rw [show n + 2 = (n + 1) + 1 from rfl, policyIteration_succ, h]
  exact (m.policyIteration_succ hγ0 hγ1 p₀ n).symm

/-- A stable iterate has a value satisfying the Bellman optimality equation. -/
theorem optimalityOperator_policyValue_of_policyIteration_stable (m : MDP S A) {γ : ℝ}
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (p₀ : S → A) (n : ℕ)
    (h : m.policyIteration hγ0 hγ1 p₀ (n + 1) = m.policyIteration hγ0 hγ1 p₀ n) :
    m.optimalityOperator γ
      (m.policyValue (fun s => PMF.pure (m.policyIteration hγ0 hγ1 p₀ n s)) hγ0 hγ1) =
    m.policyValue (fun s => PMF.pure (m.policyIteration hγ0 hγ1 p₀ n s)) hγ0 hγ1 := by
  rw [← m.oneStepValue_policyIteration_succ hγ0 hγ1 p₀ n, h]
  exact m.oneStepValue_policyValue _ hγ0 hγ1

/-- Policy iteration eventually stays at one policy whose value is Bellman optimal. -/
theorem exists_policyIteration_stable_optimal (m : MDP S A) {γ : ℝ}
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (p₀ : S → A) :
    ∃ N : ℕ, (∀ k : ℕ, m.policyIteration hγ0 hγ1 p₀ (N + k) =
        m.policyIteration hγ0 hγ1 p₀ N) ∧
      m.optimalityOperator γ
        (m.policyValue (fun s => PMF.pure (m.policyIteration hγ0 hγ1 p₀ N s)) hγ0 hγ1) =
      m.policyValue (fun s => PMF.pure (m.policyIteration hγ0 hγ1 p₀ N s)) hγ0 hγ1 := by
  classical
  let p := m.policyIteration hγ0 hγ1 p₀
  let V := fun n => m.policyValue (fun s => PMF.pure (p n s)) hγ0 hγ1
  have hmono : Monotone V := m.policyValue_policyIteration_mono hγ0 hγ1 p₀
  obtain ⟨i, j, hij, heq⟩ := Finite.exists_ne_map_eq_of_infinite p
  have hordered : ∃ i j : ℕ, i < j ∧ p i = p j := by
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · exact ⟨i, j, hlt, heq⟩
    · exact ⟨j, i, hgt, heq.symm⟩
  obtain ⟨i, j, hij, heq⟩ := hordered
  have hvalues : V (i + 1) = V i := by
    apply le_antisymm
    · calc
        V (i + 1) ≤ V j := hmono hij
        _ = V i := by dsimp [V]; rw [heq]
    · exact hmono (Nat.le_succ i)
  have hstable : p (i + 1 + 1) = p (i + 1) :=
    m.policyIteration_stable_of_value_eq hγ0 hγ1 p₀ i hvalues
  refine ⟨i + 1, ?_, m.optimalityOperator_policyValue_of_policyIteration_stable
    hγ0 hγ1 p₀ (i + 1) hstable⟩
  let f := fun q : S → A => m.greedyPolicy γ (m.policyValue (fun s => PMF.pure (q s)) hγ0 hγ1)
  have hfixed : f (p (i + 1)) = p (i + 1) :=
    (m.policyIteration_succ hγ0 hγ1 p₀ (i + 1)).symm.trans hstable
  intro k
  change f^[i + 1 + k] p₀ = p (i + 1)
  rw [Nat.add_comm (i + 1) k, Function.iterate_add_apply]
  exact Function.iterate_fixed hfixed k

end Rlib.MDP
