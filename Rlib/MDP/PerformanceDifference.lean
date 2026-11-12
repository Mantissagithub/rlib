module

public import Rlib.MDP.Advantage

/-! # The performance difference lemma

The gain from switching policies is the value of the new policy when every reward is replaced
by the old policy's advantage.
-/

@[expose] public section

noncomputable section

namespace Rlib.MDP

variable {S A : Type*} [Fintype S] [Fintype A]

/-- The same transitions with a different expected reward. -/
def withReward (m : MDP S A) (g : S → A → ℝ) : MDP S A where
  transition := m.transition
  reward := g

/-- A policy whose expected immediate reward is nonnegative at every state has a nonnegative
value for a discount in `[0, 1)`. -/
theorem policyValue_nonneg (m : MDP S A) (π : StationaryPolicy S A) {γ : ℝ} (hγ0 : 0 ≤ γ)
    (hγ1 : γ < 1) (hr : ∀ s, 0 ≤ expect (π s) (m.reward s)) (s : S) :
    0 ≤ m.policyValue π hγ0 hγ1 s := by
  set v := m.policyValue π hγ0 hγ1
  have : Nonempty S := ⟨s⟩
  obtain ⟨t, ht⟩ := Finite.exists_min v
  suffices 0 ≤ v t from this.trans (ht s)
  have hfix := congrFun (m.oneStepValue_policyValue π hγ0 hγ1) t
  have hlow : expect (π t) (fun a => m.reward t a + γ * v t) ≤
      m.oneStepValue π γ v t := by
    refine expect_mono _ fun a => ?_
    simp only [oneStepActionValue]
    have : v t ≤ expect (m.transition t a) v := by
      simpa using expect_mono (m.transition t a) (fun x => ht x) (f := fun _ => v t)
    nlinarith
  rw [expect_add, expect_const, hfix] at hlow
  nlinarith [hr t]

/-- **Performance difference lemma.** For a discount in `[0, 1)`, the value of a policy `π'`
minus the value of a policy `π` is the value of `π'` when every reward is replaced by the
advantage of `π`. -/
theorem policyValue_sub_policyValue (m : MDP S A) (π π' : StationaryPolicy S A) {γ : ℝ}
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) :
    m.policyValue π' hγ0 hγ1 - m.policyValue π hγ0 hγ1 =
      (m.withReward (m.advantage π hγ0 hγ1)).policyValue π' hγ0 hγ1 := by
  apply eq_policyValue_of_fixedPoint
  funext s
  set V' := m.policyValue π' hγ0 hγ1
  set V := m.policyValue π hγ0 hγ1
  have hpoint : (m.withReward (m.advantage π hγ0 hγ1)).oneStepActionValue γ (V' - V) s =
      fun a => m.oneStepActionValue γ V' s a + (-1) * V s := by
    funext a
    have hsub : expect (m.transition s a) (V' - V) =
        expect (m.transition s a) V' - expect (m.transition s a) V := by
      have : (V' - V) = fun t => V' t + (-1) * V t := by
        funext t
        simp only [Pi.sub_apply]
        ring
      rw [this, expect_add, expect_mul]
      ring
    simp only [oneStepActionValue, withReward, advantage, policyActionValue, hsub]
    ring
  simp only [oneStepValue, hpoint]
  rw [expect_add, expect_const]
  have hV' := congrFun (m.oneStepValue_policyValue π' hγ0 hγ1) s
  simp only [oneStepValue] at hV'
  rw [hV']
  simp only [Pi.sub_apply]
  ring

/-- **Policy improvement from advantages.** If a policy `π'` has nonnegative expected advantage
under a policy `π` at every state, then `π'` is at least as good as `π` everywhere. -/
theorem policyValue_le_of_expect_advantage_nonneg (m : MDP S A) (π π' : StationaryPolicy S A)
    {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (h : ∀ s, 0 ≤ expect (π' s) (m.advantage π hγ0 hγ1 s)) (s : S) :
    m.policyValue π hγ0 hγ1 s ≤ m.policyValue π' hγ0 hγ1 s := by
  have hdiff := congrFun (m.policyValue_sub_policyValue π π' hγ0 hγ1) s
  have hnn := (m.withReward (m.advantage π hγ0 hγ1)).policyValue_nonneg π' hγ0 hγ1 h s
  simp only [Pi.sub_apply] at hdiff
  linarith

end Rlib.MDP
