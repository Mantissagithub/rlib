module

public import Rlib.MDP.TotalVariance
public import Rlib.MDP.QGreedy

/-! # Minimax model-based Q estimation

This file follows Agarwal, Jiang, Kakade, and Sun, *Reinforcement Learning: Theory and
Algorithms*, Sections 2.3 and 2.4. Two MDPs `M` and `M̂` share their rewards and differ in their
transitions `P` and `P̂`. Writing `(I - γ P̂^π)⁻¹ g` for the action values of `π` in `M̂` under
reward `g`, their Lemma 2.5 (component-wise bounds) states
`γ (I - γ P̂^{π̂*})⁻¹ (P - P̂) V* ≤ Q* - Q̂* ≤ γ (I - γ P̂^{π*})⁻¹ (P - P̂) V*`, where `π*` and
`π̂*` are greedy for `Q*` and `Q̂*`. Here the factor `γ` sits inside the reward.
-/

@[expose] public section

noncomputable section

namespace Rlib.MDP

variable {S A : Type*} [Fintype S] [Fintype A]

/-- **Comparison from below for action values.** If `w ≤ g + γ P (π w)`, then `w` is at most the
action values of `π` under reward `g`. -/
theorem le_policyActionValue_withReward (m : MDP S A) (π : StationaryPolicy S A) {γ : ℝ}
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (g w : S → A → ℝ)
    (hw : ∀ s a, w s a ≤ g s a + γ * expect (m.transition s a) (fun s' => expect (π s') (w s')))
    (s : S) (a : A) : w s a ≤ (m.withReward g).policyActionValue π hγ0 hγ1 s a := by
  set V := (m.withReward g).policyValue π hγ0 hγ1
  set W : S → ℝ := fun s' => expect (π s') (w s')
  have hWV : ∀ s', W s' ≤ V s' := by
    have : Nonempty S := ⟨s⟩
    obtain ⟨t, ht⟩ := Finite.exists_max fun s' => W s' - V s'
    suffices h : W t - V t ≤ 0 from fun s' => by linarith [ht s']
    have hfix : (m.withReward g).oneStepValue π γ V t = V t :=
      congrFun ((m.withReward g).oneStepValue_policyValue π hγ0 hγ1) t
    have hWt : W t ≤ expect (π t) (fun a => g t a + γ * expect (m.transition t a) W) :=
      expect_mono _ fun a => hw t a
    have hdiff : expect (π t) (fun a => g t a + γ * expect (m.transition t a) W) -
        expect (π t) (fun a => g t a + γ * expect (m.transition t a) V) ≤ γ * (W t - V t) := by
      rw [← expect_sub]
      refine le_trans (expect_mono _ fun a => ?_) (expect_const _ _).le
      have hE : expect (m.transition t a) W - expect (m.transition t a) V ≤ W t - V t := by
        rw [← expect_sub]
        exact (expect_mono _ fun s' => ht s').trans (expect_const _ _).le
      nlinarith [mul_le_mul_of_nonneg_left hE hγ0]
    change expect (π t) (fun a => g t a + γ * expect (m.transition t a) V) = V t at hfix
    nlinarith [sub_pos.mpr hγ1]
  have hQ : (m.withReward g).policyActionValue π hγ0 hγ1 s a =
      g s a + γ * expect (m.transition s a) V := rfl
  rw [hQ]
  refine (hw s a).trans ?_
  have := mul_le_mul_of_nonneg_left (expect_mono (m.transition s a) hWV) hγ0
  linarith

variable [Nonempty A]

omit [Fintype S] in
/-- The largest entry of a table is attained by its greedy action. -/
theorem qMax_eq_qGreedy (q : S → A → ℝ) (s : S) : qMax q s = q s (qGreedy q s) :=
  le_antisymm (Finset.sup'_le _ _ fun a _ => le_qGreedy q s a)
    (Finset.le_sup' (q s) (Finset.mem_univ _))

/-- The reward `γ (P - P̂) V*` that drives the gap between two Bellman Q fixed points. -/
def transitionGap (m m' : MDP S A) (γ : ℝ) (v : S → ℝ) (s : S) (a : A) : ℝ :=
  γ * (expect (m.transition s a) v - expect (m'.transition s a) v)

/-- With shared rewards, the gap between Bellman Q fixed points is the transition gap plus `γ P̂`
applied to the gap in maximal values. -/
theorem sub_eq_transitionGap_add (m m' : MDP S A) (hrew : m'.reward = m.reward) {γ : ℝ}
    {q q' : S → A → ℝ} (hq : m.qBellmanOperator γ q = q)
    (hq' : m'.qBellmanOperator γ q' = q') (s : S) (a : A) :
    q s a - q' s a = m.transitionGap m' γ (qMax q) s a +
      γ * expect (m'.transition s a) (fun s' => qMax q s' - qMax q' s') := by
  have h1 : q s a = m.reward s a + γ * expect (m.transition s a) (qMax q) :=
    (congrFun (congrFun hq s) a).symm
  have h2 : q' s a = m.reward s a + γ * expect (m'.transition s a) (qMax q') := by
    have := (congrFun (congrFun hq' s) a).symm
    simp only [qBellmanOperator, oneStepActionValue, hrew] at this
    exact this
  rw [h1, h2, expect_sub, transitionGap]
  ring

/-- **Component-wise bounds (Agarwal, Jiang, Kakade, and Sun, Lemma 2.5).** Let `M` and `M̂` share
their rewards, and let `Q*` and `Q̂*` be their Bellman Q fixed points. Then
`(I - γ P̂^{π̂*})⁻¹ (γ (P - P̂) V*) ≤ Q* - Q̂* ≤ (I - γ P̂^{π*})⁻¹ (γ (P - P̂) V*)`, where
`V* = max_a Q*` and `π*`, `π̂*` are greedy for `Q*`, `Q̂*`. -/
theorem sub_le_policyActionValue_transitionGap (m m' : MDP S A) (hrew : m'.reward = m.reward)
    {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) {q q' : S → A → ℝ} (hq : m.qBellmanOperator γ q = q)
    (hq' : m'.qBellmanOperator γ q' = q') (s : S) (a : A) :
    (m'.withReward (m.transitionGap m' γ (qMax q))).policyActionValue (qGreedyPolicy q')
        hγ0 hγ1 s a ≤ q s a - q' s a ∧
      q s a - q' s a ≤
        (m'.withReward (m.transitionGap m' γ (qMax q))).policyActionValue (qGreedyPolicy q)
          hγ0 hγ1 s a := by
  set D : S → A → ℝ := fun s a => q s a - q' s a
  have hD := m.sub_eq_transitionGap_add m' hrew hq hq'
  constructor
  · refine m'.policyActionValue_withReward_le _ hγ0 hγ1 _ D (fun s a => ?_) s a
    rw [show D s a = _ from hD s a]
    refine add_le_add_right (mul_le_mul_of_nonneg_left (expect_mono _ fun s' => ?_) hγ0) _
    simp only [qGreedyPolicy, expect_pure, D]
    rw [qMax_eq_qGreedy q' s']
    linarith [le_qGreedy q s' (qGreedy q' s'), qMax_eq_qGreedy q s']
  · refine m'.le_policyActionValue_withReward _ hγ0 hγ1 _ D (fun s a => ?_) s a
    rw [show D s a = _ from hD s a]
    refine add_le_add_right (mul_le_mul_of_nonneg_left (expect_mono _ fun s' => ?_) hγ0) _
    simp only [qGreedyPolicy, expect_pure, D]
    rw [qMax_eq_qGreedy q s']
    linarith [le_qGreedy q' s' (qGreedy q s'), qMax_eq_qGreedy q' s']

end Rlib.MDP
