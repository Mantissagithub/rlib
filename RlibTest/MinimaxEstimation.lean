module

import Rlib

open Rlib

/-- Agarwal, Jiang, Kakade, and Sun, Lemma 2.5, for any two MDPs that share their rewards. -/
example {S A : Type} [Fintype S] [Fintype A] [Nonempty A] (m m' : MDP S A)
    (hrew : m'.reward = m.reward) {q q' : S → A → ℝ}
    (hq : m.qBellmanOperator (1 / 2) q = q) (hq' : m'.qBellmanOperator (1 / 2) q' = q')
    (s : S) (a : A) :
    q s a - q' s a ≤ (m'.withReward (m.transitionGap m' (1 / 2) (qMax q))).policyActionValue
      (MDP.qGreedyPolicy q) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) s a :=
  (m.sub_le_policyActionValue_transitionGap m' hrew (by norm_num) (by norm_num) hq hq' s a).2

/-- When the two transition laws agree the gap reward vanishes. -/
example {S A : Type} [Fintype S] [Fintype A] (m : MDP S A) (γ : ℝ) (v : S → ℝ) :
    m.transitionGap m γ v = fun _ _ => 0 := by
  funext s a
  simp [MDP.transitionGap]
