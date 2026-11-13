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

open MeasureTheory ProbabilityTheory in
/-- Agarwal, Jiang, Kakade, and Sun, Lemma 2.10, for a value bounded by `1 / (1 - γ) = 2`. -/
example {Ω S A : Type} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    [Fintype S] [Fintype A] [MeasurableSpace S] [MeasurableSingletonClass S] {n : ℕ}
    (m : MDP S A) (D : Ω → S → A → Fin (n + 1) → S)
    (hindep : ∀ s a, iIndepFun (fun i ω => D ω s a i) μ)
    (hmeas : ∀ s a i, AEMeasurable (fun ω => D ω s a i) μ)
    (hlaw : ∀ s a i, μ.map (fun ω => D ω s a i) = (m.transition s a).toMeasure)
    (v : S → ℝ) (hv : ∀ s, v s ∈ Set.Icc 0 2) :
    μ.real {ω | ∃ s a, Real.sqrt (2 * Real.log (2 * (Fintype.card S * Fintype.card A) /
        (1 / 10)) / (n + 1) * m.transitionVar v s a) +
        2 * 2 * Real.log (2 * (Fintype.card S * Fintype.card A) / (1 / 10)) / (3 * (n + 1)) ≤
        |expect (m.transition s a) v - expect ((m.withSuccessors (D ω)).transition s a) v|} ≤
      1 / 10 :=
  m.measure_exists_transition_deviation_le D hindep hmeas hlaw (by norm_num) hv (by norm_num)
    (by norm_num)
