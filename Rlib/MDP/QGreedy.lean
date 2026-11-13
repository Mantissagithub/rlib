module

public import Rlib.MDP.QSampleComplexity
public import Rlib.MDP.SoftmaxPGConvergence

/-! # Greedy policies of estimated Q tables

This file follows Agarwal, Jiang, Kakade, and Sun, *Reinforcement Learning: Theory and
Algorithms*, Lemma 1.11 (Q-error amplification): if a table `q` is within `ε` of the optimal Q
table `Q*` in sup norm, the policy that is greedy with respect to `q` has value at least
`V* - 2 * ε / (1 - γ)` at every state, where `V* s = max_a Q* (s, a)`. Combined with the sample
complexity of model-based estimation, the greedy policy of the empirical Q fixed point is
within `2 * ε / (1 - γ) ^ 2` of optimal with probability at least `1 - δ`.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Rlib.MDP

variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty A]

/-- An action with the largest table entry at each state. -/
def qGreedy (q : S → A → ℝ) (s : S) : A :=
  Classical.choose (Finset.exists_max_image Finset.univ (q s) Finset.univ_nonempty)

omit [Fintype S] in
/-- The greedy action attains the largest table entry. -/
theorem le_qGreedy (q : S → A → ℝ) (s : S) (a : A) : q s a ≤ q s (qGreedy q s) :=
  (Classical.choose_spec (Finset.exists_max_image Finset.univ (q s)
    Finset.univ_nonempty)).2 a (Finset.mem_univ a)

/-- The deterministic policy that is greedy with respect to a table `q`. -/
def qGreedyPolicy (q : S → A → ℝ) : StationaryPolicy S A := fun s => PMF.pure (qGreedy q s)

/-- **The optimal value dominates every policy.** If `q` is a Bellman Q fixed point, then
`V* = qMax q` is at least the value of every stationary policy. -/
theorem policyValue_le_qMax (m : MDP S A) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    {q : S → A → ℝ} (hq : m.qBellmanOperator γ q = q) (π : StationaryPolicy S A) (s : S) :
    m.policyValue π hγ0 hγ1 s ≤ qMax q s :=
  m.policyValue_le_of_oneStepActionValue_le π hγ0 hγ1 (fun s a => by
    have h : m.oneStepActionValue γ (qMax q) s a = q s a := congrFun (congrFun hq s) a
    rw [h]
    exact Finset.le_sup' (q s) (Finset.mem_univ a)) s

/-- **Q-error amplification (Agarwal, Jiang, Kakade, and Sun, Lemma 1.11).** If `q*` is a
Bellman Q fixed point and `‖q - q*‖ ≤ ε`, the greedy policy of `q` has value at least
`V* - 2 * ε / (1 - γ)` at every state, where `V* = qMax q*`. -/
theorem qMax_sub_policyValue_qGreedyPolicy_le (m : MDP S A) {γ : ℝ} (hγ0 : 0 ≤ γ)
    (hγ1 : γ < 1) {qstar : S → A → ℝ} (hq : m.qBellmanOperator γ qstar = qstar)
    {q : S → A → ℝ} {ε : ℝ} (hε : ‖q - qstar‖ ≤ ε) (s : S) :
    qMax qstar s - m.policyValue (qGreedyPolicy q) hγ0 hγ1 s ≤ 2 * ε / (1 - γ) := by
  have hγ : 0 < 1 - γ := sub_pos.mpr hγ1
  set V := m.policyValue (qGreedyPolicy q) hγ0 hγ1
  have : Nonempty S := ⟨s⟩
  obtain ⟨t, ht⟩ := Finite.exists_max fun s => qMax qstar s - V s
  suffices h : qMax qstar t - V t ≤ 2 * ε / (1 - γ) from (ht s).trans h
  have hent (s : S) (a : A) : |q s a - qstar s a| ≤ ε := by
    have h1 := norm_le_pi_norm (q - qstar) s
    have h2 := norm_le_pi_norm ((q - qstar) s) a
    rw [Real.norm_eq_abs] at h2
    exact h2.trans (h1.trans hε)
  set a := qGreedy q t
  obtain ⟨b, -, hb⟩ := Finset.exists_max_image Finset.univ (qstar t) Finset.univ_nonempty
  have hmax : qMax qstar t = qstar t b :=
    le_antisymm (Finset.sup'_le _ _ fun c _ => hb c (Finset.mem_univ c))
      (Finset.le_sup' (qstar t) (Finset.mem_univ b))
  -- The greedy action is within `2 ε` of the best action under `q*`.
  have hgreedy : qstar t b ≤ qstar t a + 2 * ε := by
    have h1 := (abs_le.mp (hent t b)).1
    have h2 := (abs_le.mp (hent t a)).2
    have h3 := le_qGreedy q t b
    linarith
  -- Following the greedy action loses at most `γ` times the worst value gap afterwards.
  have hfix : V t = m.oneStepActionValue γ V t a := by
    have h := congrFun (m.oneStepValue_policyValue (qGreedyPolicy q) hγ0 hγ1) t
    change expect (PMF.pure a) (m.oneStepActionValue γ V t) = V t at h
    rw [expect_pure] at h
    exact h.symm
  have hqa : qstar t a = m.oneStepActionValue γ (qMax qstar) t a :=
    (congrFun (congrFun hq t) a).symm
  have hgap : m.oneStepActionValue γ (qMax qstar) t a - m.oneStepActionValue γ V t a ≤
      γ * (qMax qstar t - V t) := by
    simp only [oneStepActionValue]
    have h := expect_mono (m.transition t a) (f := fun s => qMax qstar s - V s)
      (g := fun _ => qMax qstar t - V t) ht
    rw [expect_const] at h
    have hlin : expect (m.transition t a) (qMax qstar) - expect (m.transition t a) V =
        expect (m.transition t a) (fun s => qMax qstar s - V s) := by
      simp only [expect, ← Finset.sum_sub_distrib, ← mul_sub]
    nlinarith [mul_le_mul_of_nonneg_left h hγ0]
  rw [le_div_iff₀ hγ]
  nlinarith

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [MeasurableSpace S] [MeasurableSingletonClass S] {n : ℕ}

/-- **The greedy policy of the empirical model is near optimal.** Under the conditions of
`measure_norm_ofSamples_fixed_sub_le_of_le`, the greedy policy of the empirical Bellman Q fixed
point has value within `2 * ε / (1 - γ) ^ 2` of optimal at every state, except with probability
at most `δ`. -/
theorem measure_qGreedyPolicy_suboptimal_le (m : MDP S A)
    (D : Ω → S → A → Fin (n + 1) → ℝ × S) {γ R : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (hR0 : 0 < R)
    (hindep : ∀ s a, iIndepFun (fun i ω => D ω s a i) μ)
    (hmeas : ∀ s a i, AEMeasurable (fun ω => D ω s a i) μ)
    (hR : ∀ s a i, ∀ᵐ ω ∂μ, |(D ω s a i).1| ≤ R)
    (hreward : ∀ s a i, ∫ ω, (D ω s a i).1 ∂μ = m.reward s a)
    (hlaw : ∀ s a i, μ.map (fun ω => (D ω s a i).2) = (m.transition s a).toMeasure)
    {q : S → A → ℝ} (hq : m.qBellmanOperator γ q = q) (qhat : Ω → S → A → ℝ)
    (hqhat : ∀ ω, (ofSamples (D ω)).qBellmanOperator γ (qhat ω) = qhat ω)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    (hn : 2 * R ^ 2 * Real.log (2 * (Fintype.card S * Fintype.card A) / δ) /
      (ε ^ 2 * (1 - γ) ^ 2) ≤ n + 1) :
    μ.real {ω | ∃ s, 2 * ε / (1 - γ) ^ 2 <
      qMax q s - m.policyValue (qGreedyPolicy (qhat ω)) hγ0 hγ1 s} ≤ δ := by
  have hγ : 0 < 1 - γ := sub_pos.mpr hγ1
  refine le_trans (measureReal_mono fun ω hω => ?_)
    (m.measure_norm_ofSamples_fixed_sub_le_of_le D hγ0 hγ1 hR0 hindep hmeas hR hreward hlaw hq
      qhat hqhat hε hδ hn)
  obtain ⟨s, hs⟩ := hω
  simp only [Set.mem_ofPred_eq]
  by_contra hlt
  rw [not_le] at hlt
  have h := m.qMax_sub_policyValue_qGreedyPolicy_le hγ0 hγ1 hq hlt.le s
  have : 2 * (ε / (1 - γ)) / (1 - γ) = 2 * ε / (1 - γ) ^ 2 := by field_simp
  linarith

end Rlib.MDP
