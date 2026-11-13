module

public import Rlib.MDP.TotalVariance
public import Rlib.MDP.QGreedy
public import Rlib.Probability.Bernstein

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

open MeasureTheory ProbabilityTheory

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

omit [Fintype A] [Nonempty A] in
/-- The variance of `v` under `P (· | s, a)` is the expected squared deviation from the mean. -/
theorem expect_sub_sq_eq_transitionVar (m : MDP S A) (v : S → ℝ) (s : S) (a : A) :
    expect (m.transition s a) (fun s' => (v s' - expect (m.transition s a) v) ^ 2) =
      m.transitionVar v s a := by
  set c := expect (m.transition s a) v
  have hterm (s' : S) : (v s' - c) ^ 2 = v s' ^ 2 + (-2 * c) * v s' + c ^ 2 := by ring
  simp only [hterm, expect_add, expect_mul, expect_const, transitionVar]
  simp only [c]
  ring

/-- The MDP with the rewards of `m` and the empirical transition laws of observed successors,
as in the generative model of Agarwal, Jiang, Kakade, and Sun, Section 2.1. -/
def withSuccessors {n : ℕ} (m : MDP S A) (rows : S → A → Fin (n + 1) → S) : MDP S A where
  reward := m.reward
  transition s a := empiricalPMF (rows s a)

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [MeasurableSpace S] [MeasurableSingletonClass S] {n : ℕ}

omit [Fintype A] [Nonempty A] in
/-- **Bernstein deviation at one pair.** If the `n + 1` successors at `(s, a)` are independent
with law `P (· | s, a)` and `v` takes values in `[0, B]` with `B > 0`, then for `0 < δ ≤ 1`,
`|(P - P̂) v (s, a)| ≥ √(2 * Var_P (v) (s, a) * log (2 / δ) / (n + 1)) +
2 * B * log (2 / δ) / (3 * (n + 1))` with probability at most `δ`. -/
theorem measure_transition_deviation_le (m : MDP S A) (D : Ω → S → A → Fin (n + 1) → S)
    (s : S) (a : A) (hindep : iIndepFun (fun i ω => D ω s a i) μ)
    (hmeas : ∀ i, AEMeasurable (fun ω => D ω s a i) μ)
    (hlaw : ∀ i, μ.map (fun ω => D ω s a i) = (m.transition s a).toMeasure)
    {v : S → ℝ} {B : ℝ} (hB : 0 < B) (hv : ∀ s, v s ∈ Set.Icc 0 B) {δ : ℝ} (hδ0 : 0 < δ)
    (hδ1 : δ ≤ 1) :
    μ.real {ω | Real.sqrt (2 * m.transitionVar v s a * Real.log (2 / δ) / (n + 1)) +
        2 * B * Real.log (2 / δ) / (3 * (n + 1)) ≤
        |expect (m.transition s a) v - expect ((m.withSuccessors (D ω)).transition s a) v|} ≤
      δ := by
  have hvm : Measurable v := measurable_of_countable v
  set θ := expect (m.transition s a) v
  have hθ : θ ∈ Set.Icc 0 B := by
    constructor
    · have h := expect_mono (m.transition s a) (f := fun _ => 0) (g := v) fun t => (hv t).1
      rwa [expect_zero] at h
    · have h := expect_mono (m.transition s a) (g := fun _ => B) (f := v) fun t => (hv t).2
      rwa [expect_const] at h
  have hlawint (i : Fin (n + 1)) (f : S → ℝ) :
      ∫ ω, f (D ω s a i) ∂μ = expect (m.transition s a) f := by
    rw [← integral_toMeasure_eq_expect, ← hlaw i,
      integral_map (hmeas i) (measurable_of_countable f).aestronglyMeasurable]
  have h := measure_abs_sampleMean_sub_ge_le_bernstein (X := fun i ω => v (D ω s a i))
    (hindep.comp (fun _ => v) (fun _ => hvm)) (fun i => hvm.comp_aemeasurable (hmeas i))
    (M := B) (σ2 := m.transitionVar v s a) (θ := θ) hB (m.transitionVar_nonneg v s a)
    (fun i => ae_of_all μ fun ω => by
      rw [abs_le]
      constructor <;> linarith [(hv (D ω s a i)).1, (hv (D ω s a i)).2, hθ.1, hθ.2])
    (fun i => hlawint i v)
    (fun i => by rw [hlawint i (fun s' => (v s' - θ) ^ 2), expect_sub_sq_eq_transitionVar])
    hδ0 hδ1
  refine le_trans (le_of_eq ?_) h
  congr 1
  ext ω
  simp only [Set.mem_ofPred_eq, withSuccessors, expect_empiricalPMF, abs_sub_comm θ]

omit [Nonempty A] in
/-- **Uniform Bernstein deviations (Agarwal, Jiang, Kakade, and Sun, Lemma 2.10).** If the
successors at every pair are independent with the model's laws and `v` takes values in `[0, B]`,
then for `0 < δ ≤ 1`, with probability at least `1 - δ`, at every pair
`|(P - P̂) v| < √(2 * log (2 |S| |A| / δ) / (n + 1) * Var_P (v)) +
2 * B * log (2 |S| |A| / δ) / (3 * (n + 1))`. -/
theorem measure_exists_transition_deviation_le (m : MDP S A) (D : Ω → S → A → Fin (n + 1) → S)
    (hindep : ∀ s a, iIndepFun (fun i ω => D ω s a i) μ)
    (hmeas : ∀ s a i, AEMeasurable (fun ω => D ω s a i) μ)
    (hlaw : ∀ s a i, μ.map (fun ω => D ω s a i) = (m.transition s a).toMeasure)
    {v : S → ℝ} {B : ℝ} (hB : 0 < B) (hv : ∀ s, v s ∈ Set.Icc 0 B) {δ : ℝ} (hδ0 : 0 < δ)
    (hδ1 : δ ≤ 1) :
    μ.real {ω | ∃ s a, Real.sqrt (2 * Real.log (2 * (Fintype.card S * Fintype.card A) / δ) /
        (n + 1) * m.transitionVar v s a) +
        2 * B * Real.log (2 * (Fintype.card S * Fintype.card A) / δ) / (3 * (n + 1)) ≤
        |expect (m.transition s a) v - expect ((m.withSuccessors (D ω)).transition s a) v|} ≤
      δ := by
  classical
  by_cases hne : Nonempty (S × A)
  swap
  · have hempty : {ω | ∃ s a, Real.sqrt (2 * Real.log (2 * (Fintype.card S * Fintype.card A) / δ) /
        (n + 1) * m.transitionVar v s a) +
        2 * B * Real.log (2 * (Fintype.card S * Fintype.card A) / δ) / (3 * (n + 1)) ≤
        |expect (m.transition s a) v - expect ((m.withSuccessors (D ω)).transition s a) v|} =
        ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_exists]
      exact fun s a _ => hne ⟨(s, a)⟩
    rw [hempty, measureReal_empty]
    exact hδ0.le
  obtain ⟨⟨s₀, a₀⟩⟩ := hne
  have : Nonempty S := ⟨s₀⟩
  have : Nonempty A := ⟨a₀⟩
  set K : ℝ := Fintype.card S * Fintype.card A
  have hK : 1 ≤ K := by
    have h1 : (1 : ℝ) ≤ Fintype.card S := Nat.one_le_cast.mpr Fintype.card_pos
    have h2 : (1 : ℝ) ≤ Fintype.card A := Nat.one_le_cast.mpr Fintype.card_pos
    nlinarith
  set δ' := δ / K
  have hδ'0 : 0 < δ' := div_pos hδ0 (by linarith)
  have hδ'1 : δ' ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
  have hlog : Real.log (2 / δ') = Real.log (2 * K / δ) := by
    simp only [δ']; congr 1; field_simp
  have hsub : {ω | ∃ s a, Real.sqrt (2 * Real.log (2 * K / δ) / (n + 1) * m.transitionVar v s a) +
        2 * B * Real.log (2 * K / δ) / (3 * (n + 1)) ≤
        |expect (m.transition s a) v - expect ((m.withSuccessors (D ω)).transition s a) v|} ⊆
      ⋃ p : S × A, {ω | Real.sqrt (2 * m.transitionVar v p.1 p.2 * Real.log (2 / δ') / (n + 1)) +
        2 * B * Real.log (2 / δ') / (3 * (n + 1)) ≤
        |expect (m.transition p.1 p.2) v -
          expect ((m.withSuccessors (D ω)).transition p.1 p.2) v|} := by
    rintro ω ⟨s, a, h⟩
    refine Set.mem_iUnion.mpr ⟨(s, a), ?_⟩
    simp only [Set.mem_ofPred_eq, hlog]
    convert h using 4
    ring
  refine (measureReal_mono hsub).trans ((measureReal_iUnion_fintype_le _).trans ?_)
  calc ∑ p : S × A, μ.real {ω | Real.sqrt (2 * m.transitionVar v p.1 p.2 *
          Real.log (2 / δ') / (n + 1)) + 2 * B * Real.log (2 / δ') / (3 * (n + 1)) ≤
          |expect (m.transition p.1 p.2) v -
            expect ((m.withSuccessors (D ω)).transition p.1 p.2) v|}
      ≤ ∑ _p : S × A, δ' := Finset.sum_le_sum fun p _ =>
        m.measure_transition_deviation_le D p.1 p.2 (hindep p.1 p.2) (hmeas p.1 p.2)
          (hlaw p.1 p.2) hB hv hδ'0 hδ'1
    _ = δ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, nsmul_eq_mul, δ', K]
        push_cast
        field_simp

omit [Fintype A] [Nonempty A] in
/-- **Hoeffding deviation at one pair.** If the `n + 1` successors at `(s, a)` are independent
with law `P (· | s, a)` and `|v| ≤ B` with `B > 0`, then for `0 < δ`,
`|(P - P̂) v (s, a)| ≥ B * √(2 * log (2 / δ) / (n + 1))` with probability at most `δ`. -/
theorem measure_transition_hoeffding_le (m : MDP S A) (D : Ω → S → A → Fin (n + 1) → S)
    (s : S) (a : A) (hindep : iIndepFun (fun i ω => D ω s a i) μ)
    (hmeas : ∀ i, AEMeasurable (fun ω => D ω s a i) μ)
    (hlaw : ∀ i, μ.map (fun ω => D ω s a i) = (m.transition s a).toMeasure)
    {v : S → ℝ} {B : ℝ} (hB : 0 < B) (hv : ∀ s, |v s| ≤ B) {δ : ℝ} (hδ0 : 0 < δ)
    (hδ2 : δ ≤ 2) :
    μ.real {ω | B * Real.sqrt (2 * Real.log (2 / δ) / (n + 1)) ≤
        |expect (m.transition s a) v - expect ((m.withSuccessors (D ω)).transition s a) v|} ≤
      δ := by
  have hvm : Measurable v := measurable_of_countable v
  have hN : (0 : ℝ) < n + 1 := by positivity
  have hL : 0 ≤ Real.log (2 / δ) := Real.log_nonneg (by rw [le_div_iff₀ hδ0]; linarith)
  have hlawint (i : Fin (n + 1)) :
      ∫ ω, v (D ω s a i) ∂μ = expect (m.transition s a) v := by
    rw [← integral_toMeasure_eq_expect, ← hlaw i,
      integral_map (hmeas i) hvm.aestronglyMeasurable]
  set ε := B * Real.sqrt (2 * Real.log (2 / δ) / (n + 1))
  have hε : 0 ≤ ε := by positivity
  have h := measure_abs_sampleMean_sub_le_of_abs_le (X := fun i ω => v (D ω s a i))
    (hindep.comp (fun _ => v) (fun _ => hvm)) (fun i => hvm.comp_aemeasurable (hmeas i)) hB
    (fun i => ae_of_all μ fun ω => hv _) hlawint hε
  have hexp : 2 * Real.exp (-((n + 1 : ℝ) * ε ^ 2) / (2 * B ^ 2)) = δ := by
    have hsq : ε ^ 2 = B ^ 2 * (2 * Real.log (2 / δ) / (n + 1)) := by
      simp only [ε, mul_pow, Real.sq_sqrt (by positivity : 0 ≤ 2 * Real.log (2 / δ) / (n + 1))]
    rw [hsq, show -((n + 1 : ℝ) * (B ^ 2 * (2 * Real.log (2 / δ) / (n + 1)))) / (2 * B ^ 2) =
      -Real.log (2 / δ) by field_simp, Real.exp_neg, Real.exp_log (by positivity)]
    field_simp
  rw [hexp] at h
  refine le_trans (le_of_eq ?_) h
  congr 1
  ext ω
  simp only [Set.mem_ofPred_eq, withSuccessors, expect_empiricalPMF,
    abs_sub_comm (expect (m.transition s a) v)]

omit [Nonempty A] in
/-- **Uniform Hoeffding deviations.** If the successors at every pair are independent with the
model's laws and `|v| ≤ B`, then for `0 < δ ≤ 1`, with probability at least `1 - δ`,
`|(P - P̂) v| < B * √(2 * log (2 |S| |A| / δ) / (n + 1))` at every pair. -/
theorem measure_exists_transition_hoeffding_le (m : MDP S A) (D : Ω → S → A → Fin (n + 1) → S)
    (hindep : ∀ s a, iIndepFun (fun i ω => D ω s a i) μ)
    (hmeas : ∀ s a i, AEMeasurable (fun ω => D ω s a i) μ)
    (hlaw : ∀ s a i, μ.map (fun ω => D ω s a i) = (m.transition s a).toMeasure)
    {v : S → ℝ} {B : ℝ} (hB : 0 < B) (hv : ∀ s, |v s| ≤ B) {δ : ℝ} (hδ0 : 0 < δ)
    (hδ1 : δ ≤ 1) :
    μ.real {ω | ∃ s a, B * Real.sqrt (2 * Real.log (2 * (Fintype.card S * Fintype.card A) / δ) /
        (n + 1)) ≤
        |expect (m.transition s a) v - expect ((m.withSuccessors (D ω)).transition s a) v|} ≤
      δ := by
  classical
  by_cases hne : Nonempty (S × A)
  swap
  · have hempty : {ω | ∃ s a, B * Real.sqrt (2 * Real.log (2 * (Fintype.card S *
        Fintype.card A) / δ) / (n + 1)) ≤
        |expect (m.transition s a) v - expect ((m.withSuccessors (D ω)).transition s a) v|} =
        ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_exists]
      exact fun s a _ => hne ⟨(s, a)⟩
    rw [hempty, measureReal_empty]
    exact hδ0.le
  obtain ⟨⟨s₀, a₀⟩⟩ := hne
  have : Nonempty S := ⟨s₀⟩
  have : Nonempty A := ⟨a₀⟩
  set K : ℝ := Fintype.card S * Fintype.card A
  have hK : 1 ≤ K := by
    have h1 : (1 : ℝ) ≤ Fintype.card S := Nat.one_le_cast.mpr Fintype.card_pos
    have h2 : (1 : ℝ) ≤ Fintype.card A := Nat.one_le_cast.mpr Fintype.card_pos
    nlinarith
  set δ' := δ / K
  have hδ'0 : 0 < δ' := div_pos hδ0 (by linarith)
  have hδ'2 : δ' ≤ 2 := ((div_le_one (by linarith)).mpr (by linarith)).trans (by norm_num)
  have hlog : Real.log (2 / δ') = Real.log (2 * K / δ) := by
    simp only [δ']; congr 1; field_simp
  have hsub : {ω | ∃ s a, B * Real.sqrt (2 * Real.log (2 * K / δ) / (n + 1)) ≤
        |expect (m.transition s a) v - expect ((m.withSuccessors (D ω)).transition s a) v|} ⊆
      ⋃ p : S × A, {ω | B * Real.sqrt (2 * Real.log (2 / δ') / (n + 1)) ≤
        |expect (m.transition p.1 p.2) v -
          expect ((m.withSuccessors (D ω)).transition p.1 p.2) v|} := by
    rintro ω ⟨s, a, h⟩
    refine Set.mem_iUnion.mpr ⟨(s, a), ?_⟩
    simp only [Set.mem_ofPred_eq, hlog]
    exact h
  refine (measureReal_mono hsub).trans ((measureReal_iUnion_fintype_le _).trans ?_)
  calc ∑ p : S × A, μ.real {ω | B * Real.sqrt (2 * Real.log (2 / δ') / (n + 1)) ≤
          |expect (m.transition p.1 p.2) v -
            expect ((m.withSuccessors (D ω)).transition p.1 p.2) v|}
      ≤ ∑ _p : S × A, δ' := Finset.sum_le_sum fun p _ =>
        m.measure_transition_hoeffding_le D p.1 p.2 (hindep p.1 p.2) (hmeas p.1 p.2)
          (hlaw p.1 p.2) hB hv hδ'0 hδ'2
    _ = δ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, nsmul_eq_mul, δ', K]
        push_cast
        field_simp

end Rlib.MDP
