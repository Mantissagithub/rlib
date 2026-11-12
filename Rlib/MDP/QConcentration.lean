module

public import Rlib.MDP.Concentration
public import Rlib.MDP.QSynchronous

/-! # Concentration of the empirical Bellman Q operator

With independent samples of rewards and successors for each state-action pair, the Bellman Q
operator of the empirical MDP concentrates around the model's Bellman Q operator at any fixed
table.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter

namespace Rlib.MDP

variable {Ω S A : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [Fintype S] [Fintype A] [Nonempty A] [MeasurableSpace S] [MeasurableSingletonClass S]
  {n : ℕ}

/-- **Hoeffding bound for one empirical Bellman Q target.** Suppose the `n + 1` samples at a
state-action pair are independent, have rewards bounded by `R > 0` with the model's mean, and
have the model's transition law as successor law. At any fixed table `q`, the empirical Bellman
Q target deviates from the model's by at least `ε` with probability at most
`2 * exp (-(n + 1) * ε ^ 2 / (2 * (R + γ * ‖q‖) ^ 2))`. -/
theorem measure_abs_ofSamples_qBellmanOperator_sub_le (m : MDP S A)
    (D : Ω → S → A → Fin (n + 1) → ℝ × S) {γ R : ℝ} (hγ0 : 0 ≤ γ) (hR0 : 0 < R)
    (q : S → A → ℝ) (s : S) (a : A)
    (hindep : iIndepFun (fun i ω => D ω s a i) μ)
    (hmeas : ∀ i, AEMeasurable (fun ω => D ω s a i) μ)
    (hR : ∀ i, ∀ᵐ ω ∂μ, |(D ω s a i).1| ≤ R)
    (hreward : ∀ i, ∫ ω, (D ω s a i).1 ∂μ = m.reward s a)
    (hlaw : ∀ i, μ.map (fun ω => (D ω s a i).2) = (m.transition s a).toMeasure)
    {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ |(ofSamples (D ω)).qBellmanOperator γ q s a -
      m.qBellmanOperator γ q s a|} ≤
      2 * Real.exp (-((n + 1 : ℝ) * ε ^ 2) / (2 * (R + γ * ‖q‖) ^ 2)) := by
  set f : ℝ × S → ℝ := fun x => qLearningTarget γ q x
  have hf : Measurable f :=
    measurable_fst.add (measurable_const.mul ((measurable_of_countable (qMax q)).comp
      measurable_snd))
  have hmax (t : S) : |qMax q t| ≤ ‖q‖ := by
    have := (norm_le_pi_norm (qMax q) t).trans (norm_qMax_le q)
    rwa [Real.norm_eq_abs] at this
  have hbound (i : Fin (n + 1)) : ∀ᵐ ω ∂μ, |f (D ω s a i)| ≤ R + γ * ‖q‖ := by
    filter_upwards [hR i] with ω h
    refine (abs_add_le _ _).trans (add_le_add h ?_)
    rw [abs_mul, abs_of_nonneg hγ0]
    exact mul_le_mul_of_nonneg_left (hmax _) hγ0
  have hmean (i : Fin (n + 1)) :
      ∫ ω, f (D ω s a i) ∂μ = m.qBellmanOperator γ q s a := by
    have hsnd : AEMeasurable (fun ω => (D ω s a i).2) μ := (hmeas i).snd
    have hfst : Integrable (fun ω => (D ω s a i).1) μ :=
      Integrable.of_bound (hmeas i).fst.aestronglyMeasurable R
        (by simpa [Real.norm_eq_abs] using hR i)
    have hmaxi : Integrable (fun ω => qMax q (D ω s a i).2) μ :=
      Integrable.of_bound ((measurable_of_countable (qMax q)).comp_aemeasurable
        hsnd).aestronglyMeasurable ‖q‖ (Eventually.of_forall fun ω => by
          rw [Real.norm_eq_abs]
          exact hmax _)
    have hlawi : ∫ ω, qMax q (D ω s a i).2 ∂μ = expect (m.transition s a) (qMax q) := by
      rw [← integral_toMeasure_eq_expect, ← hlaw i,
        integral_map hsnd (measurable_of_countable (qMax q)).aestronglyMeasurable]
    simp only [f, qLearningTarget]
    rw [integral_add hfst (hmaxi.const_mul γ), integral_const_mul, hreward i, hlawi]
    rfl
  have h := measure_abs_sampleMean_sub_le_of_abs_le (X := fun i ω => f (D ω s a i))
    (hindep.comp (fun _ => f) (fun _ => hf)) (fun i => hf.comp_aemeasurable (hmeas i))
    (by positivity) hbound hmean hε
  simpa only [qBellmanOperator_ofSamples] using h

/-- **Uniform Hoeffding bound for the empirical Bellman Q operator.** Under the sampling
conditions of `measure_abs_ofSamples_qBellmanOperator_sub_le` at every state-action pair, and
for `ε > 0`, the empirical Bellman Q operator at a fixed table `q` deviates from the model's in
sup norm by at least `ε` with probability at most
`|S| * |A| * 2 * exp (-(n + 1) * ε ^ 2 / (2 * (R + γ * ‖q‖) ^ 2))`. -/
theorem measure_norm_ofSamples_qBellmanOperator_sub_le (m : MDP S A)
    (D : Ω → S → A → Fin (n + 1) → ℝ × S) {γ R : ℝ} (hγ0 : 0 ≤ γ) (hR0 : 0 < R)
    (q : S → A → ℝ)
    (hindep : ∀ s a, iIndepFun (fun i ω => D ω s a i) μ)
    (hmeas : ∀ s a i, AEMeasurable (fun ω => D ω s a i) μ)
    (hR : ∀ s a i, ∀ᵐ ω ∂μ, |(D ω s a i).1| ≤ R)
    (hreward : ∀ s a i, ∫ ω, (D ω s a i).1 ∂μ = m.reward s a)
    (hlaw : ∀ s a i, μ.map (fun ω => (D ω s a i).2) = (m.transition s a).toMeasure)
    {ε : ℝ} (hε : 0 < ε) :
    μ.real {ω | ε ≤ ‖(ofSamples (D ω)).qBellmanOperator γ q - m.qBellmanOperator γ q‖} ≤
      Fintype.card S * Fintype.card A *
        (2 * Real.exp (-((n + 1 : ℝ) * ε ^ 2) / (2 * (R + γ * ‖q‖) ^ 2))) := by
  set b := 2 * Real.exp (-((n + 1 : ℝ) * ε ^ 2) / (2 * (R + γ * ‖q‖) ^ 2))
  have hsub : {ω | ε ≤ ‖(ofSamples (D ω)).qBellmanOperator γ q - m.qBellmanOperator γ q‖} ⊆
      ⋃ p : S × A, {ω | ε ≤ |(ofSamples (D ω)).qBellmanOperator γ q p.1 p.2 -
        m.qBellmanOperator γ q p.1 p.2|} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω
    by_contra hnot
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, not_exists, not_le] at hnot
    have hlt : ‖(ofSamples (D ω)).qBellmanOperator γ q - m.qBellmanOperator γ q‖ < ε :=
      (pi_norm_lt_iff hε).2 fun s => (pi_norm_lt_iff hε).2 fun a => by
        rw [Real.norm_eq_abs]
        exact hnot (s, a)
    linarith
  refine (measureReal_mono hsub).trans ((measureReal_iUnion_fintype_le _).trans ?_)
  calc
    ∑ p : S × A, μ.real {ω | ε ≤ |(ofSamples (D ω)).qBellmanOperator γ q p.1 p.2 -
        m.qBellmanOperator γ q p.1 p.2|} ≤ ∑ _p : S × A, b :=
      Finset.sum_le_sum fun p _ => m.measure_abs_ofSamples_qBellmanOperator_sub_le D hγ0 hR0 q
        p.1 p.2 (hindep p.1 p.2) (hmeas p.1 p.2) (hR p.1 p.2) (hreward p.1 p.2) (hlaw p.1 p.2)
        hε.le
    _ = Fintype.card S * Fintype.card A * b := by
      simp [Finset.sum_const, Finset.card_univ, Fintype.card_prod]

end Rlib.MDP
