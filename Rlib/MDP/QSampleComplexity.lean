module

public import Rlib.MDP.QConcentration
public import Rlib.MDP.QSimulation

/-! # Sample complexity of model-based Q-value estimation

Draw `n + 1` independent samples for each state-action pair, build the empirical MDP, and take
its Bellman Q fixed point. This estimates the model's Bellman Q fixed point to accuracy
`ε / (1 - γ)` with probability at least `1 - δ` once
`n + 1 ≥ 2 * R ^ 2 * log (2 * |S| * |A| / δ) / (ε ^ 2 * (1 - γ) ^ 2)`.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Rlib.MDP

variable {Ω S A : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [Fintype S] [Fintype A] [Nonempty A] [MeasurableSpace S] [MeasurableSingletonClass S]
  {n : ℕ}

omit [MeasurableSpace S] [MeasurableSingletonClass S] in
/-- With rewards bounded by `R ≥ 0` and a discount in `[0, 1)`, a Bellman Q fixed point is
bounded by `R / (1 - γ)` in sup norm. -/
theorem norm_le_of_qBellmanOperator_fixed (m : MDP S A) {γ R : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hR0 : 0 ≤ R) (hR : ∀ s a, |m.reward s a| ≤ R) {q : S → A → ℝ}
    (hq : m.qBellmanOperator γ q = q) : ‖q‖ ≤ R / (1 - γ) := by
  rw [le_div_iff₀ (sub_pos.mpr hγ1)]
  have hzero : m.qBellmanOperator γ 0 = m.reward := by
    funext s a
    have h0 : qMax (0 : S → A → ℝ) = 0 := by
      funext t
      simp [qMax]
    simp [qBellmanOperator, oneStepActionValue, h0, expect]
  have hr : ‖m.reward‖ ≤ R :=
    (pi_norm_le_iff_of_nonneg hR0).2 fun s => (pi_norm_le_iff_of_nonneg hR0).2 fun a => by
      rw [Real.norm_eq_abs]
      exact hR s a
  have hcontract := m.norm_qBellmanOperator_sub_le γ q 0
  rw [Real.norm_of_nonneg hγ0, sub_zero, hq, hzero] at hcontract
  have htri := norm_sub_norm_le q m.reward
  linarith

/-- **Probability of a large estimation error.** For `ε > 0`, the Bellman Q fixed point of the
empirical MDP is at least `ε / (1 - γ)` from the model's Bellman Q fixed point `q` with
probability at most `|S| * |A| * 2 * exp (-(n + 1) * ε ^ 2 / (2 * (R + γ * ‖q‖) ^ 2))`. -/
theorem measure_norm_ofSamples_fixed_sub_le (m : MDP S A)
    (D : Ω → S → A → Fin (n + 1) → ℝ × S) {γ R : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (hR0 : 0 < R)
    (hindep : ∀ s a, iIndepFun (fun i ω => D ω s a i) μ)
    (hmeas : ∀ s a i, AEMeasurable (fun ω => D ω s a i) μ)
    (hR : ∀ s a i, ∀ᵐ ω ∂μ, |(D ω s a i).1| ≤ R)
    (hreward : ∀ s a i, ∫ ω, (D ω s a i).1 ∂μ = m.reward s a)
    (hlaw : ∀ s a i, μ.map (fun ω => (D ω s a i).2) = (m.transition s a).toMeasure)
    {q : S → A → ℝ} (hq : m.qBellmanOperator γ q = q) (qhat : Ω → S → A → ℝ)
    (hqhat : ∀ ω, (ofSamples (D ω)).qBellmanOperator γ (qhat ω) = qhat ω)
    {ε : ℝ} (hε : 0 < ε) :
    μ.real {ω | ε / (1 - γ) ≤ ‖qhat ω - q‖} ≤
      Fintype.card S * Fintype.card A *
        (2 * Real.exp (-((n + 1 : ℝ) * ε ^ 2) / (2 * (R + γ * ‖q‖) ^ 2))) := by
  have hγ : 0 < 1 - γ := sub_pos.mpr hγ1
  refine (measureReal_mono fun ω hω => ?_).trans
    (m.measure_norm_ofSamples_qBellmanOperator_sub_le D hγ0 hR0 q hindep hmeas hR hreward hlaw
      hε)
  simp only [Set.mem_ofPred_eq] at hω ⊢
  have hsim := norm_sub_le_of_qBellmanOperator_fixed m (ofSamples (D ω)) hγ0 hγ1 hq (hqhat ω)
  exact (div_le_div_iff_of_pos_right hγ).1 (hω.trans hsim)

/-- **Sample complexity of model-based Q-value estimation.** Suppose each state-action pair has
`n + 1` independent samples whose rewards are bounded by `R > 0` with the model's mean and whose
successors follow the model's transition law. For a discount in `[0, 1)`, `ε > 0`, and
`δ > 0`, if `n + 1 ≥ 2 * R ^ 2 * log (2 * |S| * |A| / δ) / (ε ^ 2 * (1 - γ) ^ 2)`, then the
Bellman Q fixed point of the empirical MDP is within `ε / (1 - γ)` of the model's except with
probability at most `δ`. -/
theorem measure_norm_ofSamples_fixed_sub_le_of_le (m : MDP S A)
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
    μ.real {ω | ε / (1 - γ) ≤ ‖qhat ω - q‖} ≤ δ := by
  have hγ : 0 < 1 - γ := sub_pos.mpr hγ1
  set K : ℝ := Fintype.card S * Fintype.card A
  have hK0 : 0 ≤ K := by positivity
  refine (m.measure_norm_ofSamples_fixed_sub_le D hγ0 hγ1 hR0 hindep hmeas hR hreward hlaw hq
    qhat hqhat hε).trans ?_
  change K * _ ≤ δ
  rcases hK0.eq_or_lt with hK | hK
  · rw [← hK]
    simp only [zero_mul]
    exact hδ.le
  have hrew (s : S) (a : A) : |m.reward s a| ≤ R := by
    rw [← hreward s a 0]
    have h := norm_integral_le_of_norm_le_const (μ := μ) (f := fun ω => (D ω s a 0).1)
      (C := R) (by simpa only [Real.norm_eq_abs] using hR s a 0)
    simpa [Real.norm_eq_abs, probReal_univ] using h
  have hqR := m.norm_le_of_qBellmanOperator_fixed hγ0 hγ1 hR0.le hrew hq
  set c := R + γ * ‖q‖
  have hc0 : 0 < c := by positivity
  have hcR : c ≤ R / (1 - γ) := by
    have : γ * ‖q‖ ≤ γ * (R / (1 - γ)) := mul_le_mul_of_nonneg_left hqR hγ0
    have heq : R + γ * (R / (1 - γ)) = R / (1 - γ) := by
      field_simp
      ring
    linarith
  have hlog : Real.log (2 * K / δ) ≤ (n + 1 : ℝ) * ε ^ 2 / (2 * c ^ 2) := by
    have h1 : Real.log (2 * K / δ) ≤ (n + 1 : ℝ) * (ε ^ 2 * (1 - γ) ^ 2) / (2 * R ^ 2) := by
      rw [div_le_iff₀ (by positivity)] at hn
      rw [le_div_iff₀ (by positivity)]
      nlinarith
    refine h1.trans ?_
    have hsq : c ^ 2 ≤ (R / (1 - γ)) ^ 2 := pow_le_pow_left₀ hc0.le hcR 2
    rw [div_pow] at hsq
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hsq' : c ^ 2 * (1 - γ) ^ 2 ≤ R ^ 2 := by
      rwa [le_div_iff₀ (by positivity)] at hsq
    have hn0 : (0 : ℝ) ≤ (n + 1 : ℝ) * ε ^ 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hsq' (mul_nonneg hn0 (by norm_num : (0 : ℝ) ≤ 2))]
  have hexp : Real.exp (-((n + 1 : ℝ) * ε ^ 2) / (2 * c ^ 2)) ≤ δ / (2 * K) := by
    rw [neg_div, ← Real.exp_log (by positivity : 0 < δ / (2 * K))]
    apply Real.exp_le_exp.2
    have h2K : (2 * K) ≠ 0 := (by positivity : (0 : ℝ) < 2 * K).ne'
    rw [Real.log_div hδ.ne' h2K]
    linarith [show Real.log (2 * K / δ) = Real.log (2 * K) - Real.log δ from
      Real.log_div h2K hδ.ne']
  calc
    K * (2 * Real.exp (-((n + 1 : ℝ) * ε ^ 2) / (2 * c ^ 2))) ≤ K * (2 * (δ / (2 * K))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexp (by norm_num)) hK0
    _ = δ := by
      field_simp

end Rlib.MDP
