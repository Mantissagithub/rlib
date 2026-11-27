module

public import Rlib.MDP.TrustRegion
public import Rlib.MDP.GradientDomination
public import Rlib.MDP.SoftmaxSmoothness

/-! # Conservative policy iteration

This file follows Agarwal, Jiang, Kakade, and Sun, Section 14.1, after Kakade and Langford (2002).
Conservative policy iteration (CPI) moves from `π` to the mixture `(1 - α) π + α π'`, which keeps
the discounted visitation close to that of `π`. Lemma 14.1 bounds how far it moves, and
Theorem 14.2 shows that the mixture improves on `π` whenever the expected advantage of `π'` under
the visitation of `π` is large enough.

Start states are drawn from a restart distribution `μ`. Rewards lie in `[0, 1]`.
-/

@[expose] public section

noncomputable section

namespace Rlib.MDP

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S]

/-- The mixture `(1 - α) π + α π'`: at every state, follow `π` with probability `1 - α` and `π'`
with probability `α`. Values of `α` outside `[0, 1]` are clamped to that interval. -/
def mixPolicy (α : ℝ) (π π' : StationaryPolicy S A) : StationaryPolicy S A := fun s =>
  PMF.ofFintype (fun a => ENNReal.ofReal (1 - max 0 (min α 1)) * π s a +
    ENNReal.ofReal (max 0 (min α 1)) * π' s a) (by
      have hp : ∑ a, π s a = 1 := by
        rw [← tsum_fintype (L := .unconditional A)]; exact (π s).tsum_coe
      have hq : ∑ a, π' s a = 1 := by
        rw [← tsum_fintype (L := .unconditional A)]; exact (π' s).tsum_coe
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hp, hq, mul_one, mul_one,
        ← ENNReal.ofReal_add (by simp) (by positivity)]
      simp)

omit [Fintype S] [DecidableEq S] in
theorem mixPolicy_toReal {α : ℝ} (hα : α ∈ Set.Icc (0 : ℝ) 1) (π π' : StationaryPolicy S A)
    (s : S) (a : A) :
    (mixPolicy α π π' s a).toReal = (1 - α) * (π s a).toReal + α * (π' s a).toReal := by
  have hc : max 0 (min α 1) = α := by
    rw [min_eq_left hα.2, max_eq_right hα.1]
  simp only [mixPolicy, PMF.ofFintype_apply, hc]
  rw [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ((π s).apply_ne_top a))
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ((π' s).apply_ne_top a)), ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by linarith [hα.2]), ENNReal.toReal_ofReal hα.1]

omit [Fintype S] [DecidableEq S] in
/-- Expectations under the mixture mix the expectations. -/
theorem expect_mixPolicy {α : ℝ} (hα : α ∈ Set.Icc (0 : ℝ) 1) (π π' : StationaryPolicy S A)
    (s : S) (f : A → ℝ) :
    expect (mixPolicy α π π' s) f = (1 - α) * expect (π s) f + α * expect (π' s) f := by
  simp only [expect, mixPolicy_toReal hα, Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun a _ => by ring

omit [DecidableEq S] in
/-- The expected advantage of `π` under the mixture is `α` times that under `π'`, since the
advantage of `π` averages to zero under `π`. -/
theorem expect_mixPolicy_advantage (m : MDP S A) {α : ℝ} (hα : α ∈ Set.Icc (0 : ℝ) 1)
    (π π' : StationaryPolicy S A) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (s : S) :
    expect (mixPolicy α π π' s) (m.advantage π hγ0 hγ1 s) =
      α * expect (π' s) (m.advantage π hγ0 hγ1 s) := by
  rw [expect_mixPolicy hα, m.expect_advantage π hγ0 hγ1 s, mul_zero, zero_add]

omit [Fintype S] [DecidableEq S] in
/-- **Lemma 14.1, first part.** The mixture is within `2 α` of `π` in `ℓ¹` at every state. -/
theorem sum_abs_mixPolicy_sub_le {α : ℝ} (hα : α ∈ Set.Icc (0 : ℝ) 1)
    (π π' : StationaryPolicy S A) (s : S) :
    ∑ a, |(mixPolicy α π π' s a).toReal - (π s a).toReal| ≤ 2 * α := by
  have h (a : A) : |(mixPolicy α π π' s a).toReal - (π s a).toReal| =
      α * |(π' s a).toReal - (π s a).toReal| := by
    rw [mixPolicy_toReal hα, show (1 - α) * (π s a).toReal + α * (π' s a).toReal -
      (π s a).toReal = α * ((π' s a).toReal - (π s a).toReal) by ring, abs_mul,
      abs_of_nonneg hα.1]
  simp only [h, ← Finset.mul_sum]
  have hle : ∑ a, |(π' s a).toReal - (π s a).toReal| ≤ 2 := by
    calc ∑ a, |(π' s a).toReal - (π s a).toReal|
        ≤ ∑ a, ((π' s a).toReal + (π s a).toReal) := Finset.sum_le_sum fun a _ => by
          rw [abs_le]; constructor <;> linarith [(π' s a).toReal_nonneg, (π s a).toReal_nonneg]
      _ = 2 := by rw [Finset.sum_add_distrib, probability_sum, probability_sum]; norm_num
  nlinarith [hα.1]

/-- **Lemma 14.1 (similar policies imply similar state visitations).** With start states drawn
from `μ`, the discounted visitations of the mixture and of `π` are within `2 α γ / (1 - γ)` in
`ℓ¹`. -/
theorem sum_abs_weightedVisitation_mixPolicy_sub_le (m : MDP S A) {α : ℝ}
    (hα : α ∈ Set.Icc (0 : ℝ) 1) (π π' : StationaryPolicy S A) {γ : ℝ} (hγ0 : 0 ≤ γ)
    (hγ1 : γ < 1) (μ : PMF S) :
    ∑ s, |m.weightedVisitation (mixPolicy α π π') hγ0 hγ1 (fun t => (μ t).toReal) s -
        m.weightedVisitation π hγ0 hγ1 (fun t => (μ t).toReal) s| ≤ 2 * α * γ / (1 - γ) := by
  have hγ : 0 < 1 - γ := sub_pos.mpr hγ1
  calc ∑ s, |m.weightedVisitation (mixPolicy α π π') hγ0 hγ1 (fun t => (μ t).toReal) s -
        m.weightedVisitation π hγ0 hγ1 (fun t => (μ t).toReal) s|
      = ∑ s, |∑ s₀, (μ s₀).toReal * (m.discountedVisitation (mixPolicy α π π') hγ0 hγ1 s₀ s -
          m.discountedVisitation π hγ0 hγ1 s₀ s)| := by
        simp only [weightedVisitation, ← Finset.sum_sub_distrib, mul_sub]
    _ ≤ ∑ s, ∑ s₀, (μ s₀).toReal * |m.discountedVisitation (mixPolicy α π π') hγ0 hγ1 s₀ s -
          m.discountedVisitation π hγ0 hγ1 s₀ s| := Finset.sum_le_sum fun s _ => by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
        simp only [abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
    _ = ∑ s₀, (μ s₀).toReal * ∑ s, |m.discountedVisitation (mixPolicy α π π') hγ0 hγ1 s₀ s -
          m.discountedVisitation π hγ0 hγ1 s₀ s| := by
        rw [Finset.sum_comm]; simp only [Finset.mul_sum]
    _ ≤ ∑ s₀, (μ s₀).toReal * (γ / (1 - γ) * (2 * α)) := Finset.sum_le_sum fun s₀ _ =>
        mul_le_mul_of_nonneg_left (m.sum_abs_discountedVisitation_sub_le_of_le π _ hγ0 hγ1
          (sum_abs_mixPolicy_sub_le hα π π') s₀) ENNReal.toReal_nonneg
    _ = 2 * α * γ / (1 - γ) := by
        rw [← Finset.sum_mul, probability_sum]; field_simp

/-- The expected advantage of `π` under `π'` along the visitation of `π` from `μ`:
`𝔸 = E_{s ∼ d^π_μ} E_{a ∼ π' (s)} A^π (s, a)`. -/
def visitationAdvantage (m : MDP S A) (π π' : StationaryPolicy S A) {γ : ℝ} (hγ0 : 0 ≤ γ)
    (hγ1 : γ < 1) (μ : PMF S) : ℝ :=
  ∑ s, m.weightedVisitation π hγ0 hγ1 (fun t => (μ t).toReal) s *
    expect (π' s) (m.advantage π hγ0 hγ1 s)

/-- **Theorem 14.2 (monotonic improvement in CPI).** Take rewards in `[0, 1]`, a restart
distribution `μ`, and `α ∈ [0, 1]`. Let `𝔸 = E_{s ∼ d^π_μ} E_{a ∼ π' (s)} A^π (s, a)`. Then the
mixture improves the `μ`-average value by at least `α / (1 - γ) * (𝔸 - 2 α γ / (1 - γ) ^ 2)`. -/
theorem expect_policyValue_mixPolicy_sub_ge (m : MDP S A)
    (hr : ∀ s a, m.reward s a ∈ Set.Icc (0 : ℝ) 1) {α : ℝ} (hα : α ∈ Set.Icc (0 : ℝ) 1)
    (π π' : StationaryPolicy S A) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (μ : PMF S) :
    α / (1 - γ) * (m.visitationAdvantage π π' hγ0 hγ1 μ - 2 * α * γ / (1 - γ) ^ 2) ≤
      expect μ (m.policyValue (mixPolicy α π π') hγ0 hγ1) -
        expect μ (m.policyValue π hγ0 hγ1) := by
  unfold visitationAdvantage
  have hγ : 0 < 1 - γ := sub_pos.mpr hγ1
  set g : S → ℝ := fun s => expect (π' s) (m.advantage π hγ0 hγ1 s)
  have hg (s : S) : |g s| ≤ 1 / (1 - γ) := by
    have hA := m.abs_advantage_le π hγ0 hγ1 hr s
    rw [abs_le]
    constructor
    · have := expect_mono (π' s) (f := fun _ => -(1 / (1 - γ)))
        (g := m.advantage π hγ0 hγ1 s) fun a => (abs_le.mp (hA a)).1
      rwa [expect_const] at this
    · have := expect_mono (π' s) (g := fun _ => 1 / (1 - γ))
        (f := m.advantage π hγ0 hγ1 s) fun a => (abs_le.mp (hA a)).2
      rwa [expect_const] at this
  have hε (s : S) : |expect (mixPolicy α π π' s) (m.advantage π hγ0 hγ1 s)| ≤ α / (1 - γ) := by
    rw [m.expect_mixPolicy_advantage hα π π' hγ0 hγ1 s, abs_mul, abs_of_nonneg hα.1]
    exact (mul_le_mul_of_nonneg_left (hg s) hα.1).trans (le_of_eq (by ring))
  have hstep (s₀ : S) := m.policyValue_sub_ge π (mixPolicy α π π') hγ0 hγ1 hε
    (sum_abs_mixPolicy_sub_le hα π π') s₀
  simp only [m.expect_mixPolicy_advantage hα π π' hγ0 hγ1] at hstep
  -- Average the per-state bound over `μ`.
  have havg : ∑ s₀, (μ s₀).toReal * (∑ s, m.discountedVisitation π hγ0 hγ1 s₀ s * (α * g s) -
      γ / (1 - γ) * (α / (1 - γ)) * (2 * α)) ≤ ∑ s₀, (μ s₀).toReal * ((1 - γ) *
      (m.policyValue (mixPolicy α π π') hγ0 hγ1 s₀ - m.policyValue π hγ0 hγ1 s₀)) :=
    Finset.sum_le_sum fun s₀ _ => mul_le_mul_of_nonneg_left (hstep s₀) ENNReal.toReal_nonneg
  set X : S → ℝ := fun s₀ => ∑ s, m.discountedVisitation π hγ0 hγ1 s₀ s * (α * g s)
  set c : ℝ := γ / (1 - γ) * (α / (1 - γ)) * (2 * α)
  have hL : ∑ s₀, (μ s₀).toReal * (X s₀ - c) = α * ∑ s, m.weightedVisitation π hγ0 hγ1
        (fun t => (μ t).toReal) s * g s - 2 * α ^ 2 * γ / (1 - γ) ^ 2 := by
    have h1 : ∑ s₀, (μ s₀).toReal * (X s₀ - c) = ∑ s₀, (μ s₀).toReal * X s₀ - c := by
      simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, probability_sum, one_mul]
    have h2 : ∑ s₀, (μ s₀).toReal * X s₀ = α * ∑ s, m.weightedVisitation π hγ0 hγ1
        (fun t => (μ t).toReal) s * g s := by
      simp only [X, weightedVisitation, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun s₀ _ => by ring
    have h3 : c = 2 * α ^ 2 * γ / (1 - γ) ^ 2 := by simp only [c]; field_simp
    rw [h1, h2, h3]
  have hR : ∑ s₀, (μ s₀).toReal * ((1 - γ) *
      (m.policyValue (mixPolicy α π π') hγ0 hγ1 s₀ - m.policyValue π hγ0 hγ1 s₀)) =
      (1 - γ) * (expect μ (m.policyValue (mixPolicy α π π') hγ0 hγ1) -
        expect μ (m.policyValue π hγ0 hγ1)) := by
    simp only [expect]
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    exact Finset.sum_congr rfl fun s₀ _ => by ring
  rw [hL, hR] at havg
  rw [div_mul_eq_mul_div, div_le_iff₀ hγ]
  have : α * (∑ s, m.weightedVisitation π hγ0 hγ1 (fun t => (μ t).toReal) s * g s -
      2 * α * γ / (1 - γ) ^ 2) = α * ∑ s, m.weightedVisitation π hγ0 hγ1
        (fun t => (μ t).toReal) s * g s - 2 * α ^ 2 * γ / (1 - γ) ^ 2 := by ring
  rw [this]
  linarith

/-- **Theorem 14.2, tuned step size.** With `γ > 0`, `𝔸 ≥ 0`, and the step
`α = 𝔸 (1 - γ) ^ 2 / (4 γ)` in `[0, 1]`, the mixture improves the `μ`-average value by at least
`𝔸 ^ 2 (1 - γ) / (8 γ)`. The book leaves `α ≤ 1` implicit. -/
theorem expect_policyValue_mixPolicy_sub_ge_sq (m : MDP S A)
    (hr : ∀ s a, m.reward s a ∈ Set.Icc (0 : ℝ) 1) (π π' : StationaryPolicy S A) {γ : ℝ}
    (hγ0 : 0 < γ) (hγ1 : γ < 1) (μ : PMF S) (hA : 0 ≤ m.visitationAdvantage π π' hγ0.le hγ1 μ)
    (hα1 : m.visitationAdvantage π π' hγ0.le hγ1 μ * (1 - γ) ^ 2 / (4 * γ) ≤ 1) :
    m.visitationAdvantage π π' hγ0.le hγ1 μ ^ 2 * (1 - γ) / (8 * γ) ≤
      expect μ (m.policyValue (mixPolicy (m.visitationAdvantage π π' hγ0.le hγ1 μ *
        (1 - γ) ^ 2 / (4 * γ)) π π') hγ0.le hγ1) - expect μ (m.policyValue π hγ0.le hγ1) := by
  set 𝔸 := m.visitationAdvantage π π' hγ0.le hγ1 μ
  have hγ : 0 < 1 - γ := sub_pos.mpr hγ1
  have hα : 𝔸 * (1 - γ) ^ 2 / (4 * γ) ∈ Set.Icc (0 : ℝ) 1 := ⟨by positivity, hα1⟩
  refine le_trans (le_of_eq ?_) (m.expect_policyValue_mixPolicy_sub_ge hr hα π π' hγ0.le hγ1 μ)
  field_simp
  ring
