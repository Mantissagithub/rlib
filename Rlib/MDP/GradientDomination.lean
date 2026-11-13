module

public import Rlib.MDP.SoftmaxSmoothness
public import Mathlib.Algebra.Order.Chebyshev

/-! # Gradient domination for softmax policies

Start states are weighted by `μ`. The gradient of the weighted value with respect to the softmax
score of action `a` at state `s` is `(1 - γ)⁻¹ * d s * π a * A s a`, where `d` is the
`μ`-weighted discounted visitation. If a deterministic comparison policy `b` keeps probability at
least `c` under `π`, and its `ρ`-weighted visitation is at most `C` times `d`, then its value
gain over `π` under `ρ` is at most `C / c` times the sum over states of the gradient entries at
`b`. So a policy with a small gradient is close to `b`.
-/

@[expose] public section

noncomputable section

namespace Rlib.MDP

variable {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]

/-- The discounted visitation of `π` with start states weighted by `μ`. -/
def weightedVisitation (m : MDP S A) (π : StationaryPolicy S A) {γ : ℝ} (hγ0 : 0 ≤ γ)
    (hγ1 : γ < 1) (μ : S → ℝ) (s : S) : ℝ :=
  ∑ s₀, μ s₀ * m.discountedVisitation π hγ0 hγ1 s₀ s

/-- The gradient of the `μ`-weighted value of a softmax policy with respect to the score of
action `a` at state `s`. -/
def softmaxGradient (m : MDP S A) (π : StationaryPolicy S A) {γ : ℝ} (hγ0 : 0 ≤ γ)
    (hγ1 : γ < 1) (μ : S → ℝ) (s : S) (a : A) : ℝ :=
  (1 - γ)⁻¹ * m.weightedVisitation π hγ0 hγ1 μ s * (π s a).toReal * m.advantage π hγ0 hγ1 s a

/-- The `μ`-weighted directional derivative pairs the gradient with the direction. -/
theorem sum_directionalGain_eq (m : MDP S A) (π : StationaryPolicy S A) {γ : ℝ} (hγ0 : 0 ≤ γ)
    (hγ1 : γ < 1) (μ : S → ℝ) (u : S → A → ℝ) :
    ∑ s₀, μ s₀ * ((1 - γ)⁻¹ * m.directionalGain π hγ0 hγ1 u s₀) =
      ∑ s, ∑ a, m.softmaxGradient π hγ0 hγ1 μ s a * u s a := by
  simp only [directionalGain, softmaxGradient, weightedVisitation, Finset.mul_sum,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun s₀ _ => by ring

/-- The `ρ`-weighted gain of a deterministic policy `b` over `π`, through visitation of `b`. -/
theorem sum_sub_policyValue_eq (m : MDP S A) (π : StationaryPolicy S A) {γ : ℝ} (hγ0 : 0 ≤ γ)
    (hγ1 : γ < 1) (b : S → A) (ρ : S → ℝ) :
    (1 - γ) * ∑ s₀, ρ s₀ * (m.policyValue (fun s => PMF.pure (b s)) hγ0 hγ1 s₀ -
        m.policyValue π hγ0 hγ1 s₀) =
      ∑ s, m.weightedVisitation (fun s => PMF.pure (b s)) hγ0 hγ1 ρ s *
        m.advantage π hγ0 hγ1 s (b s) := by
  simp only [Finset.mul_sum, weightedVisitation, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s₀ _ => ?_
  rw [mul_left_comm, m.sub_policyValue_eq_sum_visitation π _ hγ0 hγ1 s₀, Finset.mul_sum]
  exact Finset.sum_congr rfl fun s _ => by rw [expect_pure]; ring

/-- **Gradient domination.** Weight start states by `μ ≥ 0` for the gradient and by `ρ` for the
comparison. If the deterministic policy `b` has probability at least `c > 0` under `π` at every
state, and its `ρ`-weighted visitation is at most `C` times the `μ`-weighted visitation of `π`,
then its `ρ`-weighted gain over `π` is at most `C / c` times the sum of the gradient entries at
`b` in absolute value. -/
theorem sum_sub_policyValue_le_sum_abs_softmaxGradient (m : MDP S A)
    (π : StationaryPolicy S A) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) {μ ρ : S → ℝ}
    (hμ : ∀ s, 0 ≤ μ s) (hρ : ∀ s, 0 ≤ ρ s) (b : S → A) {c C : ℝ} (hc : 0 < c)
    (hπ : ∀ s, c ≤ (π s (b s)).toReal)
    (hC : ∀ s, m.weightedVisitation (fun s => PMF.pure (b s)) hγ0 hγ1 ρ s ≤
      C * m.weightedVisitation π hγ0 hγ1 μ s) :
    ∑ s₀, ρ s₀ * (m.policyValue (fun s => PMF.pure (b s)) hγ0 hγ1 s₀ -
        m.policyValue π hγ0 hγ1 s₀) ≤
      C / c * ∑ s, |m.softmaxGradient π hγ0 hγ1 μ s (b s)| := by
  have hγ : 0 < 1 - γ := sub_pos.mpr hγ1
  set Db := m.weightedVisitation (fun s => PMF.pure (b s)) hγ0 hγ1 ρ
  set Dμ := m.weightedVisitation π hγ0 hγ1 μ
  set Ad := m.advantage π hγ0 hγ1
  have hDb (s : S) : 0 ≤ Db s := Finset.sum_nonneg fun s₀ _ =>
    mul_nonneg (hρ s₀) (m.discountedVisitation_nonneg _ hγ0 hγ1 s₀ s)
  have hDμ (s : S) : 0 ≤ Dμ s := Finset.sum_nonneg fun s₀ _ =>
    mul_nonneg (hμ s₀) (m.discountedVisitation_nonneg _ hγ0 hγ1 s₀ s)
  have hG (s : S) : |m.softmaxGradient π hγ0 hγ1 μ s (b s)| =
      (1 - γ)⁻¹ * (Dμ s * (π s (b s)).toReal * |Ad s (b s)|) := by
    simp only [softmaxGradient, abs_mul, abs_inv, abs_of_pos hγ, abs_of_nonneg (hDμ s),
      abs_of_nonneg (ENNReal.toReal_nonneg : 0 ≤ (π s (b s)).toReal), Dμ, Ad]
    ring
  have hterm (s : S) : Db s * Ad s (b s) ≤ C / c * (Dμ s * (π s (b s)).toReal * |Ad s (b s)|) := by
    calc Db s * Ad s (b s) ≤ Db s * |Ad s (b s)| :=
          mul_le_mul_of_nonneg_left (le_abs_self _) (hDb s)
      _ ≤ C * Dμ s * |Ad s (b s)| := mul_le_mul_of_nonneg_right (hC s) (abs_nonneg _)
      _ ≤ C * Dμ s * |Ad s (b s)| * ((π s (b s)).toReal / c) := by
          refine le_mul_of_one_le_right ?_ ((one_le_div hc).mpr (hπ s))
          exact mul_nonneg ((hDb s).trans (hC s)) (abs_nonneg _)
      _ = C / c * (Dμ s * (π s (b s)).toReal * |Ad s (b s)|) := by ring
  have hsum := m.sum_sub_policyValue_eq π hγ0 hγ1 b ρ
  have hle : (1 - γ) * ∑ s₀, ρ s₀ * (m.policyValue (fun s => PMF.pure (b s)) hγ0 hγ1 s₀ -
      m.policyValue π hγ0 hγ1 s₀) ≤
      (1 - γ) * (C / c * ∑ s, |m.softmaxGradient π hγ0 hγ1 μ s (b s)|) := by
    rw [hsum]
    calc _ ≤ ∑ s, C / c * (Dμ s * (π s (b s)).toReal * |Ad s (b s)|) :=
          Finset.sum_le_sum fun s _ => hterm s
      _ = _ := by
          simp only [hG, ← Finset.mul_sum]
          field_simp
  exact le_of_mul_le_mul_left hle hγ

/-- Squared form of gradient domination: when the gain of `b` is nonnegative, its square is at
most `(C / c) ^ 2 * |S|` times the squared length of the gradient. -/
theorem sq_sum_sub_policyValue_le (m : MDP S A)
    (π : StationaryPolicy S A) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) {μ ρ : S → ℝ}
    (hμ : ∀ s, 0 ≤ μ s) (hρ : ∀ s, 0 ≤ ρ s) (b : S → A) {c C : ℝ} (hc : 0 < c) (hC0 : 0 ≤ C)
    (hπ : ∀ s, c ≤ (π s (b s)).toReal)
    (hC : ∀ s, m.weightedVisitation (fun s => PMF.pure (b s)) hγ0 hγ1 ρ s ≤
      C * m.weightedVisitation π hγ0 hγ1 μ s)
    (hgap : 0 ≤ ∑ s₀, ρ s₀ * (m.policyValue (fun s => PMF.pure (b s)) hγ0 hγ1 s₀ -
        m.policyValue π hγ0 hγ1 s₀)) :
    (∑ s₀, ρ s₀ * (m.policyValue (fun s => PMF.pure (b s)) hγ0 hγ1 s₀ -
        m.policyValue π hγ0 hγ1 s₀)) ^ 2 ≤
      (C / c) ^ 2 * Fintype.card S *
        ∑ s, ∑ a, m.softmaxGradient π hγ0 hγ1 μ s a ^ 2 := by
  set G := m.softmaxGradient π hγ0 hγ1 μ
  have h := m.sum_sub_policyValue_le_sum_abs_softmaxGradient π hγ0 hγ1 hμ hρ b hc hπ hC
  have hcs : (∑ s, |G s (b s)|) ^ 2 ≤ Fintype.card S * ∑ s, |G s (b s)| ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun s => |G s (b s)|)
    simpa using this
  have hsq (s : S) : |G s (b s)| ^ 2 ≤ ∑ a, G s a ^ 2 := by
    rw [sq_abs]
    exact Finset.single_le_sum (f := fun a => G s a ^ 2) (fun a _ => sq_nonneg _)
      (Finset.mem_univ (b s))
  have hCc : 0 ≤ C / c := div_nonneg hC0 hc.le
  calc _ ≤ (C / c * ∑ s, |G s (b s)|) ^ 2 := pow_le_pow_left₀ hgap h 2
    _ = (C / c) ^ 2 * (∑ s, |G s (b s)|) ^ 2 := by ring
    _ ≤ (C / c) ^ 2 * (Fintype.card S * ∑ s, ∑ a, G s a ^ 2) := by
        refine mul_le_mul_of_nonneg_left (hcs.trans ?_) (sq_nonneg _)
        exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun s _ => hsq s) (by positivity)
    _ = _ := by ring

end Rlib.MDP
