module

public import Rlib.MDP.ClippedSurrogate
public import Rlib.MDP.PolicyGradient

/-! # The trust-region policy improvement bound

Switching from `π` to `π'` gains at least the surrogate objective minus a penalty that grows with
how far the action probabilities of the two policies are apart. The penalty comes from a bound on
how much the discounted visitation can move.
-/

@[expose] public section

noncomputable section

namespace Rlib.MDP

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S]

omit [Fintype S] [DecidableEq S] in
/-- The changes in action probabilities between two policies sum to zero at every state. -/
theorem sum_toReal_sub_eq_zero (π π' : StationaryPolicy S A) (t : S) :
    ∑ a, ((π' t a).toReal - (π t a).toReal) = 0 := by
  rw [Finset.sum_sub_distrib, probability_sum, probability_sum, sub_self]

/-- **Change in discounted visitation.** Switching from `π` to `π'` changes the discounted
visitation of `s` by `γ` times the new visitation average of the change in action probabilities
weighted by the expected next value of the indicator reward of `s` under `π`. -/
theorem discountedVisitation_sub_eq (m : MDP S A) (π π' : StationaryPolicy S A) {γ : ℝ}
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (s₀ s : S) :
    m.discountedVisitation π' hγ0 hγ1 s₀ s - m.discountedVisitation π hγ0 hγ1 s₀ s =
      γ * ∑ t, m.discountedVisitation π' hγ0 hγ1 s₀ t *
        ∑ a, ((π' t a).toReal - (π t a).toReal) *
          expect (m.transition t a)
            ((m.withReward fun x _ => if x = s then 1 else 0).policyValue π hγ0 hγ1) := by
  set ms := m.withReward fun x _ => if x = s then (1 : ℝ) else 0
  set W := ms.policyValue π hγ0 hγ1
  have hpdl := ms.sub_policyValue_eq_sum_visitation π π' hγ0 hγ1 s₀
  simp only [show ∀ t, ms.discountedVisitation π' hγ0 hγ1 s₀ t =
    m.discountedVisitation π' hγ0 hγ1 s₀ t from fun t => rfl] at hpdl
  have hinner (t : S) : expect (π' t) (ms.advantage π hγ0 hγ1 t) =
      γ * ∑ a, ((π' t a).toReal - (π t a).toReal) * expect (m.transition t a) W := by
    rw [ms.expect_advantage_eq_sum_sub π π' hγ0 hγ1 t]
    have hA (a : A) : ms.advantage π hγ0 hγ1 t a =
        ((if t = s then 1 else 0) - W t) + γ * expect (m.transition t a) W := by
      simp only [advantage, policyActionValue, oneStepActionValue, ms, withReward, W]
      ring
    simp only [hA, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul,
      sum_toReal_sub_eq_zero π π' t, zero_mul, zero_add, Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => by ring
  simp only [hinner] at hpdl
  have hd : m.discountedVisitation π' hγ0 hγ1 s₀ s - m.discountedVisitation π hγ0 hγ1 s₀ s =
      (1 - γ) * (ms.policyValue π' hγ0 hγ1 s₀ - W s₀) := by
    simp only [discountedVisitation, ms, W]
    ring
  rw [hd, hpdl, Finset.mul_sum]
  exact Finset.sum_congr rfl fun t _ => by ring

/-- **Visitation is stable under small policy changes.** Switching from `π` to `π'` moves the
discounted visitation by at most `γ / (1 - γ)` times the new visitation average of the `ℓ¹`
distance between the action distributions. -/
theorem sum_abs_discountedVisitation_sub_le (m : MDP S A) (π π' : StationaryPolicy S A) {γ : ℝ}
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (s₀ : S) :
    ∑ s, |m.discountedVisitation π' hγ0 hγ1 s₀ s - m.discountedVisitation π hγ0 hγ1 s₀ s| ≤
      γ / (1 - γ) * ∑ t, m.discountedVisitation π' hγ0 hγ1 s₀ t *
        ∑ a, |(π' t a).toReal - (π t a).toReal| := by
  have hγ : 0 < 1 - γ := sub_pos.mpr hγ1
  set W : S → S → ℝ := fun s =>
    (m.withReward fun x _ => if x = s then 1 else 0).policyValue π hγ0 hγ1
  have hWnn (s x : S) : 0 ≤ W s x := by
    refine (m.withReward _).policyValue_nonneg π hγ0 hγ1 (fun y => ?_) x
    have h := expect_mono (π y) (f := fun _ => (0 : ℝ))
      (g := fun _ => if y = s then (1 : ℝ) else 0) fun a => by split_ifs <;> norm_num
    rw [expect_zero] at h
    exact h
  have hWsum (x : S) : ∑ s, W s x = 1 / (1 - γ) := by
    have h := m.sum_discountedVisitation π hγ0 hγ1 x
    simp only [discountedVisitation, ← Finset.mul_sum] at h
    rw [eq_div_iff hγ.ne']
    linarith
  have hE (t : S) (a : A) : ∑ s, expect (m.transition t a) (W s) = 1 / (1 - γ) := by
    rw [← expect_sum, show (fun x => ∑ s, W s x) = fun _ => 1 / (1 - γ) from funext hWsum,
      expect_const]
  have hEnn (s t : S) (a : A) : 0 ≤ expect (m.transition t a) (W s) := by
    have h := expect_mono (m.transition t a) (f := fun _ => (0 : ℝ)) (g := W s) (hWnn s)
    rwa [expect_zero] at h
  have hdnn (t : S) := m.discountedVisitation_nonneg π' hγ0 hγ1 s₀ t
  calc
    ∑ s, |m.discountedVisitation π' hγ0 hγ1 s₀ s - m.discountedVisitation π hγ0 hγ1 s₀ s| =
        ∑ s, |γ * ∑ t, m.discountedVisitation π' hγ0 hγ1 s₀ t *
          ∑ a, ((π' t a).toReal - (π t a).toReal) * expect (m.transition t a) (W s)| :=
      Finset.sum_congr rfl fun s _ => by rw [m.discountedVisitation_sub_eq π π' hγ0 hγ1 s₀ s]
    _ ≤ ∑ s, γ * ∑ t, m.discountedVisitation π' hγ0 hγ1 s₀ t *
          ∑ a, |(π' t a).toReal - (π t a).toReal| * expect (m.transition t a) (W s) := by
      refine Finset.sum_le_sum fun s _ => ?_
      rw [abs_mul, abs_of_nonneg hγ0]
      refine mul_le_mul_of_nonneg_left ?_ hγ0
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun t _ => ?_)
      rw [abs_mul, abs_of_nonneg (hdnn t)]
      refine mul_le_mul_of_nonneg_left ?_ (hdnn t)
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun a _ => ?_)
      rw [abs_mul, abs_of_nonneg (hEnn s t a)]
    _ = γ * ∑ t, m.discountedVisitation π' hγ0 hγ1 s₀ t *
          ∑ a, |(π' t a).toReal - (π t a).toReal| * ∑ s, expect (m.transition t a) (W s) := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [Finset.sum_comm]
    _ = γ / (1 - γ) * ∑ t, m.discountedVisitation π' hγ0 hγ1 s₀ t *
          ∑ a, |(π' t a).toReal - (π t a).toReal| := by
      simp only [hE, Finset.mul_sum]
      refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun a _ => ?_
      field_simp

/-- If the `ℓ¹` distance between the action distributions of `π` and `π'` is at most `δ` at
every state, switching policies moves the discounted visitation by at most `γ / (1 - γ) * δ`. -/
theorem sum_abs_discountedVisitation_sub_le_of_le (m : MDP S A) (π π' : StationaryPolicy S A)
    {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) {δ : ℝ}
    (hδ : ∀ t, ∑ a, |(π' t a).toReal - (π t a).toReal| ≤ δ) (s₀ : S) :
    ∑ s, |m.discountedVisitation π' hγ0 hγ1 s₀ s - m.discountedVisitation π hγ0 hγ1 s₀ s| ≤
      γ / (1 - γ) * δ := by
  have hγ : 0 < 1 - γ := sub_pos.mpr hγ1
  refine (m.sum_abs_discountedVisitation_sub_le π π' hγ0 hγ1 s₀).trans
    (mul_le_mul_of_nonneg_left ?_ (div_nonneg hγ0 hγ.le))
  calc
    ∑ t, m.discountedVisitation π' hγ0 hγ1 s₀ t * ∑ a, |(π' t a).toReal - (π t a).toReal| ≤
        ∑ t, m.discountedVisitation π' hγ0 hγ1 s₀ t * δ :=
      Finset.sum_le_sum fun t _ =>
        mul_le_mul_of_nonneg_left (hδ t) (m.discountedVisitation_nonneg π' hγ0 hγ1 s₀ t)
    _ = δ := by rw [← Finset.sum_mul, m.sum_discountedVisitation π' hγ0 hγ1 s₀, one_mul]

/-- **Trust-region policy improvement bound.** Suppose the expected advantage of `π` under `π'`
is at most `ε` in absolute value at every state, and the `ℓ¹` distance between the action
distributions of the two policies is at most `δ` at every state. Then `1 - γ` times the gain of
`π'` over `π` is at least the old policy's visitation average of the expected advantage minus
`γ / (1 - γ) * ε * δ`. -/
theorem policyValue_sub_ge (m : MDP S A) (π π' : StationaryPolicy S A) {γ : ℝ} (hγ0 : 0 ≤ γ)
    (hγ1 : γ < 1) {ε δ : ℝ} (hε : ∀ s, |expect (π' s) (m.advantage π hγ0 hγ1 s)| ≤ ε)
    (hδ : ∀ t, ∑ a, |(π' t a).toReal - (π t a).toReal| ≤ δ) (s₀ : S) :
    ∑ s, m.discountedVisitation π hγ0 hγ1 s₀ s * expect (π' s) (m.advantage π hγ0 hγ1 s) -
        γ / (1 - γ) * ε * δ ≤
      (1 - γ) * (m.policyValue π' hγ0 hγ1 s₀ - m.policyValue π hγ0 hγ1 s₀) := by
  have hγ : 0 < 1 - γ := sub_pos.mpr hγ1
  set g : S → ℝ := fun s => expect (π' s) (m.advantage π hγ0 hγ1 s)
  have hε0 : 0 ≤ ε := (abs_nonneg _).trans (hε s₀)
  rw [m.sub_policyValue_eq_sum_visitation π π' hγ0 hγ1 s₀]
  have hgap : |∑ s, (m.discountedVisitation π' hγ0 hγ1 s₀ s -
      m.discountedVisitation π hγ0 hγ1 s₀ s) * g s| ≤ γ / (1 - γ) * δ * ε := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc
      ∑ s, |(m.discountedVisitation π' hγ0 hγ1 s₀ s - m.discountedVisitation π hγ0 hγ1 s₀ s) *
          g s| ≤ ∑ s, |m.discountedVisitation π' hγ0 hγ1 s₀ s -
            m.discountedVisitation π hγ0 hγ1 s₀ s| * ε :=
        Finset.sum_le_sum fun s _ => by
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (hε s) (abs_nonneg _)
      _ ≤ γ / (1 - γ) * δ * ε := by
        rw [← Finset.sum_mul]
        exact mul_le_mul_of_nonneg_right
          (m.sum_abs_discountedVisitation_sub_le_of_le π π' hγ0 hγ1 hδ s₀) hε0
  have hsplit : ∑ s, m.discountedVisitation π' hγ0 hγ1 s₀ s * g s =
      ∑ s, m.discountedVisitation π hγ0 hγ1 s₀ s * g s +
        ∑ s, (m.discountedVisitation π' hγ0 hγ1 s₀ s -
          m.discountedVisitation π hγ0 hγ1 s₀ s) * g s := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun s _ => by ring
  rw [hsplit]
  have := neg_abs_le (∑ s, (m.discountedVisitation π' hγ0 hγ1 s₀ s -
    m.discountedVisitation π hγ0 hγ1 s₀ s) * g s)
  nlinarith

/-- **Trust-region bound for the surrogate objective.** If the old policy covers the support of
the new one, `1 - γ` times the gain of `π'` over `π` is at least the surrogate objective minus
`γ / (1 - γ) * ε * δ`. -/
theorem surrogate_sub_le (m : MDP S A) (π π' : StationaryPolicy S A) {γ : ℝ} (hγ0 : 0 ≤ γ)
    (hγ1 : γ < 1) (hsupp : ∀ s a, π' s a ≠ 0 → π s a ≠ 0) {ε δ : ℝ}
    (hε : ∀ s, |expect (π' s) (m.advantage π hγ0 hγ1 s)| ≤ ε)
    (hδ : ∀ t, ∑ a, |(π' t a).toReal - (π t a).toReal| ≤ δ) (s₀ : S) :
    m.surrogate π π' hγ0 hγ1 s₀ - γ / (1 - γ) * ε * δ ≤
      (1 - γ) * (m.policyValue π' hγ0 hγ1 s₀ - m.policyValue π hγ0 hγ1 s₀) := by
  rw [m.surrogate_eq π π' hγ0 hγ1 hsupp s₀]
  exact m.policyValue_sub_ge π π' hγ0 hγ1 hε hδ s₀

end Rlib.MDP
