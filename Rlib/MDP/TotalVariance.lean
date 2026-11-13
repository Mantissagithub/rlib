module

public import Rlib.MDP.NaturalPolicyGradient

/-! # Total variance

This file follows Agarwal, Jiang, Kakade, and Sun, *Reinforcement Learning: Theory and
Algorithms*, Section 2.4.1. For `V ∈ ℝ^S`, `Var_P (V) (s, a)` is the variance of `V (s')` for
`s' ∼ P (· | s, a)`. Writing `(I - γ P^π)⁻¹ g` for the action values of `π` under reward `g`, their
Lemma 2.12 (weighted sum of deviations) states
`‖(I - γ P^π)⁻¹ √(Var_P (V^π))‖∞ ≤ √(2 / (1 - γ) ^ 3)` for rewards in `[0, 1]`.

Here `(I - γ P^π)⁻¹ Var_P (V^π) ≤ 1 / (1 - γ) ^ 2` is proved directly, by checking that
`1 / (1 - γ) ^ 2 - (P V^π) ^ 2` is a supersolution of the Bellman equation for the reward
`Var_P (V^π)`. Jensen's inequality, applied one step at a time, then gives
`(I - γ P^π)⁻¹ √(Var_P (V^π)) ≤ √(1 / (1 - γ) ^ 3)`, which implies the book's bound.
-/

@[expose] public section

noncomputable section

namespace Rlib

variable {X : Type*} [Fintype X]

/-- The square of an expectation is at most the expectation of the square. -/
theorem sq_expect_le_expect_sq (p : PMF X) (f : X → ℝ) :
    expect p f ^ 2 ≤ expect p (fun x => f x ^ 2) := by
  set c := expect p f
  have h0 : 0 ≤ expect p (fun x => (f x - c) ^ 2) :=
    Finset.sum_nonneg fun x _ => mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _)
  have hexp : expect p (fun x => (f x - c) ^ 2) = expect p (fun x => f x ^ 2) - c ^ 2 := by
    have hterm (x : X) : (p x).toReal * (f x - c) ^ 2 =
        (p x).toReal * f x ^ 2 - 2 * c * ((p x).toReal * f x) + c ^ 2 * (p x).toReal := by ring
    simp only [expect, hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      probability_sum]
    simp only [c, expect]
    ring
  linarith

/-- **Jensen's inequality for the square root.** -/
theorem expect_sqrt_le (p : PMF X) {f : X → ℝ} (hf : ∀ x, 0 ≤ f x) :
    expect p (fun x => Real.sqrt (f x)) ≤ Real.sqrt (expect p f) := by
  have h := sq_expect_le_expect_sq p (fun x => Real.sqrt (f x))
  simp only [Real.sq_sqrt (hf _)] at h
  exact Real.le_sqrt_of_sq_le h

namespace MDP

variable {S A : Type*} [Fintype S] [Fintype A]

/-- The variance of `v (s')` for `s' ∼ P (· | s, a)`. -/
def transitionVar (m : MDP S A) (v : S → ℝ) (s : S) (a : A) : ℝ :=
  expect (m.transition s a) (fun s' => v s' ^ 2) - expect (m.transition s a) v ^ 2

omit [Fintype A] in
/-- Variances are nonnegative. -/
theorem transitionVar_nonneg (m : MDP S A) (v : S → ℝ) (s : S) (a : A) :
    0 ≤ m.transitionVar v s a :=
  sub_nonneg.mpr (sq_expect_le_expect_sq _ v)

/-- **Comparison for action values.** If `w` satisfies `g + γ P (π w) ≤ w`, then the action
values of `π` under reward `g`, `(I - γ P^π)⁻¹ g`, are at most `w`. -/
theorem policyActionValue_withReward_le (m : MDP S A) (π : StationaryPolicy S A) {γ : ℝ}
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (g w : S → A → ℝ)
    (hw : ∀ s a, g s a + γ * expect (m.transition s a) (fun s' => expect (π s') (w s')) ≤ w s a)
    (s : S) (a : A) : (m.withReward g).policyActionValue π hγ0 hγ1 s a ≤ w s a := by
  set V := (m.withReward g).policyValue π hγ0 hγ1
  set W : S → ℝ := fun s' => expect (π s') (w s')
  have hVW : ∀ s', V s' ≤ W s' := by
    have : Nonempty S := ⟨s⟩
    obtain ⟨t, ht⟩ := Finite.exists_max fun s' => V s' - W s'
    suffices h : V t - W t ≤ 0 from fun s' => by linarith [ht s']
    have hfix : (m.withReward g).oneStepValue π γ V t = V t :=
      congrFun ((m.withReward g).oneStepValue_policyValue π hγ0 hγ1) t
    have hWt : expect (π t) (fun a => g t a + γ * expect (m.transition t a) W) ≤ W t :=
      expect_mono _ fun a => hw t a
    have hdiff : expect (π t) (fun a => g t a + γ * expect (m.transition t a) V) -
        expect (π t) (fun a => g t a + γ * expect (m.transition t a) W) ≤ γ * (V t - W t) := by
      rw [← expect_sub]
      refine le_trans (expect_mono _ fun a => ?_) (expect_const _ _).le
      have hE : expect (m.transition t a) V - expect (m.transition t a) W ≤ V t - W t := by
        rw [← expect_sub]
        exact (expect_mono _ fun s' => ht s').trans (expect_const _ _).le
      nlinarith [mul_le_mul_of_nonneg_left hE hγ0]
    change expect (π t) (fun a => g t a + γ * expect (m.transition t a) V) = V t at hfix
    nlinarith [sub_pos.mpr hγ1]
  have hQ : (m.withReward g).policyActionValue π hγ0 hγ1 s a =
      g s a + γ * expect (m.transition s a) V := rfl
  rw [hQ]
  refine le_trans ?_ (hw s a)
  have := mul_le_mul_of_nonneg_left (expect_mono (m.transition s a) hVW) hγ0
  linarith

/-- **Total variance.** With rewards in `[0, 1]`, the action values of `π` under the reward
`Var_P (V^π)` are at most `1 / (1 - γ) ^ 2`. -/
theorem policyActionValue_withReward_transitionVar_le (m : MDP S A) (π : StationaryPolicy S A)
    {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (hr : ∀ s a, m.reward s a ∈ Set.Icc (0 : ℝ) 1)
    (s : S) (a : A) :
    (m.withReward (m.transitionVar (m.policyValue π hγ0 hγ1))).policyActionValue π hγ0 hγ1 s a ≤
      1 / (1 - γ) ^ 2 := by
  have hγ : 0 < 1 - γ := sub_pos.mpr hγ1
  set V := m.policyValue π hγ0 hγ1
  set c := 1 / (1 - γ) ^ 2
  set x : S → A → ℝ := fun s a => expect (m.transition s a) V
  have hV0 (s : S) : 0 ≤ V s := (m.policyValue_mem_Icc π hγ0 hγ1 hr s).1
  have hx0 (s : S) (a : A) : 0 ≤ x s a := by
    have h := expect_mono (m.transition s a) (f := fun _ => 0) (g := V) hV0
    rwa [expect_zero] at h
  -- Pointwise, `V (s') ^ 2 - γ * E_π [x ^ 2] ≤ 1 / (1 - γ)`.
  have hpt (s' : S) : V s' ^ 2 - γ * expect (π s') (fun a' => x s' a' ^ 2) ≤ 1 / (1 - γ) := by
    have hfix : expect (π s') (fun a' => m.reward s' a' + γ * x s' a') = V s' :=
      congrFun (m.oneStepValue_policyValue π hγ0 hγ1) s'
    have hjen := sq_expect_le_expect_sq (π s') (fun a' => m.reward s' a' + γ * x s' a')
    rw [hfix] at hjen
    have hbound (a' : A) : (m.reward s' a' + γ * x s' a') ^ 2 - γ * x s' a' ^ 2 ≤ 1 / (1 - γ) := by
      have hr0 := (hr s' a').1
      have hr1 := (hr s' a').2
      have hx := hx0 s' a'
      have hsq : 0 ≤ γ * (1 - γ) * (x s' a' - 1 / (1 - γ)) ^ 2 :=
        mul_nonneg (mul_nonneg hγ0 hγ.le) (sq_nonneg _)
      have hexp : γ * (1 - γ) * (x s' a' - 1 / (1 - γ)) ^ 2 =
          γ * (1 - γ) * x s' a' ^ 2 - 2 * γ * x s' a' + γ / (1 - γ) := by
        field_simp; ring
      have hone : 1 / (1 - γ) = 1 + γ / (1 - γ) := by field_simp; ring
      have hr2 : m.reward s' a' ^ 2 ≤ 1 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_right hr1 (mul_nonneg hγ0 hx)]
    have h := expect_mono (π s') (f := fun a' => (m.reward s' a' + γ * x s' a') ^ 2 -
      γ * x s' a' ^ 2) (g := fun _ => 1 / (1 - γ)) hbound
    rw [expect_const] at h
    have hsplit : expect (π s') (fun a' => (m.reward s' a' + γ * x s' a') ^ 2 -
        γ * x s' a' ^ 2) = expect (π s') (fun a' => (m.reward s' a' + γ * x s' a') ^ 2) -
          γ * expect (π s') (fun a' => x s' a' ^ 2) := by
      rw [expect_sub, expect_mul]
    linarith
  refine (m.policyActionValue_withReward_le π hγ0 hγ1 _ (fun s a => c - x s a ^ 2)
    (fun s a => ?_) s a).trans (by have := sq_nonneg (x s a); linarith)
  -- Check the supersolution inequality.
  have hπw (s' : S) : expect (π s') (fun a' => c - x s' a' ^ 2) =
      c - expect (π s') (fun a' => x s' a' ^ 2) := by
    rw [expect_sub, expect_const]
  simp only [hπw]
  have h := expect_mono (m.transition s a)
    (f := fun s' => V s' ^ 2 - γ * expect (π s') (fun a' => x s' a' ^ 2))
    (g := fun _ => 1 / (1 - γ)) hpt
  rw [expect_const] at h
  have hsplit : expect (m.transition s a) (fun s' => c - expect (π s') (fun a' => x s' a' ^ 2)) =
      c - expect (m.transition s a) (fun s' => expect (π s') (fun a' => x s' a' ^ 2)) := by
    rw [expect_sub, expect_const]
  have hsplit2 : expect (m.transition s a)
      (fun s' => V s' ^ 2 - γ * expect (π s') (fun a' => x s' a' ^ 2)) =
      expect (m.transition s a) (fun s' => V s' ^ 2) -
        γ * expect (m.transition s a) (fun s' => expect (π s') (fun a' => x s' a' ^ 2)) := by
    rw [expect_sub, expect_mul]
  rw [hsplit]
  simp only [transitionVar]
  change expect (m.transition s a) (fun s' => V s' ^ 2) - x s a ^ 2 + _ ≤ _
  have hc : (1 - γ) * c = 1 / (1 - γ) := by simp only [c]; field_simp
  nlinarith

/-- **Weighted sum of deviations, sharp form.** With rewards in `[0, 1]`, the action values of
`π` under the reward `√(Var_P (V^π))` are at most `√(1 / (1 - γ) ^ 3)`. -/
theorem policyActionValue_withReward_sqrt_transitionVar_le (m : MDP S A)
    (π : StationaryPolicy S A) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hr : ∀ s a, m.reward s a ∈ Set.Icc (0 : ℝ) 1) (s : S) (a : A) :
    (m.withReward fun s a => Real.sqrt (m.transitionVar (m.policyValue π hγ0 hγ1) s a)
      ).policyActionValue π hγ0 hγ1 s a ≤ Real.sqrt (1 / (1 - γ) ^ 3) := by
  have hγ : 0 < 1 - γ := sub_pos.mpr hγ1
  set V := m.policyValue π hγ0 hγ1
  set v := m.transitionVar V
  set mv := m.withReward v
  set Q := mv.policyActionValue π hγ0 hγ1
  set Vv := mv.policyValue π hγ0 hγ1
  have hv0 (s : S) (a : A) : 0 ≤ v s a := m.transitionVar_nonneg V s a
  have hVv0 (s : S) : 0 ≤ Vv s := mv.policyValue_nonneg π hγ0 hγ1 (fun t => by
    have h := expect_mono (π t) (f := fun _ => 0) (g := v t) (hv0 t)
    rwa [expect_zero] at h) s
  have hQ (s : S) (a : A) : Q s a = v s a + γ * expect (m.transition s a) Vv := rfl
  have hQ0 (s : S) (a : A) : 0 ≤ Q s a := by
    rw [hQ]
    have h := expect_mono (m.transition s a) (f := fun _ => 0) (g := Vv) hVv0
    rw [expect_zero] at h
    exact add_nonneg (hv0 s a) (mul_nonneg hγ0 h)
  have hπQ (s' : S) : expect (π s') (Q s') = Vv s' := mv.expect_policyActionValue π hγ0 hγ1 s'
  set h : S → A → ℝ := fun s a => Real.sqrt (Q s a / (1 - γ))
  have hsuper (s : S) (a : A) : Real.sqrt (v s a) +
      γ * expect (m.transition s a) (fun s' => expect (π s') (h s')) ≤ h s a := by
    have hstep1 (s' : S) : expect (π s') (h s') ≤ Real.sqrt (Vv s' / (1 - γ)) := by
      have hj := expect_sqrt_le (π s') (f := fun a' => Q s' a' / (1 - γ))
        fun a' => div_nonneg (hQ0 s' a') hγ.le
      rw [expect_div, hπQ] at hj
      exact hj
    set Y := expect (m.transition s a) Vv
    have hY0 : 0 ≤ Y := by
      have h := expect_mono (m.transition s a) (f := fun _ => 0) (g := Vv) hVv0
      rwa [expect_zero] at h
    have hstep2 : expect (m.transition s a) (fun s' => expect (π s') (h s')) ≤
        Real.sqrt (Y / (1 - γ)) := by
      refine (expect_mono _ hstep1).trans ?_
      have hj := expect_sqrt_le (m.transition s a) (f := fun s' => Vv s' / (1 - γ))
        fun s' => div_nonneg (hVv0 s') hγ.le
      rwa [expect_div] at hj
    refine le_trans (add_le_add_right (mul_le_mul_of_nonneg_left hstep2 hγ0) _) ?_
    simp only [h, hQ]
    set α := Real.sqrt (v s a)
    set β := Real.sqrt (Y / (1 - γ))
    have hα : α ^ 2 = v s a := Real.sq_sqrt (hv0 s a)
    have hβ : β ^ 2 = Y / (1 - γ) := Real.sq_sqrt (div_nonneg hY0 hγ.le)
    have hα0 : 0 ≤ α := Real.sqrt_nonneg _
    have hβ0 : 0 ≤ β := Real.sqrt_nonneg _
    apply Real.le_sqrt_of_sq_le
    have hY : Y = (1 - γ) * β ^ 2 := by rw [hβ]; field_simp
    rw [← hα]
    change (α + γ * β) ^ 2 ≤ (α ^ 2 + γ * Y) / (1 - γ)
    rw [hY, le_div_iff₀ hγ]
    nlinarith [mul_nonneg hγ0 (sq_nonneg (α - (1 - γ) * β))]
  refine (m.policyActionValue_withReward_le π hγ0 hγ1 _ h hsuper s a).trans ?_
  apply Real.sqrt_le_sqrt
  have hQc := m.policyActionValue_withReward_transitionVar_le π hγ0 hγ1 hr s a
  calc Q s a / (1 - γ) ≤ 1 / (1 - γ) ^ 2 / (1 - γ) :=
        div_le_div_of_nonneg_right hQc hγ.le
    _ = 1 / (1 - γ) ^ 3 := by field_simp

/-- **Weighted sum of deviations (Agarwal, Jiang, Kakade, and Sun, Lemma 2.12).** With rewards
in `[0, 1]`, `(I - γ P^π)⁻¹ √(Var_P (V^π)) ≤ √(2 / (1 - γ) ^ 3)`. -/
theorem policyActionValue_withReward_sqrt_transitionVar_le_two (m : MDP S A)
    (π : StationaryPolicy S A) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hr : ∀ s a, m.reward s a ∈ Set.Icc (0 : ℝ) 1) (s : S) (a : A) :
    (m.withReward fun s a => Real.sqrt (m.transitionVar (m.policyValue π hγ0 hγ1) s a)
      ).policyActionValue π hγ0 hγ1 s a ≤ Real.sqrt (2 / (1 - γ) ^ 3) := by
  have hγ : 0 < 1 - γ := sub_pos.mpr hγ1
  refine (m.policyActionValue_withReward_sqrt_transitionVar_le π hγ0 hγ1 hr s a).trans ?_
  exact Real.sqrt_le_sqrt (div_le_div_of_nonneg_right (by norm_num) (by positivity))

end MDP

end Rlib
