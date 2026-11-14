module

public import Rlib.MDP.MinimaxEstimation

/-! # Minimax sample complexity of model-based Q estimation

This file completes the proof of Agarwal, Jiang, Kakade, and Sun, *Reinforcement Learning: Theory
and Algorithms*, Theorem 2.6 (value estimation). It collects the facts about the action values
`(I - γ P^π)⁻¹ g` of a fixed policy, the variance transfer of their Lemma 2.13, and the final
bound with explicit constants.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Rlib

/-- The square root is subadditive on nonnegative reals. -/
theorem sqrt_add_le_add_sqrt {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt (x + y) ≤ Real.sqrt x + Real.sqrt y := by
  have h : x + y ≤ (Real.sqrt x + Real.sqrt y) ^ 2 := by
    nlinarith [Real.sq_sqrt hx, Real.sq_sqrt hy, Real.sqrt_nonneg x, Real.sqrt_nonneg y,
      mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg y)]
  calc Real.sqrt (x + y) ≤ Real.sqrt ((Real.sqrt x + Real.sqrt y) ^ 2) := Real.sqrt_le_sqrt h
    _ = _ := Real.sqrt_sq (by positivity)

namespace MDP

variable {S A : Type*} [Fintype S] [Fintype A]

/-- The action values `(I - γ P^π)⁻¹ g` satisfy `Q = g + γ P (π Q)`. -/
theorem policyActionValue_withReward_eq (m : MDP S A) (π : StationaryPolicy S A) {γ : ℝ}
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (g : S → A → ℝ) (s : S) (a : A) :
    (m.withReward g).policyActionValue π hγ0 hγ1 s a = g s a + γ * expect (m.transition s a)
      (fun s' => expect (π s') ((m.withReward g).policyActionValue π hγ0 hγ1 s')) := by
  simp only [(m.withReward g).expect_policyActionValue π hγ0 hγ1]
  rfl

/-- **Linear bounds pass through `(I - γ P^π)⁻¹`.** If `|g| ≤ α * h + β` with `α ≥ 0`, then
`|(I - γ P^π)⁻¹ g| ≤ α * (I - γ P^π)⁻¹ h + β / (1 - γ)`. -/
theorem abs_policyActionValue_withReward_le (m : MDP S A) (π : StationaryPolicy S A) {γ : ℝ}
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) {g h : S → A → ℝ} {α β : ℝ} (hα : 0 ≤ α)
    (hg : ∀ s a, |g s a| ≤ α * h s a + β) (s : S) (a : A) :
    |(m.withReward g).policyActionValue π hγ0 hγ1 s a| ≤
      α * (m.withReward h).policyActionValue π hγ0 hγ1 s a + β / (1 - γ) := by
  have hγ : 0 < 1 - γ := sub_pos.mpr hγ1
  set Qh := (m.withReward h).policyActionValue π hγ0 hγ1
  set w : S → A → ℝ := fun s a => α * Qh s a + β / (1 - γ)
  have hπw (s' : S) : expect (π s') (w s') = α * expect (π s') (Qh s') + β / (1 - γ) := by
    simp only [w, expect_add, expect_mul, expect_const]
  have hPw (s : S) (a : A) : expect (m.transition s a) (fun s' => expect (π s') (w s')) =
      α * expect (m.transition s a) (fun s' => expect (π s') (Qh s')) + β / (1 - γ) := by
    simp only [hπw, expect_add, expect_mul, expect_const]
  have hfix (s : S) (a : A) := m.policyActionValue_withReward_eq π hγ0 hγ1 h s a
  have hβ : β + γ * (β / (1 - γ)) = β / (1 - γ) := by field_simp; ring
  rw [abs_le]
  constructor
  · have h := m.le_policyActionValue_withReward π hγ0 hγ1 g (fun s a => -w s a) (fun s a => by
      have hneg (s' : S) : expect (π s') (fun a' => -w s' a') = -expect (π s') (w s') := by
        simp only [expect, mul_neg, Finset.sum_neg_distrib]
      have hneg2 : expect (m.transition s a) (fun s' => -expect (π s') (w s')) =
          -expect (m.transition s a) (fun s' => expect (π s') (w s')) := by
        simp only [expect, mul_neg, Finset.sum_neg_distrib]
      simp only [hneg, hneg2, hPw]
      have := (abs_le.mp (hg s a)).1
      have := hfix s a
      simp only [w]
      nlinarith) s a
    simp only [w] at h
    linarith
  · refine m.policyActionValue_withReward_le π hγ0 hγ1 g w (fun s a => ?_) s a
    rw [hPw]
    have := (abs_le.mp (hg s a)).2
    have := hfix s a
    simp only [w]
    nlinarith

/-- **Simulation for a fixed policy.** If `M` and `M'` share their rewards and
`|γ (P - P') V^π| ≤ c` at every pair, then the action values of `π` in the two MDPs differ by at
most `c / (1 - γ)`. -/
theorem abs_policyActionValue_sub_le (m m' : MDP S A) (hrew : m'.reward = m.reward)
    (π : StationaryPolicy S A) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) {c : ℝ}
    (hc : ∀ s a, |m.transitionGap m' γ (m.policyValue π hγ0 hγ1) s a| ≤ c) (s : S) (a : A) :
    |m.policyActionValue π hγ0 hγ1 s a - m'.policyActionValue π hγ0 hγ1 s a| ≤ c / (1 - γ) := by
  set g := m.transitionGap m' γ (m.policyValue π hγ0 hγ1)
  set D : S → A → ℝ := fun s a => m.policyActionValue π hγ0 hγ1 s a -
    m'.policyActionValue π hγ0 hγ1 s a
  have hD (s : S) (a : A) :
      D s a = g s a + γ * expect (m'.transition s a) (fun s' => expect (π s') (D s')) := by
    have hπD (s' : S) : expect (π s') (D s') =
        m.policyValue π hγ0 hγ1 s' - m'.policyValue π hγ0 hγ1 s' := by
      simp only [D, expect_sub, m.expect_policyActionValue, m'.expect_policyActionValue]
    rw [show (fun s' => expect (π s') (D s')) = fun s' =>
      m.policyValue π hγ0 hγ1 s' - m'.policyValue π hγ0 hγ1 s' from funext hπD, expect_sub]
    simp only [D, g, transitionGap, policyActionValue, oneStepActionValue, hrew]
    ring
  have h1 := m'.policyActionValue_withReward_le π hγ0 hγ1 g D (fun s a => (hD s a).ge) s a
  have h2 := m'.le_policyActionValue_withReward π hγ0 hγ1 g D (fun s a => (hD s a).le) s a
  have h3 := m'.abs_policyActionValue_withReward_le π hγ0 hγ1 (h := fun _ _ => 0) (α := 0)
    (β := c) le_rfl (fun s a => by simpa using hc s a) s a
  rw [zero_mul, zero_add] at h3
  have : D s a = (m'.withReward g).policyActionValue π hγ0 hγ1 s a := le_antisymm h2 h1
  change |D s a| ≤ _
  rw [this]
  exact h3

variable [Nonempty A]

/-- The greedy policy of a Bellman Q fixed point has value `max_a Q*`. -/
theorem policyValue_qGreedyPolicy (m : MDP S A) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    {q : S → A → ℝ} (hq : m.qBellmanOperator γ q = q) :
    m.policyValue (qGreedyPolicy q) hγ0 hγ1 = qMax q := by
  symm
  apply eq_policyValue_of_fixedPoint
  funext s
  simp only [oneStepValue, qGreedyPolicy, expect_pure]
  rw [qMax_eq_qGreedy q s]
  exact congrFun (congrFun hq s) (qGreedy q s)

omit [Fintype A] [Nonempty A] in
/-- A variance is at most the mean squared deviation from any constant. -/
theorem transitionVar_le_expect_sub_sq (m : MDP S A) (v : S → ℝ) (s : S) (a : A) (c : ℝ) :
    m.transitionVar v s a ≤ expect (m.transition s a) (fun s' => (v s' - c) ^ 2) := by
  rw [← m.expect_sub_sq_eq_transitionVar]
  set e := expect (m.transition s a) v
  have hterm (s' : S) : (v s' - c) ^ 2 = (v s' - e) ^ 2 + (2 * (e - c)) * (v s' - e) +
      (e - c) ^ 2 := by ring
  simp only [hterm, expect_add, expect_mul, expect_const, expect_sub]
  simp only [e]
  nlinarith [sq_nonneg (expect (m.transition s a) v - c)]

omit [Fintype A] [Nonempty A] in
/-- **Variance of a perturbed function.** If `|v - u| ≤ d` everywhere, then
`Var (v) ≤ 2 * d ^ 2 + 2 * Var (u)`. -/
theorem transitionVar_le_two_mul (m : MDP S A) {v u : S → ℝ} {d : ℝ}
    (hd : ∀ s, |v s - u s| ≤ d) (s : S) (a : A) :
    m.transitionVar v s a ≤ 2 * d ^ 2 + 2 * m.transitionVar u s a := by
  set e := expect (m.transition s a) u
  refine (m.transitionVar_le_expect_sub_sq v s a e).trans ?_
  rw [← m.expect_sub_sq_eq_transitionVar u]
  have hpt (s' : S) : (v s' - e) ^ 2 ≤ 2 * d ^ 2 + 2 * (u s' - e) ^ 2 := by
    have h1 : (v s' - u s') ^ 2 ≤ d ^ 2 := by
      have := hd s'
      nlinarith [abs_nonneg (v s' - u s'), sq_abs (v s' - u s')]
    nlinarith [sq_nonneg (v s' - u s' - (u s' - e))]
  calc expect (m.transition s a) (fun s' => (v s' - e) ^ 2)
      ≤ expect (m.transition s a) (fun s' => 2 * d ^ 2 + 2 * (u s' - e) ^ 2) :=
        expect_mono _ hpt
    _ = _ := by simp only [expect_add, expect_mul, expect_const]; rfl

omit [Fintype A] [Nonempty A] in
/-- The change of a variance between two transition laws. -/
theorem transitionVar_sub_transitionVar (m m' : MDP S A) (v : S → ℝ) (s : S) (a : A) :
    m.transitionVar v s a - m'.transitionVar v s a =
      (expect (m.transition s a) (fun s' => v s' ^ 2) -
        expect (m'.transition s a) (fun s' => v s' ^ 2)) -
      (expect (m.transition s a) v + expect (m'.transition s a) v) *
        (expect (m.transition s a) v - expect (m'.transition s a) v) := by
  simp only [transitionVar]
  ring


/-- Arithmetic behind the constants of Theorem 2.6: with `e3 = H u`, `e2 = H ^ 2 u`,
`e1 = H u ^ 2 / 3`, and `k = u ^ 2`, the deterministic bound is at most
`√6 γ u √(H ^ 3) + 6 γ H ^ 3 u ^ 2`. -/
theorem minimax_bound_le {γ H u : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) (hH : 1 ≤ H) (hu : 0 ≤ u) :
    γ * Real.sqrt (2 * u ^ 2) * Real.sqrt (H ^ 3) +
        γ * H * (Real.sqrt (u ^ 2 * (2 * (γ * (H * u) * H) ^ 2 + H ^ 2 * u +
          2 * H * (H * u))) + H * u ^ 2 / 3) ≤
      Real.sqrt 6 * γ * u * Real.sqrt (H ^ 3) + 6 * γ * H ^ 3 * u ^ 2 := by
  set R := Real.sqrt (H ^ 3)
  have hH0 : 0 ≤ H := by linarith
  have hR0 : 0 ≤ R := Real.sqrt_nonneg _
  have hR2 : R ^ 2 = H ^ 3 := Real.sq_sqrt (by positivity)
  have hH23 : H ^ 2 ≤ H ^ 3 := pow_le_pow_right₀ hH (by norm_num)
  have hRH : H ≤ R := (Real.le_sqrt hH0 (by positivity)).mpr hH23
  set w := Real.sqrt u
  have hw0 : 0 ≤ w := Real.sqrt_nonneg _
  have hw2 : w ^ 2 = u := Real.sq_sqrt hu
  have r2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have r3 := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have r6 := Real.sq_sqrt (show (0 : ℝ) ≤ 6 by norm_num)
  have r2n := Real.sqrt_nonneg 2
  have r3n := Real.sqrt_nonneg 3
  have r6n := Real.sqrt_nonneg 6
  have hs2u : Real.sqrt (2 * u ^ 2) = Real.sqrt 2 * u := by
    rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq hu]
  have hΔ : Real.sqrt (2 * (γ * (H * u) * H) ^ 2 + H ^ 2 * u + 2 * H * (H * u)) ≤
      Real.sqrt 2 * (γ * H ^ 2 * u) + H * (Real.sqrt 3 * w) := by
    have hsplit : 2 * (γ * (H * u) * H) ^ 2 + H ^ 2 * u + 2 * H * (H * u) =
        2 * (γ * H ^ 2 * u) ^ 2 + H ^ 2 * (3 * u) := by ring
    rw [hsplit]
    refine (sqrt_add_le_add_sqrt (by positivity) (by positivity)).trans (le_of_eq ?_)
    rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq (by positivity), Real.sqrt_mul (by positivity),
      Real.sqrt_sq hH0, Real.sqrt_mul (by norm_num)]
  have hsu : Real.sqrt (u ^ 2 * (2 * (γ * (H * u) * H) ^ 2 + H ^ 2 * u + 2 * H * (H * u))) ≤
      u * (Real.sqrt 2 * (γ * H ^ 2 * u) + H * (Real.sqrt 3 * w)) := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hu]
    exact mul_le_mul_of_nonneg_left hΔ hu
  -- `H ^ 2 * u * √u ≤ (u * R + H ^ 3 * u ^ 2) / 2`.
  have hamgm : H ^ 2 * u * w ≤ (u * R + H ^ 3 * u ^ 2) / 2 := by
    rw [← hw2]
    have hq : 0 ≤ H * (H * w - 1) ^ 2 := mul_nonneg hH0 (sq_nonneg _)
    have hqe : H * (H * w - 1) ^ 2 = H ^ 3 * w ^ 2 - 2 * H ^ 2 * w + H := by ring
    have hkey : 2 * H ^ 2 * w ≤ R + H ^ 3 * w ^ 2 := by linarith
    have hm := mul_le_mul_of_nonneg_left hkey (sq_nonneg w)
    have he1 : w ^ 2 * (2 * H ^ 2 * w) = 2 * (H ^ 2 * w ^ 2 * w) := by ring
    have he2 : w ^ 2 * (R + H ^ 3 * w ^ 2) = w ^ 2 * R + H ^ 3 * (w ^ 2) ^ 2 := by ring
    linarith
  have hγ2 : γ ^ 2 ≤ γ := by rw [sq]; exact mul_le_of_le_one_right hγ0 hγ1
  have h2 : Real.sqrt 2 < 1.415 := (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
  have h3 : Real.sqrt 3 < 1.733 := (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
  have h6 : 2.449 < Real.sqrt 6 := (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
  have hc1 : Real.sqrt 2 + Real.sqrt 3 / 2 ≤ Real.sqrt 6 := by linarith
  have hc2 : Real.sqrt 2 + Real.sqrt 3 / 2 + 1 / 3 ≤ 6 := by linarith
  rw [hs2u]
  have hstep : γ * H * (Real.sqrt (u ^ 2 * (2 * (γ * (H * u) * H) ^ 2 + H ^ 2 * u +
      2 * H * (H * u))) + H * u ^ 2 / 3) ≤
      γ * H * (u * (Real.sqrt 2 * (γ * H ^ 2 * u) + H * (Real.sqrt 3 * w)) + H * u ^ 2 / 3) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hexpand : γ * H * (u * (Real.sqrt 2 * (γ * H ^ 2 * u) + H * (Real.sqrt 3 * w)) +
      H * u ^ 2 / 3) = Real.sqrt 2 * γ ^ 2 * H ^ 3 * u ^ 2 +
        Real.sqrt 3 * γ * (H ^ 2 * u * w) + γ * H ^ 2 * u ^ 2 / 3 := by ring
  have hA : Real.sqrt 3 * γ * (H ^ 2 * u * w) ≤ Real.sqrt 3 / 2 * γ * (u * R + H ^ 3 * u ^ 2) := by
    have := mul_le_mul_of_nonneg_left hamgm (mul_nonneg r3n hγ0)
    linarith
  have hB : Real.sqrt 2 * γ ^ 2 * H ^ 3 * u ^ 2 ≤ Real.sqrt 2 * γ * H ^ 3 * u ^ 2 := by
    have := mul_le_mul_of_nonneg_right hγ2 (by positivity : 0 ≤ Real.sqrt 2 * H ^ 3 * u ^ 2)
    calc Real.sqrt 2 * γ ^ 2 * H ^ 3 * u ^ 2 = γ ^ 2 * (Real.sqrt 2 * H ^ 3 * u ^ 2) := by ring
      _ ≤ γ * (Real.sqrt 2 * H ^ 3 * u ^ 2) := this
      _ = _ := by ring
  have hC : γ * H ^ 2 * u ^ 2 / 3 ≤ γ * H ^ 3 * u ^ 2 / 3 := by
    have := mul_le_mul_of_nonneg_left hH23 (by positivity : 0 ≤ γ * u ^ 2 / 3)
    calc γ * H ^ 2 * u ^ 2 / 3 = γ * u ^ 2 / 3 * H ^ 2 := by ring
      _ ≤ γ * u ^ 2 / 3 * H ^ 3 := this
      _ = _ := by ring
  have hfin1 : (Real.sqrt 2 + Real.sqrt 3 / 2) * (γ * u * R) ≤ Real.sqrt 6 * (γ * u * R) :=
    mul_le_mul_of_nonneg_right hc1 (by positivity)
  have hfin2 : (Real.sqrt 2 + Real.sqrt 3 / 2 + 1 / 3) * (γ * H ^ 3 * u ^ 2) ≤
      6 * (γ * H ^ 3 * u ^ 2) := mul_le_mul_of_nonneg_right hc2 (by positivity)
  calc γ * (Real.sqrt 2 * u) * R + γ * H * (Real.sqrt (u ^ 2 * (2 * (γ * (H * u) * H) ^ 2 +
        H ^ 2 * u + 2 * H * (H * u))) + H * u ^ 2 / 3)
      ≤ γ * (Real.sqrt 2 * u) * R + (Real.sqrt 2 * γ ^ 2 * H ^ 3 * u ^ 2 +
        Real.sqrt 3 * γ * (H ^ 2 * u * w) + γ * H ^ 2 * u ^ 2 / 3) := by
        rw [← hexpand]; exact add_le_add_right hstep _
    _ ≤ γ * (Real.sqrt 2 * u) * R + (Real.sqrt 2 * γ * H ^ 3 * u ^ 2 +
        Real.sqrt 3 / 2 * γ * (u * R + H ^ 3 * u ^ 2) + γ * H ^ 3 * u ^ 2 / 3) := by
        gcongr
    _ = (Real.sqrt 2 + Real.sqrt 3 / 2) * (γ * u * R) +
        (Real.sqrt 2 + Real.sqrt 3 / 2 + 1 / 3) * (γ * H ^ 3 * u ^ 2) := by ring
    _ ≤ Real.sqrt 6 * (γ * u * R) + 6 * (γ * H ^ 3 * u ^ 2) := add_le_add hfin1 hfin2
    _ = _ := by ring

omit [Nonempty A] in
/-- One side of Theorem 2.6: the action values in `M'` of a policy `π` under the gap reward
`γ (P - P') V*` are bounded through the variance of `V^π_{M'}` under `P'`, given the three
deviation bounds and `|V* - V^π_{M'}| ≤ d`. -/
theorem abs_policyActionValue_transitionGap_le (m m' : MDP S A) (hrew : m'.reward = m.reward)
    (hr : ∀ s a, m.reward s a ∈ Set.Icc (0 : ℝ) 1) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (π : StationaryPolicy S A) {v : S → ℝ} (hv : ∀ s, v s ∈ Set.Icc 0 (1 / (1 - γ)))
    {k e1 e2 e3 d : ℝ} (hk : 0 ≤ k) (he2 : 0 ≤ e2) (he3 : 0 ≤ e3)
    (h3 : ∀ s a, |expect (m.transition s a) v - expect (m'.transition s a) v| ≤ e3)
    (h2 : ∀ s a, |expect (m.transition s a) (fun s' => v s' ^ 2) -
      expect (m'.transition s a) (fun s' => v s' ^ 2)| ≤ e2)
    (h1 : ∀ s a, |expect (m.transition s a) v - expect (m'.transition s a) v| ≤
      Real.sqrt (k * m.transitionVar v s a) + e1)
    (hd : ∀ s, |v s - m'.policyValue π hγ0 hγ1 s| ≤ d) (s : S) (a : A) :
    |(m'.withReward (m.transitionGap m' γ v)).policyActionValue π hγ0 hγ1 s a| ≤
      γ * Real.sqrt (2 * k) * Real.sqrt ((1 / (1 - γ)) ^ 3) +
        γ * (1 / (1 - γ)) * (Real.sqrt (k * (2 * d ^ 2 + e2 + 2 * (1 / (1 - γ)) * e3)) + e1) := by
  have hγ : 0 < 1 - γ := sub_pos.mpr hγ1
  set H := 1 / (1 - γ)
  set U := m'.policyValue π hγ0 hγ1
  set Δ := 2 * d ^ 2 + e2 + 2 * H * e3
  have hr' : ∀ s a, m'.reward s a ∈ Set.Icc (0 : ℝ) 1 := by rw [hrew]; exact hr
  have hE (p : PMF S) : expect p v ∈ Set.Icc 0 H := by
    constructor
    · have h := expect_mono p (f := fun _ => 0) (g := v) fun t => (hv t).1
      rwa [expect_zero] at h
    · have h := expect_mono p (g := fun _ => H) (f := v) fun t => (hv t).2
      rwa [expect_const] at h
  -- Transfer of the variance from `P` to `P'` and from `v` to `U`.
  have hvar (s : S) (a : A) : m.transitionVar v s a ≤ 2 * m'.transitionVar U s a + Δ := by
    have hdiff := m.transitionVar_sub_transitionVar m' v s a
    have hsum : |expect (m.transition s a) v + expect (m'.transition s a) v| ≤ 2 * H := by
      rw [abs_le]
      constructor <;> linarith [(hE (m.transition s a)).1, (hE (m.transition s a)).2,
        (hE (m'.transition s a)).1, (hE (m'.transition s a)).2]
    have hprod : -((expect (m.transition s a) v + expect (m'.transition s a) v) *
        (expect (m.transition s a) v - expect (m'.transition s a) v)) ≤ 2 * H * e3 := by
      have := abs_mul (expect (m.transition s a) v + expect (m'.transition s a) v)
        (expect (m.transition s a) v - expect (m'.transition s a) v)
      have h3' := h3 s a
      have hH : 0 ≤ 2 * H := by positivity
      nlinarith [neg_abs_le ((expect (m.transition s a) v + expect (m'.transition s a) v) *
        (expect (m.transition s a) v - expect (m'.transition s a) v)),
        mul_le_mul hsum h3' (abs_nonneg _) hH]
    have hP' := m'.transitionVar_le_two_mul hd s a
    have h2' := le_abs_self (expect (m.transition s a) (fun s' => v s' ^ 2) -
      expect (m'.transition s a) (fun s' => v s' ^ 2))
    have := h2 s a
    simp only [Δ]
    linarith
  -- The gap reward is bounded through `√(Var_{P'} (U))`.
  have hg (s : S) (a : A) : |m.transitionGap m' γ v s a| ≤
      γ * Real.sqrt (2 * k) * Real.sqrt (m'.transitionVar U s a) +
        γ * (Real.sqrt (k * Δ) + e1) := by
    have hsq : Real.sqrt (k * m.transitionVar v s a) ≤
        Real.sqrt (2 * k) * Real.sqrt (m'.transitionVar U s a) + Real.sqrt (k * Δ) := by
      calc Real.sqrt (k * m.transitionVar v s a)
          ≤ Real.sqrt (2 * k * m'.transitionVar U s a + k * Δ) :=
            Real.sqrt_le_sqrt (by nlinarith [hvar s a])
        _ ≤ Real.sqrt (2 * k * m'.transitionVar U s a) + Real.sqrt (k * Δ) :=
            sqrt_add_le_add_sqrt (mul_nonneg (by positivity) (m'.transitionVar_nonneg U s a))
              (mul_nonneg hk (by simp only [Δ, H]; positivity))
        _ = _ := by rw [Real.sqrt_mul (by positivity)]
    rw [transitionGap, abs_mul, abs_of_nonneg hγ0]
    have := h1 s a
    nlinarith [mul_le_mul_of_nonneg_left (this.trans (add_le_add_left hsq e1)) hγ0]
  have hα : 0 ≤ γ * Real.sqrt (2 * k) := by positivity
  have h := m'.abs_policyActionValue_withReward_le π hγ0 hγ1 hα hg s a
  have htv := m'.policyActionValue_withReward_sqrt_transitionVar_le π hγ0 hγ1 hr' s a
  have hH3 : 1 / (1 - γ) ^ 3 = H ^ 3 := by simp only [H, one_div_pow]
  rw [hH3] at htv
  refine h.trans ?_
  have := mul_le_mul_of_nonneg_left htv hα
  have hdiv : γ * (Real.sqrt (k * Δ) + e1) / (1 - γ) = γ * H * (Real.sqrt (k * Δ) + e1) := by
    simp only [H]; field_simp
  rw [hdiv]
  linarith

/-- **Theorem 2.6, deterministic part.** Let `M` and `M̂` share rewards in `[0, 1]`, and let `Q*`
and `Q̂*` be their Bellman Q fixed points with `V* = max_a Q*`. If at every pair
`|(P - P̂) V*| ≤ e3`, `|(P - P̂) (V*) ^ 2| ≤ e2`, and
`|(P - P̂) V*| ≤ √(k * Var_P (V*)) + e1`, then with `H = 1 / (1 - γ)`,
`|Q* - Q̂*| ≤ γ √(2 k) √(H ^ 3) + γ H (√(k (2 (γ e3 H) ^ 2 + e2 + 2 H e3)) + e1)`. -/
theorem abs_sub_le_of_deviations (m m' : MDP S A) (hrew : m'.reward = m.reward)
    (hr : ∀ s a, m.reward s a ∈ Set.Icc (0 : ℝ) 1) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    {q q' : S → A → ℝ} (hq : m.qBellmanOperator γ q = q) (hq' : m'.qBellmanOperator γ q' = q')
    {k e1 e2 e3 : ℝ} (hk : 0 ≤ k) (he2 : 0 ≤ e2) (he3 : 0 ≤ e3)
    (h3 : ∀ s a, |expect (m.transition s a) (qMax q) - expect (m'.transition s a) (qMax q)| ≤ e3)
    (h2 : ∀ s a, |expect (m.transition s a) (fun s' => qMax q s' ^ 2) -
      expect (m'.transition s a) (fun s' => qMax q s' ^ 2)| ≤ e2)
    (h1 : ∀ s a, |expect (m.transition s a) (qMax q) - expect (m'.transition s a) (qMax q)| ≤
      Real.sqrt (k * m.transitionVar (qMax q) s a) + e1) (s : S) (a : A) :
    |q s a - q' s a| ≤ γ * Real.sqrt (2 * k) * Real.sqrt ((1 / (1 - γ)) ^ 3) +
      γ * (1 / (1 - γ)) * (Real.sqrt (k * (2 * (γ * e3 * (1 / (1 - γ))) ^ 2 + e2 +
        2 * (1 / (1 - γ)) * e3)) + e1) := by
  have hγ : 0 < 1 - γ := sub_pos.mpr hγ1
  set H := 1 / (1 - γ)
  set v := qMax q
  set g := m.transitionGap m' γ v
  have hr' : ∀ s a, m'.reward s a ∈ Set.Icc (0 : ℝ) 1 := by rw [hrew]; exact hr
  have hvπ : m.policyValue (qGreedyPolicy q) hγ0 hγ1 = v := m.policyValue_qGreedyPolicy hγ0 hγ1 hq
  have hv (s : S) : v s ∈ Set.Icc 0 H := by
    rw [← hvπ]; exact m.policyValue_mem_Icc _ hγ0 hγ1 hr s
  have hgb (s : S) (a : A) : |g s a| ≤ γ * e3 := by
    simp only [g, transitionGap, abs_mul, abs_of_nonneg hγ0]
    exact mul_le_mul_of_nonneg_left (h3 s a) hγ0
  have hcrude (π : StationaryPolicy S A) (s : S) (a : A) :
      |(m'.withReward g).policyActionValue π hγ0 hγ1 s a| ≤ γ * e3 * H := by
    have h := m'.abs_policyActionValue_withReward_le π hγ0 hγ1 (h := fun _ _ => 0) (α := 0)
      (β := γ * e3) le_rfl (fun s a => by simpa using hgb s a) s a
    simp only [zero_mul, zero_add] at h
    rw [← mul_one_div] at h
    exact h
  have hlem := m.sub_le_policyActionValue_transitionGap m' hrew hγ0 hγ1 hq hq'
  -- `|Q* - Q̂*| ≤ γ e3 H`, hence the same bound on `max_a`.
  have hqq (s : S) (a : A) : |q s a - q' s a| ≤ γ * e3 * H := by
    rw [abs_le]
    constructor
    · linarith [(hlem s a).1, neg_abs_le ((m'.withReward g).policyActionValue
        (qGreedyPolicy q') hγ0 hγ1 s a), hcrude (qGreedyPolicy q') s a]
    · linarith [(hlem s a).2, le_abs_self ((m'.withReward g).policyActionValue
        (qGreedyPolicy q) hγ0 hγ1 s a), hcrude (qGreedyPolicy q) s a]
  -- Distances to the two comparison values.
  have hd1 (s : S) : |v s - m'.policyValue (qGreedyPolicy q) hγ0 hγ1 s| ≤ γ * e3 * H := by
    have hsim := m.abs_policyActionValue_sub_le m' hrew (qGreedyPolicy q) hγ0 hγ1
      (c := γ * e3) (fun s a => by rw [hvπ]; exact hgb s a) s (qGreedy q s)
    have hV (mm : MDP S A) : mm.policyValue (qGreedyPolicy q) hγ0 hγ1 s =
        mm.policyActionValue (qGreedyPolicy q) hγ0 hγ1 s (qGreedy q s) := by
      rw [← mm.expect_policyActionValue]; simp only [qGreedyPolicy, expect_pure]
    rw [← hvπ, hV m, hV m']
    rw [← mul_one_div] at hsim
    exact hsim
  have hvπ' : m'.policyValue (qGreedyPolicy q') hγ0 hγ1 = qMax q' :=
    m'.policyValue_qGreedyPolicy hγ0 hγ1 hq'
  have hd2 (s : S) : |v s - m'.policyValue (qGreedyPolicy q') hγ0 hγ1 s| ≤ γ * e3 * H := by
    rw [hvπ']
    simp only [v]
    rw [abs_le]
    constructor
    · rw [qMax_eq_qGreedy q' s]
      have := le_qGreedy q s (qGreedy q' s)
      rw [← qMax_eq_qGreedy q s] at this
      linarith [(abs_le.mp (hqq s (qGreedy q' s))).1]
    · rw [qMax_eq_qGreedy q s]
      have := le_qGreedy q' s (qGreedy q s)
      rw [← qMax_eq_qGreedy q' s] at this
      linarith [(abs_le.mp (hqq s (qGreedy q s))).2]
  have hup := m.abs_policyActionValue_transitionGap_le m' hrew hr hγ0 hγ1 (qGreedyPolicy q) hv
    hk he2 he3 h3 h2 h1 hd1 s a
  have hlow := m.abs_policyActionValue_transitionGap_le m' hrew hr hγ0 hγ1 (qGreedyPolicy q')
    hv hk he2 he3 h3 h2 h1 hd2 s a
  have hsq : (γ * e3 * H) ^ 2 = (γ * e3 * (1 / (1 - γ))) ^ 2 := rfl
  rw [abs_le]
  constructor
  · linarith [(hlem s a).1, neg_abs_le ((m'.withReward g).policyActionValue
      (qGreedyPolicy q') hγ0 hγ1 s a)]
  · linarith [(hlem s a).2, le_abs_self ((m'.withReward g).policyActionValue
      (qGreedyPolicy q) hγ0 hγ1 s a)]

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [MeasurableSpace S] [MeasurableSingletonClass S] {n : ℕ}

/-- **Minimax value estimation (Agarwal, Jiang, Kakade, and Sun, Theorem 2.6).** Take rewards in
`[0, 1]`, a discount `γ ∈ [0, 1)`, and `N = n + 1` independent successors per state-action pair
from the model's transition law. Let `Q̂*` be the Bellman Q fixed point of the MDP with the true
rewards and the empirical transitions. Then for `0 < δ ≤ 1`, with probability at least `1 - δ`,
`‖Q* - Q̂*‖∞ ≤ γ √(c log (c |S| |A| / δ) / ((1 - γ) ^ 3 N)) + c γ log (c |S| |A| / δ) /
((1 - γ) ^ 3 N)` with the absolute constant `c = 12`. -/
theorem measure_abs_sub_qBellman_fixed_le (m : MDP S A)
    (hr : ∀ s a, m.reward s a ∈ Set.Icc (0 : ℝ) 1) (D : Ω → S → A → Fin (n + 1) → S)
    (hindep : ∀ s a, iIndepFun (fun i ω => D ω s a i) μ)
    (hmeas : ∀ s a i, AEMeasurable (fun ω => D ω s a i) μ)
    (hlaw : ∀ s a i, μ.map (fun ω => D ω s a i) = (m.transition s a).toMeasure)
    {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) {q : S → A → ℝ} (hq : m.qBellmanOperator γ q = q)
    (qhat : Ω → S → A → ℝ)
    (hqhat : ∀ ω, (m.withSuccessors (D ω)).qBellmanOperator γ (qhat ω) = qhat ω)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    μ.real {ω | ∃ s a, γ * Real.sqrt (12 * Real.log (12 * (Fintype.card S * Fintype.card A) / δ) /
        ((1 - γ) ^ 3 * (n + 1))) +
        12 * γ * Real.log (12 * (Fintype.card S * Fintype.card A) / δ) /
          ((1 - γ) ^ 3 * (n + 1)) < |q s a - qhat ω s a|} ≤ δ := by
  classical
  by_cases hne : Nonempty (S × A)
  swap
  · have hempty : {ω | ∃ s a, γ * Real.sqrt (12 * Real.log (12 * (Fintype.card S *
        Fintype.card A) / δ) / ((1 - γ) ^ 3 * (n + 1))) +
        12 * γ * Real.log (12 * (Fintype.card S * Fintype.card A) / δ) /
          ((1 - γ) ^ 3 * (n + 1)) < |q s a - qhat ω s a|} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_exists]
      exact fun s a _ => hne ⟨(s, a)⟩
    rw [hempty, measureReal_empty]
    exact hδ0.le
  obtain ⟨⟨s₀, a₀⟩⟩ := hne
  have hγ : 0 < 1 - γ := sub_pos.mpr hγ1
  have hN : (0 : ℝ) < n + 1 := by positivity
  set K : ℝ := Fintype.card S * Fintype.card A
  have hK : 1 ≤ K := by
    have : Nonempty S := ⟨s₀⟩
    have h1 : (1 : ℝ) ≤ Fintype.card S := Nat.one_le_cast.mpr Fintype.card_pos
    have h2 : (1 : ℝ) ≤ Fintype.card A := Nat.one_le_cast.mpr Fintype.card_pos
    nlinarith
  set H := 1 / (1 - γ)
  have hH : 1 ≤ H := by rw [le_div_iff₀ hγ]; linarith
  have hH0 : 0 < H := by linarith
  set v := qMax q
  have hv (s : S) : v s ∈ Set.Icc 0 H := by
    have := m.policyValue_mem_Icc (qGreedyPolicy q) hγ0 hγ1 hr s
    rwa [m.policyValue_qGreedyPolicy hγ0 hγ1 hq] at this
  set δ3 := δ / 3
  have hδ30 : 0 < δ3 := by positivity
  have hδ31 : δ3 ≤ 1 := by simp only [δ3]; linarith
  set L := Real.log (2 * K / δ3)
  have hL0 : 0 ≤ L := Real.log_nonneg (by rw [le_div_iff₀ hδ30]; simp only [δ3]; nlinarith)
  have hL12 : L ≤ Real.log (12 * K / δ) := by
    refine Real.log_le_log (by positivity) ?_
    simp only [δ3]
    rw [div_div_eq_mul_div, div_le_div_iff_of_pos_right hδ0]
    nlinarith
  set u := Real.sqrt (2 * L / (n + 1))
  have hu0 : 0 ≤ u := Real.sqrt_nonneg _
  have hu2 : u ^ 2 = 2 * L / (n + 1) := Real.sq_sqrt (by positivity)
  -- The three bad events.
  have hE3 := m.measure_exists_transition_hoeffding_le D hindep hmeas hlaw (v := v) hH0
    (fun s => by rw [abs_of_nonneg (hv s).1]; exact (hv s).2) hδ30 hδ31
  have hE2 := m.measure_exists_transition_hoeffding_le D hindep hmeas hlaw
    (v := fun s => v s ^ 2) (B := H ^ 2) (by positivity)
    (fun s => by
      rw [abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (hv s).1 (hv s).2 2) hδ30 hδ31
  have hE1 := m.measure_exists_transition_deviation_le D hindep hmeas hlaw hH0 hv hδ30 hδ31
  set E3 := {ω | ∃ s a, H * Real.sqrt (2 * L / (n + 1)) ≤
    |expect (m.transition s a) v - expect ((m.withSuccessors (D ω)).transition s a) v|}
  set E2 := {ω | ∃ s a, H ^ 2 * Real.sqrt (2 * L / (n + 1)) ≤
    |expect (m.transition s a) (fun s' => v s' ^ 2) -
      expect ((m.withSuccessors (D ω)).transition s a) (fun s' => v s' ^ 2)|}
  set E1 := {ω | ∃ s a, Real.sqrt (2 * L / (n + 1) * m.transitionVar v s a) +
      2 * H * L / (3 * (n + 1)) ≤
    |expect (m.transition s a) v - expect ((m.withSuccessors (D ω)).transition s a) v|}
  -- Outside the bad events the deterministic bound applies.
  have hsub : {ω | ∃ s a, γ * Real.sqrt (12 * Real.log (12 * K / δ) / ((1 - γ) ^ 3 * (n + 1))) +
      12 * γ * Real.log (12 * K / δ) / ((1 - γ) ^ 3 * (n + 1)) < |q s a - qhat ω s a|} ⊆
      E1 ∪ E2 ∪ E3 := by
    rintro ω ⟨s, a, hbad⟩
    by_contra hnot
    simp only [Set.mem_union, not_or, E1, E2, E3, Set.mem_ofPred_eq, not_exists, not_le] at hnot
    obtain ⟨⟨h1, h2⟩, h3⟩ := hnot
    set m' := m.withSuccessors (D ω)
    have hcore := m.abs_sub_le_of_deviations m' rfl hr hγ0 hγ1 hq (hqhat ω)
      (k := u ^ 2) (e1 := H * u ^ 2 / 3) (e2 := H ^ 2 * u) (e3 := H * u) (sq_nonneg u)
      (by positivity) (by positivity)
      (fun s a => (h3 s a).le) (fun s a => (h2 s a).le)
      (fun s a => by
        have := (h1 s a).le
        rw [hu2]
        convert this using 2
        field_simp) s a
    have hsimp := minimax_bound_le (γ := γ) (H := H) (u := u) hγ0 hγ1.le hH hu0
    have hcore' : |q s a - qhat ω s a| ≤
        Real.sqrt 6 * γ * u * Real.sqrt (H ^ 3) + 6 * γ * H ^ 3 * u ^ 2 := by
      exact hcore.trans hsimp
    -- Compare with the stated bound.
    have hH3 : (1 - γ) ^ 3 * (n + 1) ≠ 0 := by positivity
    have hfirst : Real.sqrt 6 * u * Real.sqrt (H ^ 3) ≤
        Real.sqrt (12 * Real.log (12 * K / δ) / ((1 - γ) ^ 3 * (n + 1))) := by
      have hR2 : Real.sqrt (H ^ 3) ^ 2 = H ^ 3 := Real.sq_sqrt (by positivity)
      have h62 : Real.sqrt 6 ^ 2 = 6 := Real.sq_sqrt (by norm_num)
      rw [Real.le_sqrt (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hu0) (Real.sqrt_nonneg _))
        (div_nonneg (mul_nonneg (by norm_num) (hL0.trans hL12)) (by positivity)), mul_pow,
        mul_pow, hR2, h62, hu2]
      have : H ^ 3 = 1 / (1 - γ) ^ 3 := by simp only [H, one_div_pow]
      rw [this, show 6 * (2 * L / (n + 1)) * (1 / (1 - γ) ^ 3) =
        12 * L / ((1 - γ) ^ 3 * (n + 1)) by field_simp; ring]
      exact div_le_div_of_nonneg_right (by linarith) (by positivity)
    have hsecond : 6 * H ^ 3 * u ^ 2 ≤
        12 * Real.log (12 * K / δ) / ((1 - γ) ^ 3 * (n + 1)) := by
      rw [hu2]
      have : H ^ 3 = 1 / (1 - γ) ^ 3 := by simp only [H, one_div_pow]
      rw [this, show 6 * (1 / (1 - γ) ^ 3) * (2 * L / (n + 1)) =
        12 * L / ((1 - γ) ^ 3 * (n + 1)) by field_simp; ring]
      exact div_le_div_of_nonneg_right (by linarith) (by positivity)
    have h1' := mul_le_mul_of_nonneg_left hfirst hγ0
    have h2' := mul_le_mul_of_nonneg_left hsecond hγ0
    have hlhs : Real.sqrt 6 * γ * u * Real.sqrt (H ^ 3) + 6 * γ * H ^ 3 * u ^ 2 =
        γ * (Real.sqrt 6 * u * Real.sqrt (H ^ 3)) + γ * (6 * H ^ 3 * u ^ 2) := by ring
    have hrhs : 12 * γ * Real.log (12 * K / δ) / ((1 - γ) ^ 3 * (n + 1)) =
        γ * (12 * Real.log (12 * K / δ) / ((1 - γ) ^ 3 * (n + 1))) := by ring
    linarith
  calc _ ≤ μ.real (E1 ∪ E2 ∪ E3) := measureReal_mono hsub
    _ ≤ μ.real E1 + μ.real E2 + μ.real E3 :=
        (measureReal_union_le _ _).trans (add_le_add_left (measureReal_union_le _ _) _)
    _ ≤ δ3 + δ3 + δ3 := by
        refine add_le_add (add_le_add ?_ ?_) ?_
        · exact hE1
        · exact hE2
        · exact hE3
    _ = δ := by simp only [δ3]; ring

/-- **Near-optimal planning from samples (Theorem 2.6 with Lemma 1.11).** Under the conditions
of `measure_abs_sub_qBellman_fixed_le`, with probability at least `1 - δ`, the greedy policy of
`Q̂*` has value within `2 / (1 - γ)` times the bound of Theorem 2.6 of `V*` at every state. -/
theorem measure_qGreedyPolicy_suboptimal_le_minimax (m : MDP S A)
    (hr : ∀ s a, m.reward s a ∈ Set.Icc (0 : ℝ) 1) (D : Ω → S → A → Fin (n + 1) → S)
    (hindep : ∀ s a, iIndepFun (fun i ω => D ω s a i) μ)
    (hmeas : ∀ s a i, AEMeasurable (fun ω => D ω s a i) μ)
    (hlaw : ∀ s a i, μ.map (fun ω => D ω s a i) = (m.transition s a).toMeasure)
    {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) {q : S → A → ℝ} (hq : m.qBellmanOperator γ q = q)
    (qhat : Ω → S → A → ℝ)
    (hqhat : ∀ ω, (m.withSuccessors (D ω)).qBellmanOperator γ (qhat ω) = qhat ω)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    μ.real {ω | ∃ s, 2 / (1 - γ) * (γ * Real.sqrt (12 * Real.log (12 * (Fintype.card S *
        Fintype.card A) / δ) / ((1 - γ) ^ 3 * (n + 1))) +
        12 * γ * Real.log (12 * (Fintype.card S * Fintype.card A) / δ) /
          ((1 - γ) ^ 3 * (n + 1))) <
        qMax q s - m.policyValue (qGreedyPolicy (qhat ω)) hγ0 hγ1 s} ≤ δ := by
  have hγ : 0 < 1 - γ := sub_pos.mpr hγ1
  set b := γ * Real.sqrt (12 * Real.log (12 * (Fintype.card S * Fintype.card A) / δ) /
    ((1 - γ) ^ 3 * (n + 1))) + 12 * γ * Real.log (12 * (Fintype.card S * Fintype.card A) / δ) /
      ((1 - γ) ^ 3 * (n + 1))
  refine le_trans (measureReal_mono fun ω hω => ?_)
    (m.measure_abs_sub_qBellman_fixed_le hr D hindep hmeas hlaw hγ0 hγ1 hq qhat hqhat hδ0 hδ1)
  obtain ⟨s, hs⟩ := hω
  simp only [Set.mem_ofPred_eq]
  by_contra hnot
  simp only [not_exists, not_lt] at hnot
  have hb : 0 ≤ b := (abs_nonneg _).trans (hnot s (Classical.arbitrary A))
  have hnorm : ‖qhat ω - q‖ ≤ b := (pi_norm_le_iff_of_nonneg hb).mpr fun s =>
    (pi_norm_le_iff_of_nonneg hb).mpr fun a => by
      rw [Pi.sub_apply, Pi.sub_apply, Real.norm_eq_abs, abs_sub_comm]
      exact hnot s a
  have h := m.qMax_sub_policyValue_qGreedyPolicy_le hγ0 hγ1 hq hnorm s
  have : 2 * b / (1 - γ) = 2 / (1 - γ) * b := by ring
  linarith

end MDP

end Rlib
