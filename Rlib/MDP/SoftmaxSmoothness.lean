module

public import Rlib.MDP.NaturalPolicyGradient
public import Rlib.MDP.TrustRegion
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Pow

/-! # Smoothness of the softmax policy value

Along any line `θ + t * u` in score space, the value of the softmax policy bends by at most a
quadratic amount: `V (θ + t * u) ≥ V θ + t * V' - 3 * K ^ 2 * t ^ 2 / (1 - γ) ^ 3` for
`t ≥ 0`, where `V'` is the directional derivative, `K` bounds `|u|`, and rewards lie in
`[0, 1]` as in Mei et al. (2020).
This is the ascent lemma behind the convergence of softmax policy gradient.
-/

@[expose] public section

noncomputable section

namespace Rlib

variable {S A : Type*} [Fintype A] [Nonempty A]

/-- Moving softmax scores by `t * u`, with `|u| ≤ K`, moves each action distribution by at most
`2 * K * |t|` in `ℓ¹`. -/
theorem sum_abs_softmaxPolicy_sub_le (θ u : S → A → ℝ) {K : ℝ} (hu : ∀ s a, |u s a| ≤ K)
    (t : ℝ) (s : S) :
    ∑ a, |(softmaxPolicy (fun s a => θ s a + t * u s a) s a).toReal -
      (softmaxPolicy θ s a).toReal| ≤ 2 * K * |t| := by
  set p : ℝ → A → ℝ := fun x a => (softmaxPolicy (fun s a => θ s a + x * u s a) s a).toReal
  set σ : A → ℝ := fun a => if 0 ≤ p t a - p 0 a then 1 else -1
  have hderiv (x : ℝ) (a : A) : HasDerivAt (fun y => p y a)
      (p x a * (u s a - ∑ b, p x b * u s b)) x := by
    have h := hasDerivAt_softmaxPolicy (fun s a => θ s a + x * u s a) u s a
    have h' := HasDerivAt.comp_sub_const x x (by simpa using h)
    convert h' using 1
    funext y
    simp only [p]
    congr 4
    funext s a
    ring
  set F : ℝ → ℝ := fun x => ∑ a, σ a * p x a
  have hF (x : ℝ) : HasDerivAt F (∑ a, σ a * (p x a * (u s a - ∑ b, p x b * u s b))) x :=
    HasDerivAt.fun_sum fun a _ => (hderiv x a).const_mul (σ a)
  have hbound (x : ℝ) : ‖∑ a, σ a * (p x a * (u s a - ∑ b, p x b * u s b))‖ ≤ 2 * K := by
    have hpn (b : A) : 0 ≤ p x b := ENNReal.toReal_nonneg
    have hsum : ∑ b, p x b = 1 := probability_sum _
    have hmean : |∑ b, p x b * u s b| ≤ K := by
      calc |∑ b, p x b * u s b| ≤ ∑ b, |p x b * u s b| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ b, p x b * K := Finset.sum_le_sum fun b _ => by
            rw [abs_mul, abs_of_nonneg (hpn b)]
            exact mul_le_mul_of_nonneg_left (hu s b) (hpn b)
        _ = K := by rw [← Finset.sum_mul, hsum, one_mul]
    rw [Real.norm_eq_abs]
    calc _ ≤ ∑ a, |σ a * (p x a * (u s a - ∑ b, p x b * u s b))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ a, p x a * (2 * K) := Finset.sum_le_sum fun a _ => by
          have hσ : |σ a| = 1 := by simp only [σ]; split_ifs <;> simp
          rw [abs_mul, hσ, one_mul, abs_mul, abs_of_nonneg (hpn a)]
          refine mul_le_mul_of_nonneg_left ?_ (hpn a)
          calc |u s a - ∑ b, p x b * u s b| ≤ |u s a| + |∑ b, p x b * u s b| := abs_sub _ _
            _ ≤ 2 * K := by linarith [hu s a]
      _ = 2 * K := by rw [← Finset.sum_mul, hsum, one_mul]
  have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x _ => (hF x).hasDerivWithinAt) (fun x _ => hbound x) convex_univ
    (Set.mem_univ 0) (Set.mem_univ t)
  have heq : F t - F 0 = ∑ a, |p t a - p 0 a| := by
    simp only [F, ← Finset.sum_sub_distrib, ← mul_sub]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [σ]
    split_ifs with h
    · rw [one_mul, abs_of_nonneg h]
    · rw [abs_of_neg (not_le.mp h)]; ring
  rw [heq, Real.norm_eq_abs, Real.norm_eq_abs, sub_zero, abs_of_nonneg
    (Finset.sum_nonneg fun a _ => abs_nonneg _)] at hmvt
  simpa only [p, zero_mul, add_zero] using hmvt

namespace MDP

variable [Fintype S]

omit [Nonempty A] in
/-- With rewards in `[0, 1]`, every advantage is at most `1 / (1 - γ)` in absolute value. -/
theorem abs_advantage_le (m : MDP S A) (π : StationaryPolicy S A) {γ : ℝ} (hγ0 : 0 ≤ γ)
    (hγ1 : γ < 1) (hr : ∀ s a, m.reward s a ∈ Set.Icc (0 : ℝ) 1) (s : S) (a : A) :
    |m.advantage π hγ0 hγ1 s a| ≤ 1 / (1 - γ) := by
  have hγ : 0 < 1 - γ := sub_pos.mpr hγ1
  set V := m.policyValue π hγ0 hγ1
  have hV (t : S) := m.policyValue_mem_Icc π hγ0 hγ1 hr t
  have hE0 : 0 ≤ expect (m.transition s a) V := by
    have h := expect_mono (m.transition s a) (f := fun _ => 0) (g := V) fun t => (hV t).1
    rwa [expect_zero] at h
  have hE1 : expect (m.transition s a) V ≤ 1 / (1 - γ) := by
    calc expect (m.transition s a) V ≤ expect (m.transition s a) fun _ => 1 / (1 - γ) :=
          expect_mono _ fun t => (hV t).2
      _ = _ := expect_const _ _
  have hQ1 : m.reward s a + γ * expect (m.transition s a) V ≤ 1 / (1 - γ) := by
    have : 1 + γ * (1 / (1 - γ)) = 1 / (1 - γ) := by field_simp; ring
    nlinarith [(hr s a).2, mul_le_mul_of_nonneg_left hE1 hγ0]
  have hQ0 : 0 ≤ m.reward s a + γ * expect (m.transition s a) V :=
    add_nonneg (hr s a).1 (mul_nonneg hγ0 hE0)
  simp only [advantage, policyActionValue, oneStepActionValue]
  rw [abs_sub_le_iff]
  constructor <;> linarith [(hV s).1, (hV s).2]

variable [DecidableEq S]

/-- Policies whose action distributions are within `δ` in `ℓ¹` at every state have values
within `δ / (1 - γ) ^ 2`. -/
theorem abs_policyValue_sub_le_of_le (m : MDP S A) (π π' : StationaryPolicy S A) {γ : ℝ}
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) {δ : ℝ} (hr : ∀ s a, m.reward s a ∈ Set.Icc (0 : ℝ) 1)
    (hδ : ∀ s, ∑ a, |(π' s a).toReal - (π s a).toReal| ≤ δ) (s₀ : S) :
    |m.policyValue π' hγ0 hγ1 s₀ - m.policyValue π hγ0 hγ1 s₀| ≤
      δ / (1 - γ) ^ 2 := by
  have hγ : 0 < 1 - γ := sub_pos.mpr hγ1
  have h := m.policyValue_sub_eq_sum π π' hγ0 hγ1 s₀
  have hinner (s : S) : |∑ a, ((π' s a).toReal - (π s a).toReal) * m.advantage π hγ0 hγ1 s a| ≤
      δ * (1 / (1 - γ)) := by
    calc _ ≤ ∑ a, |((π' s a).toReal - (π s a).toReal) * m.advantage π hγ0 hγ1 s a| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ a, |(π' s a).toReal - (π s a).toReal| * (1 / (1 - γ)) :=
          Finset.sum_le_sum fun a _ => by
            rw [abs_mul]
            exact mul_le_mul_of_nonneg_left (m.abs_advantage_le π hγ0 hγ1 hr s a)
              (abs_nonneg _)
      _ ≤ δ * (1 / (1 - γ)) := by
          rw [← Finset.sum_mul]
          exact mul_le_mul_of_nonneg_right (hδ s)
            ((abs_nonneg _).trans (m.abs_advantage_le π hγ0 hγ1 hr s (Classical.arbitrary A)))
  have hsum : |(1 - γ) * (m.policyValue π' hγ0 hγ1 s₀ - m.policyValue π hγ0 hγ1 s₀)| ≤
      δ * (1 / (1 - γ)) := by
    rw [h]
    calc _ ≤ ∑ s, |m.discountedVisitation π' hγ0 hγ1 s₀ s *
          ∑ a, ((π' s a).toReal - (π s a).toReal) * m.advantage π hγ0 hγ1 s a| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ s, m.discountedVisitation π' hγ0 hγ1 s₀ s * (δ * (1 / (1 - γ))) :=
          Finset.sum_le_sum fun s _ => by
            rw [abs_mul, abs_of_nonneg (m.discountedVisitation_nonneg π' hγ0 hγ1 s₀ s)]
            exact mul_le_mul_of_nonneg_left (hinner s)
              (m.discountedVisitation_nonneg π' hγ0 hγ1 s₀ s)
      _ = _ := by rw [← Finset.sum_mul, m.sum_discountedVisitation, one_mul]
  rw [abs_mul, abs_of_pos hγ] at hsum
  rw [le_div_iff₀ (by positivity)]
  calc |m.policyValue π' hγ0 hγ1 s₀ - m.policyValue π hγ0 hγ1 s₀| * (1 - γ) ^ 2
      = (1 - γ) * ((1 - γ) * |m.policyValue π' hγ0 hγ1 s₀ - m.policyValue π hγ0 hγ1 s₀|) := by
        ring
    _ ≤ (1 - γ) * (δ * (1 / (1 - γ))) := mul_le_mul_of_nonneg_left hsum hγ.le
    _ = δ := by field_simp

/-- Policies within `δ` in `ℓ¹` at every state have advantages within
`(1 + γ) * (δ / (1 - γ) ^ 2)`. -/
theorem abs_advantage_sub_le_of_le (m : MDP S A) (π π' : StationaryPolicy S A) {γ : ℝ}
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) {δ : ℝ} (hr : ∀ s a, m.reward s a ∈ Set.Icc (0 : ℝ) 1)
    (hδ : ∀ s, ∑ a, |(π' s a).toReal - (π s a).toReal| ≤ δ) (s : S) (a : A) :
    |m.advantage π' hγ0 hγ1 s a - m.advantage π hγ0 hγ1 s a| ≤
      (1 + γ) * (δ / (1 - γ) ^ 2) := by
  set V := m.policyValue π hγ0 hγ1
  set V' := m.policyValue π' hγ0 hγ1
  set c := δ / (1 - γ) ^ 2
  have hV (t : S) : |V' t - V t| ≤ c := m.abs_policyValue_sub_le_of_le π π' hγ0 hγ1 hr hδ t
  have hc : 0 ≤ c := (abs_nonneg _).trans (hV s)
  have hE : |expect (m.transition s a) V' - expect (m.transition s a) V| ≤ c := by
    have h := norm_expect_sub_expect_le (m.transition s a) V' V
    rw [Real.norm_eq_abs] at h
    refine h.trans ((pi_norm_le_iff_of_nonneg hc).mpr fun t => ?_)
    rw [Pi.sub_apply, Real.norm_eq_abs]
    exact hV t
  have heq : m.advantage π' hγ0 hγ1 s a - m.advantage π hγ0 hγ1 s a =
      γ * (expect (m.transition s a) V' - expect (m.transition s a) V) - (V' s - V s) := by
    simp only [advantage, policyActionValue, oneStepActionValue, V, V']
    ring
  rw [heq]
  calc _ ≤ |γ * (expect (m.transition s a) V' - expect (m.transition s a) V)| + |V' s - V s| :=
        abs_sub _ _
    _ ≤ γ * c + c := by
        rw [abs_mul, abs_of_nonneg hγ0]
        exact add_le_add (mul_le_mul_of_nonneg_left hE hγ0) (hV s)
    _ = (1 + γ) * c := by ring

/-- The rate at which the value of `π` changes when the softmax scores move in direction `u`,
up to the factor `(1 - γ)⁻¹`: the visitation average of `∑ a, π a * u s a * A s a`. -/
def directionalGain (m : MDP S A) (π : StationaryPolicy S A) {γ : ℝ} (hγ0 : 0 ≤ γ)
    (hγ1 : γ < 1) (u : S → A → ℝ) (s₀ : S) : ℝ :=
  ∑ s, m.discountedVisitation π hγ0 hγ1 s₀ s *
    ∑ a, (π s a).toReal * u s a * m.advantage π hγ0 hγ1 s a

/-- The directional gain is Lipschitz in the policy: policies within `δ` in `ℓ¹` at every state
have gains within `3 * K * δ / (1 - γ) ^ 2`, where `K` bounds `|u|`. -/
theorem abs_directionalGain_sub_le (m : MDP S A) (π π' : StationaryPolicy S A) {γ : ℝ}
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) {δ K : ℝ} (hr : ∀ s a, m.reward s a ∈ Set.Icc (0 : ℝ) 1)
    (hδ : ∀ s, ∑ a, |(π' s a).toReal - (π s a).toReal| ≤ δ) (u : S → A → ℝ)
    (hu : ∀ s a, |u s a| ≤ K) (s₀ : S) :
    |m.directionalGain π' hγ0 hγ1 u s₀ - m.directionalGain π hγ0 hγ1 u s₀| ≤
      3 * K * δ / (1 - γ) ^ 2 := by
  have hγ : 0 < 1 - γ := sub_pos.mpr hγ1
  set d := m.discountedVisitation π hγ0 hγ1 s₀
  set d' := m.discountedVisitation π' hγ0 hγ1 s₀
  set Ad := m.advantage π hγ0 hγ1
  set Ad' := m.advantage π' hγ0 hγ1
  set M := 1 / (1 - γ)
  set M2 := (1 + γ) * (δ / (1 - γ) ^ 2)
  set X : S → ℝ := fun s => ∑ a, (π s a).toReal * u s a * Ad s a
  set X' : S → ℝ := fun s => ∑ a, (π' s a).toReal * u s a * Ad' s a
  have a₀ : A := Classical.arbitrary A
  have hK : 0 ≤ K := (abs_nonneg _).trans (hu s₀ a₀)
  have hδ0 : 0 ≤ δ := (Finset.sum_nonneg fun a _ => abs_nonneg _).trans (hδ s₀)
  have hM : 0 ≤ M := by positivity
  have hA' (s : S) (a : A) : |Ad' s a| ≤ M := m.abs_advantage_le π' hγ0 hγ1 hr s a
  have hdA (s : S) (a : A) : |Ad' s a - Ad s a| ≤ M2 :=
    m.abs_advantage_sub_le_of_le π π' hγ0 hγ1 hr hδ s a
  have hX' (s : S) : |X' s| ≤ K * M := by
    calc |X' s| ≤ ∑ a, |(π' s a).toReal * u s a * Ad' s a| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ a, (π' s a).toReal * (K * M) := Finset.sum_le_sum fun a _ => by
          rw [abs_mul, abs_mul, abs_of_nonneg ENNReal.toReal_nonneg, mul_assoc]
          exact mul_le_mul_of_nonneg_left (mul_le_mul (hu s a) (hA' s a) (abs_nonneg _) hK)
            ENNReal.toReal_nonneg
      _ = K * M := by rw [← Finset.sum_mul, probability_sum, one_mul]
  have hdX (s : S) : |X' s - X s| ≤ δ * K * M + K * M2 := by
    have hsplit : X' s - X s = ∑ a, ((π' s a).toReal - (π s a).toReal) * u s a * Ad' s a +
        ∑ a, (π s a).toReal * u s a * (Ad' s a - Ad s a) := by
      simp only [X, X', ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun a _ => by ring
    rw [hsplit]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · calc _ ≤ ∑ a, |((π' s a).toReal - (π s a).toReal) * u s a * Ad' s a| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ a, |(π' s a).toReal - (π s a).toReal| * (K * M) := Finset.sum_le_sum fun a _ => by
            rw [abs_mul, abs_mul, mul_assoc]
            exact mul_le_mul_of_nonneg_left (mul_le_mul (hu s a) (hA' s a) (abs_nonneg _) hK)
              (abs_nonneg _)
        _ ≤ δ * (K * M) := by
            rw [← Finset.sum_mul]; exact mul_le_mul_of_nonneg_right (hδ s) (by positivity)
        _ = δ * K * M := by ring
    · calc _ ≤ ∑ a, |(π s a).toReal * u s a * (Ad' s a - Ad s a)| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ a, (π s a).toReal * (K * M2) := Finset.sum_le_sum fun a _ => by
            rw [abs_mul, abs_mul, abs_of_nonneg ENNReal.toReal_nonneg, mul_assoc]
            exact mul_le_mul_of_nonneg_left (mul_le_mul (hu s a) (hdA s a) (abs_nonneg _) hK)
              ENNReal.toReal_nonneg
        _ = K * M2 := by rw [← Finset.sum_mul, probability_sum, one_mul]
  have hsplit : m.directionalGain π' hγ0 hγ1 u s₀ - m.directionalGain π hγ0 hγ1 u s₀ =
      ∑ s, (d' s - d s) * X' s + ∑ s, d s * (X' s - X s) := by
    simp only [directionalGain, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun s _ => by simp only [X, X', d, d', Ad, Ad']; ring
  have hvis := m.sum_abs_discountedVisitation_sub_le_of_le π π' hγ0 hγ1 hδ s₀
  have h1 : |∑ s, (d' s - d s) * X' s| ≤ γ / (1 - γ) * δ * (K * M) := by
    calc _ ≤ ∑ s, |(d' s - d s) * X' s| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ s, |d' s - d s| * (K * M) := Finset.sum_le_sum fun s _ => by
          rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hX' s) (abs_nonneg _)
      _ ≤ _ := by
          rw [← Finset.sum_mul]; exact mul_le_mul_of_nonneg_right hvis (by positivity)
  have h2 : |∑ s, d s * (X' s - X s)| ≤ δ * K * M + K * M2 := by
    calc _ ≤ ∑ s, |d s * (X' s - X s)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ s, d s * (δ * K * M + K * M2) := Finset.sum_le_sum fun s _ => by
          rw [abs_mul, abs_of_nonneg (m.discountedVisitation_nonneg π hγ0 hγ1 s₀ s)]
          exact mul_le_mul_of_nonneg_left (hdX s) (m.discountedVisitation_nonneg π hγ0 hγ1 s₀ s)
      _ = _ := by rw [← Finset.sum_mul, m.sum_discountedVisitation, one_mul]
  rw [hsplit]
  refine (abs_add_le _ _).trans ((add_le_add h1 h2).trans ?_)
  have htot : γ / (1 - γ) * δ * (K * M) + (δ * K * M + K * M2) =
      K * δ * (2 + γ) / (1 - γ) ^ 2 := by
    simp only [M, M2]; field_simp; ring
  rw [htot]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have : 0 ≤ K * δ := by positivity
  nlinarith

/-- The derivative of the softmax policy value along the line `θ + x * u`, at any point `x`. -/
theorem hasDerivAt_policyValue_softmax_line (m : MDP S A) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (θ u : S → A → ℝ) (s₀ : S) (x : ℝ) :
    HasDerivAt (fun t => m.policyValue (softmaxPolicy fun s a => θ s a + t * u s a) hγ0 hγ1 s₀)
      ((1 - γ)⁻¹ * m.directionalGain (softmaxPolicy fun s a => θ s a + x * u s a) hγ0 hγ1 u s₀)
      x := by
  unfold directionalGain
  have h := m.hasDerivAt_policyValue_softmax hγ0 hγ1 (fun s a => θ s a + x * u s a) u s₀
  have h' := HasDerivAt.comp_sub_const x x (by simpa using h)
  convert h' using 1
  funext y
  congr 2
  funext s a
  ring

/-- **Ascent lemma for softmax policies.** Moving the scores by `t * u` with `t ≥ 0` and
`|u| ≤ K` changes the value by at least `t` times the directional derivative minus
`3 * K ^ 2 * t ^ 2 / (1 - γ) ^ 3`, for rewards in `[0, 1]`. -/
theorem policyValue_softmax_line_ge (m : MDP S A) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) {K : ℝ}
    (hr : ∀ s a, m.reward s a ∈ Set.Icc (0 : ℝ) 1) (θ u : S → A → ℝ) (hu : ∀ s a, |u s a| ≤ K)
    (s₀ : S) {t : ℝ} (ht : 0 ≤ t) :
    m.policyValue (softmaxPolicy θ) hγ0 hγ1 s₀ +
        t * ((1 - γ)⁻¹ * m.directionalGain (softmaxPolicy θ) hγ0 hγ1 u s₀) -
          3 * K ^ 2 * t ^ 2 / (1 - γ) ^ 3 ≤
      m.policyValue (softmaxPolicy fun s a => θ s a + t * u s a) hγ0 hγ1 s₀ := by
  have hγ : 0 < 1 - γ := sub_pos.mpr hγ1
  set f : ℝ → ℝ := fun x =>
    m.policyValue (softmaxPolicy fun s a => θ s a + x * u s a) hγ0 hγ1 s₀
  set D : ℝ → ℝ := fun x =>
    (1 - γ)⁻¹ * m.directionalGain (softmaxPolicy fun s a => θ s a + x * u s a) hγ0 hγ1 u s₀
  set L := 6 * K ^ 2 / (1 - γ) ^ 3
  have hθ : (softmaxPolicy fun s a => θ s a + (0 : ℝ) * u s a) = softmaxPolicy θ := by simp
  have hf (x : ℝ) : HasDerivAt f (D x) x := m.hasDerivAt_policyValue_softmax_line hγ0 hγ1 θ u s₀ x
  have hD (x : ℝ) : |D x - D 0| ≤ L * |x| := by
    have h := m.abs_directionalGain_sub_le (softmaxPolicy θ)
      (softmaxPolicy fun s a => θ s a + x * u s a) hγ0 hγ1 hr
      (sum_abs_softmaxPolicy_sub_le θ u hu x) u hu s₀
    simp only [D, hθ, ← mul_sub, abs_mul, abs_inv, abs_of_pos hγ]
    calc (1 - γ)⁻¹ * |_| ≤ (1 - γ)⁻¹ * (3 * K * (2 * K * |x|) / (1 - γ) ^ 2) :=
          mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hγ.le)
      _ = L * |x| := by simp only [L]; field_simp; ring
  set g : ℝ → ℝ := fun x => f x - x * D 0 + L / 2 * x ^ 2
  have hg (x : ℝ) : HasDerivAt g (D x - D 0 + L * x) x := by
    have := ((hf x).sub ((hasDerivAt_id x).mul_const (D 0))).add
      ((hasDerivAt_pow 2 x).const_mul (L / 2))
    convert this using 1
    · funext y
      simp only [g, Pi.add_apply, Pi.sub_apply, id]
    · norm_num
      ring
  have hmono : MonotoneOn g (Set.Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (fun x _ => (hg x).continuousAt.continuousWithinAt)
      (fun x _ => (hg x).differentiableAt.differentiableWithinAt) fun x hx => ?_
    rw [interior_Ici, Set.mem_Ioi] at hx
    rw [(hg x).deriv]
    have h := hD x
    rw [abs_of_pos hx] at h
    linarith [neg_abs_le (D x - D 0)]
  have h := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr ht) ht
  simp only [g, f, D, zero_mul, add_zero] at h
  have hL : L / 2 * t ^ 2 = 3 * K ^ 2 * t ^ 2 / (1 - γ) ^ 3 := by simp only [L]; ring
  linarith

end MDP

end Rlib
