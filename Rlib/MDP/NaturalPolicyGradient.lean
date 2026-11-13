module

public import Rlib.MDP.Softmax

/-! # Natural policy gradient for softmax policies

This file follows Agarwal, Kakade, Lee, and Mahajan, *On the Theory of Policy Gradient
Methods* (JMLR 2021), Section 5.3. For softmax policies, natural policy gradient updates the
scores by `θ ← θ + η / (1 - γ) * A`, where `A` is the advantage of the current policy. Each step
improves the value at every state. Starting from `θ⁽⁰⁾ = 0` with rewards in `[0, 1]`,
`sum_sub_policyValue_npg_le` is their Theorem 16: for every `T > 0`,
`V* ρ - V⁽ᵀ⁾ ρ ≤ log |A| / (η * T) + 1 / ((1 - γ) ^ 2 * T)`. The comparison policy may be any
stationary policy, in particular an optimal one.
-/

@[expose] public section

noncomputable section

namespace Rlib

variable {S A : Type*} [Fintype A] [Nonempty A]

/-- **Gibbs inequality for softmax scores.** The log-normalizer changes from scores `y` to
scores `x` by at most the average score change under the softmax policy of `x`. -/
theorem log_sum_exp_sub_le (x y : S → A → ℝ) (s : S) :
    Real.log (∑ b, Real.exp (x s b)) - Real.log (∑ b, Real.exp (y s b)) ≤
      ∑ a, (softmaxPolicy x s a).toReal * (x s a - y s a) := by
  set Lx := Real.log (∑ b, Real.exp (x s b))
  set Ly := Real.log (∑ b, Real.exp (y s b))
  have hZx : 0 < ∑ b, Real.exp (x s b) :=
    Finset.sum_pos (fun b _ => Real.exp_pos _) Finset.univ_nonempty
  have hZy : 0 < ∑ b, Real.exp (y s b) :=
    Finset.sum_pos (fun b _ => Real.exp_pos _) Finset.univ_nonempty
  set p : A → ℝ := fun a => (softmaxPolicy x s a).toReal
  have hp (a : A) : p a = Real.exp (x s a - Lx) := by
    simp only [p, softmaxPolicy_apply, Real.exp_sub, Lx, Real.exp_log hZx]
  have hsum : ∑ a, p a = 1 := probability_sum _
  have hsumy : ∑ a, Real.exp (y s a - Ly) = 1 := by
    simp only [Real.exp_sub, Ly, Real.exp_log hZy, ← Finset.sum_div, div_self hZy.ne']
  have key (a : A) : p a * (1 + ((y s a - Ly) - (x s a - Lx))) ≤ Real.exp (y s a - Ly) := by
    rw [hp]
    calc Real.exp (x s a - Lx) * (1 + ((y s a - Ly) - (x s a - Lx)))
        ≤ Real.exp (x s a - Lx) * Real.exp ((y s a - Ly) - (x s a - Lx)) :=
          mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp ((y s a - Ly) -
            (x s a - Lx))]) (Real.exp_pos _).le
      _ = Real.exp (y s a - Ly) := by rw [← Real.exp_add]; ring_nf
  have h := Finset.sum_le_sum fun a (_ : a ∈ Finset.univ) => key a
  rw [hsumy] at h
  have hexp : ∑ a, p a * (1 + ((y s a - Ly) - (x s a - Lx))) =
      1 + (Lx - Ly) - ∑ a, p a * (x s a - y s a) := by
    have (a : A) : p a * (1 + ((y s a - Ly) - (x s a - Lx))) =
        p a * (1 + (Lx - Ly)) - p a * (x s a - y s a) := by ring
    simp only [this, Finset.sum_sub_distrib, ← Finset.sum_mul, hsum, one_mul]
  linarith

/-- Any average of action scores is at most their log-sum-exp. -/
theorem expect_le_log_sum_exp (q : PMF A) (θ : S → A → ℝ) (s : S) :
    expect q (θ s) ≤ Real.log (∑ b, Real.exp (θ s b)) := by
  calc expect q (θ s) ≤ expect q (fun _ => Real.log (∑ b, Real.exp (θ s b))) :=
        expect_mono q fun a => by
          rw [Real.le_log_iff_exp_le (Finset.sum_pos (fun b _ => Real.exp_pos _)
            Finset.univ_nonempty)]
          exact Finset.single_le_sum (fun b _ => (Real.exp_pos (θ s b)).le)
            (Finset.mem_univ a)
    _ = _ := expect_const _ _

namespace MDP

variable [Fintype S] [DecidableEq S]

omit [Nonempty A] in
/-- A policy visits its start state with discounted weight at least `1 - γ`. -/
theorem one_sub_le_discountedVisitation_self (m : MDP S A) (π : StationaryPolicy S A) {γ : ℝ}
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (s : S) :
    1 - γ ≤ m.discountedVisitation π hγ0 hγ1 s s := by
  set m' := m.withReward fun t _ => if t = s then (1 : ℝ) else 0
  set W := m'.policyValue π hγ0 hγ1
  have hW : 0 ≤ W := fun t => by
    have h := m.discountedVisitation_nonneg π hγ0 hγ1 t s
    unfold discountedVisitation at h
    by_contra hneg
    nlinarith [mul_neg_of_pos_of_neg (sub_pos.mpr hγ1) (not_le.mp hneg)]
  have hfix : m'.oneStepValue π γ W s = W s :=
    congrFun (m'.oneStepValue_policyValue π hγ0 hγ1) s
  have hone : 1 ≤ W s := by
    rw [← hfix]
    calc (1 : ℝ) = expect (π s) (fun _ => 1) := (expect_const _ _).symm
      _ ≤ _ := expect_mono _ fun a => by
          have h := expect_mono (m.transition s a) (f := fun _ => 0) (g := W) hW
          rw [expect_zero] at h
          simp only [oneStepActionValue, m', withReward, ↓reduceIte]
          nlinarith
  change 1 - γ ≤ (1 - γ) * W s
  nlinarith [sub_pos.mpr hγ1]

/-- The action scores after `t` steps of natural policy gradient with step size `η`, starting
from scores `θ₀`. Each step adds `η / (1 - γ)` times the advantage of the current softmax
policy. -/
def npgScores (m : MDP S A) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (η : ℝ)
    (θ₀ : S → A → ℝ) : ℕ → S → A → ℝ
  | 0 => θ₀
  | t + 1 => fun s a => m.npgScores hγ0 hγ1 η θ₀ t s a +
      η / (1 - γ) * m.advantage (softmaxPolicy (m.npgScores hγ0 hγ1 η θ₀ t)) hγ0 hγ1 s a

omit [Nonempty A] [DecidableEq S] in
/-- With rewards bounded by `R` in absolute value, every policy value is bounded by
`R / (1 - γ)`. -/
theorem abs_policyValue_le (m : MDP S A) (π : StationaryPolicy S A) {γ : ℝ} (hγ0 : 0 ≤ γ)
    (hγ1 : γ < 1) {R : ℝ} (hR : ∀ s a, |m.reward s a| ≤ R) (s : S) :
    |m.policyValue π hγ0 hγ1 s| ≤ R / (1 - γ) := by
  set v := m.policyValue π hγ0 hγ1
  have hA : Nonempty A := (π s).support_nonempty.to_subtype.map Subtype.val
  have hR0 : 0 ≤ R := (abs_nonneg _).trans (hR s (Classical.arbitrary A))
  have hnorm : ‖v‖ ≤ R + γ * ‖v‖ := by
    refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun t => ?_
    have hfix : m.oneStepValue π γ v t = v t :=
      congrFun (m.oneStepValue_policyValue π hγ0 hγ1) t
    rw [← hfix]
    have h := norm_expect_sub_expect_le (π t) (m.oneStepActionValue γ v t) 0
    rw [show expect (π t) (0 : A → ℝ) = 0 from expect_zero _, sub_zero, sub_zero] at h
    refine h.trans ((pi_norm_le_iff_of_nonneg (by positivity)).mpr fun a => ?_)
    have hP := norm_expect_sub_expect_le (m.transition t a) v 0
    rw [show expect (m.transition t a) (0 : S → ℝ) = 0 from expect_zero _, sub_zero,
      sub_zero] at hP
    simp only [oneStepActionValue, Real.norm_eq_abs] at hP ⊢
    calc |m.reward t a + γ * expect (m.transition t a) v|
        ≤ |m.reward t a| + γ * |expect (m.transition t a) v| := by
          calc _ ≤ |m.reward t a| + |γ * expect (m.transition t a) v| := abs_add_le _ _
            _ = _ := by rw [abs_mul, abs_of_nonneg hγ0]
      _ ≤ R + γ * ‖v‖ := add_le_add (hR t a) (mul_le_mul_of_nonneg_left hP hγ0)
  rw [le_div_iff₀ (sub_pos.mpr hγ1)]
  have := norm_le_pi_norm v s
  rw [Real.norm_eq_abs] at this
  nlinarith

omit [Nonempty A] [DecidableEq S] in
/-- With rewards in `[0, 1]`, every policy value lies in `[0, 1 / (1 - γ)]`. -/
theorem policyValue_mem_Icc (m : MDP S A) (π : StationaryPolicy S A) {γ : ℝ} (hγ0 : 0 ≤ γ)
    (hγ1 : γ < 1) (hr : ∀ s a, m.reward s a ∈ Set.Icc (0 : ℝ) 1) (s : S) :
    m.policyValue π hγ0 hγ1 s ∈ Set.Icc 0 (1 / (1 - γ)) := by
  refine ⟨m.policyValue_nonneg π hγ0 hγ1 (fun t => ?_) s, ?_⟩
  · have h := expect_mono (π t) (f := fun _ => 0) (g := m.reward t) fun a => (hr t a).1
    rwa [expect_zero] at h
  · have h := m.abs_policyValue_le π hγ0 hγ1 (R := 1)
      (fun t a => abs_le.mpr ⟨by linarith [(hr t a).1], (hr t a).2⟩) s
    exact (le_abs_self _).trans h

section

variable (m : MDP S A) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (η : ℝ)
  (θ₀ : S → A → ℝ)

omit [DecidableEq S] in
/-- The log-normalizer of the natural policy gradient scores never decreases, whatever the step
size. -/
theorem log_sum_exp_npgScores_le_succ (t : ℕ) (s : S) :
    Real.log (∑ b, Real.exp (m.npgScores hγ0 hγ1 η θ₀ t s b)) ≤
      Real.log (∑ b, Real.exp (m.npgScores hγ0 hγ1 η θ₀ (t + 1) s b)) := by
  set θ := m.npgScores hγ0 hγ1 η θ₀ t
  set Adv := m.advantage (softmaxPolicy θ) hγ0 hγ1
  have h := log_sum_exp_sub_le θ (m.npgScores hγ0 hγ1 η θ₀ (t + 1)) s
  have hzero := m.expect_advantage (softmaxPolicy θ) hγ0 hγ1 s
  have hrhs : ∑ a, (softmaxPolicy θ s a).toReal *
      (θ s a - m.npgScores hγ0 hγ1 η θ₀ (t + 1) s a) =
        -(η / (1 - γ)) * expect (softmaxPolicy θ s) (Adv s) := by
    simp only [npgScores, expect, Finset.mul_sum, θ, Adv]
    exact Finset.sum_congr rfl fun a _ => by ring
  rw [hrhs, hzero, mul_zero] at h
  linarith

/-- **Natural policy gradient improves every state.** For a positive step size, one step raises
the value at each state by at least the rise in the log-normalizer divided by `η / (1 - γ)`. -/
theorem log_sum_exp_npgScores_succ_sub_le {η : ℝ} (hη : 0 < η) (t : ℕ) (s : S) :
    Real.log (∑ b, Real.exp (m.npgScores hγ0 hγ1 η θ₀ (t + 1) s b)) -
        Real.log (∑ b, Real.exp (m.npgScores hγ0 hγ1 η θ₀ t s b)) ≤
      η / (1 - γ) * (m.policyValue (softmaxPolicy (m.npgScores hγ0 hγ1 η θ₀ (t + 1))) hγ0 hγ1 s -
        m.policyValue (softmaxPolicy (m.npgScores hγ0 hγ1 η θ₀ t)) hγ0 hγ1 s) := by
  have hα : 0 < η / (1 - γ) := div_pos hη (sub_pos.mpr hγ1)
  set θ := m.npgScores hγ0 hγ1 η θ₀ t
  set θ' := m.npgScores hγ0 hγ1 η θ₀ (t + 1)
  set Adv := m.advantage (softmaxPolicy θ) hγ0 hγ1
  set g : S → ℝ := fun s' => expect (softmaxPolicy θ' s') (Adv s')
  have hg (s' : S) :
      Real.log (∑ b, Real.exp (θ' s' b)) - Real.log (∑ b, Real.exp (θ s' b)) ≤
        η / (1 - γ) * g s' := by
    have h := log_sum_exp_sub_le θ' θ s'
    have hrhs : ∑ a, (softmaxPolicy θ' s' a).toReal * (θ' s' a - θ s' a) =
        η / (1 - γ) * g s' := by
      simp only [θ', npgScores, g, expect, Finset.mul_sum, θ, Adv]
      exact Finset.sum_congr rfl fun a _ => by ring
    rwa [hrhs] at h
  have hg0 (s' : S) : 0 ≤ g s' := by
    have h1 := hg s'
    have h2 := m.log_sum_exp_npgScores_le_succ hγ0 hγ1 η θ₀ t s'
    by_contra hneg
    nlinarith [mul_neg_of_pos_of_neg hα (not_le.mp hneg)]
  have hpdl :=
    m.sub_policyValue_eq_sum_visitation (softmaxPolicy θ) (softmaxPolicy θ') hγ0 hγ1 s
  have hsingle : m.discountedVisitation (softmaxPolicy θ') hγ0 hγ1 s s * g s ≤
      ∑ s', m.discountedVisitation (softmaxPolicy θ') hγ0 hγ1 s s' * g s' :=
    Finset.single_le_sum (f := fun s' => m.discountedVisitation (softmaxPolicy θ') hγ0 hγ1 s s' *
      g s') (fun s' _ => mul_nonneg (m.discountedVisitation_nonneg _ hγ0 hγ1 s s') (hg0 s'))
      (Finset.mem_univ s)
  have hself := m.one_sub_le_discountedVisitation_self (softmaxPolicy θ') hγ0 hγ1 s
  have hlow : (1 - γ) * g s ≤
      (1 - γ) * (m.policyValue (softmaxPolicy θ') hγ0 hγ1 s -
        m.policyValue (softmaxPolicy θ) hγ0 hγ1 s) := by
    rw [hpdl]
    exact (mul_le_mul_of_nonneg_right hself (hg0 s)).trans hsingle
  have hdiff := le_of_mul_le_mul_left hlow (sub_pos.mpr hγ1)
  exact (hg s).trans (mul_le_mul_of_nonneg_left hdiff hα.le)

/-- With a positive step size, natural policy gradient never lowers the value at any state. -/
theorem policyValue_npg_mono {η : ℝ} (hη : 0 < η) (s : S) {t T : ℕ} (htT : t ≤ T) :
    m.policyValue (softmaxPolicy (m.npgScores hγ0 hγ1 η θ₀ t)) hγ0 hγ1 s ≤
      m.policyValue (softmaxPolicy (m.npgScores hγ0 hγ1 η θ₀ T)) hγ0 hγ1 s := by
  refine monotone_nat_of_le_succ (f := fun n =>
    m.policyValue (softmaxPolicy (m.npgScores hγ0 hγ1 η θ₀ n)) hγ0 hγ1 s) (fun n => ?_) htT
  have h1 := m.log_sum_exp_npgScores_succ_sub_le hγ0 hγ1 θ₀ hη n s
  have h2 := m.log_sum_exp_npgScores_le_succ hγ0 hγ1 η θ₀ n s
  have hα : 0 < η / (1 - γ) := div_pos hη (sub_pos.mpr hγ1)
  by_contra hneg
  nlinarith [mul_neg_of_pos_of_neg hα (sub_neg.mpr (not_le.mp hneg))]

/-- At each state, the comparison policy's summed advantages against the natural policy gradient
iterates are bounded by a starting term plus the total value gain. -/
theorem sum_expect_advantage_npg_le {η : ℝ} (hη : 0 < η) (π' : StationaryPolicy S A) (T : ℕ)
    (s : S) :
    η / (1 - γ) * ∑ t ∈ Finset.range T, expect (π' s)
        (m.advantage (softmaxPolicy (m.npgScores hγ0 hγ1 η θ₀ t)) hγ0 hγ1 s) ≤
      Real.log (∑ b, Real.exp (θ₀ s b)) - expect (π' s) (θ₀ s) +
        η / (1 - γ) * (m.policyValue (softmaxPolicy (m.npgScores hγ0 hγ1 η θ₀ T)) hγ0 hγ1 s -
          m.policyValue (softmaxPolicy (m.npgScores hγ0 hγ1 η θ₀ 0)) hγ0 hγ1 s) := by
  set θ := m.npgScores hγ0 hγ1 η θ₀
  set V : ℕ → ℝ := fun t => m.policyValue (softmaxPolicy (θ t)) hγ0 hγ1 s
  set L : ℕ → ℝ := fun t => Real.log (∑ b, Real.exp (θ t s b))
  set c : ℕ → ℝ := fun t => expect (π' s) (θ t s)
  have hstep (t : ℕ) :
      η / (1 - γ) * expect (π' s) (m.advantage (softmaxPolicy (θ t)) hγ0 hγ1 s) =
      c (t + 1) - c t := by
    simp only [c, θ, npgScores]
    rw [expect_add, expect_mul]
    ring
  have hscore : η / (1 - γ) * ∑ t ∈ Finset.range T,
      expect (π' s) (m.advantage (softmaxPolicy (θ t)) hγ0 hγ1 s) = c T - c 0 := by
    rw [Finset.mul_sum, Finset.sum_congr rfl fun t _ => hstep t, Finset.sum_range_sub]
  have hL : L T - L 0 ≤ η / (1 - γ) * (V T - V 0) := by
    rw [← Finset.sum_range_sub, ← Finset.sum_range_sub, Finset.mul_sum]
    exact Finset.sum_le_sum fun t _ => m.log_sum_exp_npgScores_succ_sub_le hγ0 hγ1 θ₀ hη t s
  have hcT : c T ≤ L T := expect_le_log_sum_exp _ _ _
  change η / (1 - γ) * ∑ t ∈ Finset.range T,
      expect (π' s) (m.advantage (softmaxPolicy (θ t)) hγ0 hγ1 s) ≤
        L 0 - c 0 + η / (1 - γ) * (V T - V 0)
  linarith

/-- **Natural policy gradient converges at rate `1 / T`.** After `T` steps with step size
`η > 0`, `(1 - γ) * T` times the value gap to any policy `π'` is at most the average, under the
visitation of `π'`, of `1 - γ` times a starting term divided by `η` plus the total value
gain. -/
theorem policyValue_sub_npg_le {η : ℝ} (hη : 0 < η) (π' : StationaryPolicy S A) (T : ℕ)
    (s₀ : S) :
    (1 - γ) * T * (m.policyValue π' hγ0 hγ1 s₀ -
        m.policyValue (softmaxPolicy (m.npgScores hγ0 hγ1 η θ₀ T)) hγ0 hγ1 s₀) ≤
      ∑ s, m.discountedVisitation π' hγ0 hγ1 s₀ s *
        ((1 - γ) * (Real.log (∑ b, Real.exp (θ₀ s b)) - expect (π' s) (θ₀ s)) / η +
          (m.policyValue (softmaxPolicy (m.npgScores hγ0 hγ1 η θ₀ T)) hγ0 hγ1 s -
            m.policyValue (softmaxPolicy (m.npgScores hγ0 hγ1 η θ₀ 0)) hγ0 hγ1 s)) := by
  set θ := m.npgScores hγ0 hγ1 η θ₀
  set V' := m.policyValue π' hγ0 hγ1
  set V : ℕ → S → ℝ := fun t => m.policyValue (softmaxPolicy (θ t)) hγ0 hγ1
  set d := m.discountedVisitation π' hγ0 hγ1 s₀
  set G : ℕ → S → ℝ := fun t s =>
    expect (π' s) (m.advantage (softmaxPolicy (θ t)) hγ0 hγ1 s)
  have hγ : 0 ≤ 1 - γ := sub_nonneg.mpr hγ1.le
  have hstate (s : S) : ∑ t ∈ Finset.range T, G t s ≤
      (1 - γ) * (Real.log (∑ b, Real.exp (θ₀ s b)) - expect (π' s) (θ₀ s)) / η +
        (V T s - V 0 s) := by
    have h := m.sum_expect_advantage_npg_le hγ0 hγ1 θ₀ hη π' T s
    have hα : 0 < η / (1 - γ) := div_pos hη (sub_pos.mpr hγ1)
    rw [show (1 - γ) * (Real.log (∑ b, Real.exp (θ₀ s b)) - expect (π' s) (θ₀ s)) / η =
      (Real.log (∑ b, Real.exp (θ₀ s b)) - expect (π' s) (θ₀ s)) / (η / (1 - γ)) by
        field_simp]
    rw [div_add' _ _ _ hα.ne', le_div_iff₀ hα]
    change η / (1 - γ) * ∑ t ∈ Finset.range T, G t s ≤ _ at h
    linarith
  calc (1 - γ) * T * (V' s₀ - V T s₀)
      = ∑ t ∈ Finset.range T, (1 - γ) * (V' s₀ - V T s₀) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
    _ ≤ ∑ t ∈ Finset.range T, (1 - γ) * (V' s₀ - V t s₀) := by
        refine Finset.sum_le_sum fun t ht => mul_le_mul_of_nonneg_left ?_ hγ
        have := m.policyValue_npg_mono hγ0 hγ1 θ₀ hη s₀ (Finset.mem_range.mp ht).le
        linarith
    _ = ∑ t ∈ Finset.range T, ∑ s, d s * G t s :=
        Finset.sum_congr rfl fun t _ =>
          m.sub_policyValue_eq_sum_visitation (softmaxPolicy (θ t)) π' hγ0 hγ1 s₀
    _ = ∑ s, d s * ∑ t ∈ Finset.range T, G t s := by
        rw [Finset.sum_comm]; simp only [Finset.mul_sum]
    _ ≤ _ := Finset.sum_le_sum fun s _ =>
        mul_le_mul_of_nonneg_left (hstate s) (m.discountedVisitation_nonneg π' hγ0 hγ1 s₀ s)

/-- **Natural policy gradient converges at rate `1 / T` (Agarwal et al., Theorem 16).** With
rewards in `[0, 1]`, initial scores `θ⁽⁰⁾ = 0`, step size `η > 0`, and any start distribution `ρ`,
after `T > 0` steps the value gap to any policy `π'` satisfies
`V^{π'} ρ - V⁽ᵀ⁾ ρ ≤ log |A| / (η * T) + 1 / ((1 - γ) ^ 2 * T)`. -/
theorem sum_sub_policyValue_npg_le (hr : ∀ s a, m.reward s a ∈ Set.Icc (0 : ℝ) 1) {η : ℝ}
    (hη : 0 < η) (π' : StationaryPolicy S A) {ρ : S → ℝ} (hρ : ∀ s, 0 ≤ ρ s)
    (hρ1 : ∑ s, ρ s = 1) {T : ℕ} (hT : 0 < T) :
    ∑ s₀, ρ s₀ * (m.policyValue π' hγ0 hγ1 s₀ -
        m.policyValue (softmaxPolicy (m.npgScores hγ0 hγ1 η (fun _ _ => 0) T)) hγ0 hγ1 s₀) ≤
      Real.log (Fintype.card A) / (η * T) + 1 / ((1 - γ) ^ 2 * T) := by
  have hγ : 0 < 1 - γ := sub_pos.mpr hγ1
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
  set V := fun t =>
    m.policyValue (softmaxPolicy (m.npgScores hγ0 hγ1 η (fun _ _ => 0) t)) hγ0 hγ1
  set B := Real.log (Fintype.card A) / (η * T) + 1 / ((1 - γ) ^ 2 * T)
  have hstate (s₀ : S) : m.policyValue π' hγ0 hγ1 s₀ - V T s₀ ≤ B := by
    have h := m.policyValue_sub_npg_le hγ0 hγ1 (fun _ _ => 0) hη π' T s₀
    have hbound (s : S) :
        (1 - γ) * (Real.log (∑ _b : A, Real.exp 0) - expect (π' s) (fun _ => 0)) / η +
          (V T s - V 0 s) ≤ (1 - γ) * Real.log (Fintype.card A) / η + 1 / (1 - γ) := by
      have h1 := (m.policyValue_mem_Icc
        (softmaxPolicy (m.npgScores hγ0 hγ1 η (fun _ _ => 0) T)) hγ0 hγ1 hr s).2
      have h2 := (m.policyValue_mem_Icc
        (softmaxPolicy (m.npgScores hγ0 hγ1 η (fun _ _ => 0) 0)) hγ0 hγ1 hr s).1
      simp only [Real.exp_zero, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
        expect_zero, sub_zero]
      change _ + (V T s - V 0 s) ≤ _ at *
      linarith
    have hsum : ∑ s, m.discountedVisitation π' hγ0 hγ1 s₀ s *
        ((1 - γ) * (Real.log (∑ _b : A, Real.exp 0) - expect (π' s) (fun _ => 0)) / η +
          (V T s - V 0 s)) ≤ (1 - γ) * Real.log (Fintype.card A) / η + 1 / (1 - γ) := by
      calc _ ≤ ∑ s, m.discountedVisitation π' hγ0 hγ1 s₀ s *
            ((1 - γ) * Real.log (Fintype.card A) / η + 1 / (1 - γ)) :=
            Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (hbound s)
              (m.discountedVisitation_nonneg π' hγ0 hγ1 s₀ s)
        _ = _ := by rw [← Finset.sum_mul, m.sum_discountedVisitation, one_mul]
    change (1 - γ) * T * (m.policyValue π' hγ0 hγ1 s₀ - V T s₀) ≤ _ at h
    have hB : (1 - γ) * T * B = (1 - γ) * Real.log (Fintype.card A) / η + 1 / (1 - γ) := by
      simp only [B]; field_simp
    have hpos : 0 < (1 - γ) * T := mul_pos hγ hTpos
    rw [← hB] at hsum
    exact le_of_mul_le_mul_left (h.trans hsum) hpos
  calc _ ≤ ∑ s₀, ρ s₀ * B := Finset.sum_le_sum fun s₀ _ =>
        mul_le_mul_of_nonneg_left (hstate s₀) (hρ s₀)
    _ = B := by rw [← Finset.sum_mul, hρ1, one_mul]

end

end MDP

end Rlib
