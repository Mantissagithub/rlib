module

public import Rlib.MDP.KLPenaltyPPO
public import Rlib.MDP.SoftmaxPolicyGradient

/-! # Linear convergence of policy mirror descent

This file follows Xiao, *On the Convergence Rates of Policy Gradient Methods* (JMLR 2022),
Section 4.2, for the KL divergence. Policy mirror descent with step sizes `η k` moves from
`π_k` to the policy that maximizes `η k * E_p A_k - KL (p ‖ π_k s)` at every state, which for
softmax policies adds `η k * A_k` to the scores (`pmdScores`). Xiao states the update with
action values `Q`; advantages differ from them by a constant at each state, which gives the same
softmax policy. Xiao minimizes costs; here rewards are maximized.

For the KL divergence, Xiao's three-point lemma (his Lemma 6, cited without proof) is an exact
identity, `three_point_softmax`, a consequence of the Gibbs variational identity.

`pmd_linear_convergence` is Xiao's Theorem 10. Let `ρ ≥ 0` weight start states and `π⋆` be any
comparison policy, and suppose `d_ρ (π⋆) s ≤ (1 - γ) ϑ ρ s` for all `s` with `ϑ > 1`. Xiao takes
`ϑ` to be the smallest such constant, `ϑ_ρ = ‖d_ρ (π⋆) / ρ‖∞ / (1 - γ)`; the formal statement
holds for every such `ϑ`. If the step sizes are positive and `η (k + 1) ≥ ϑ / (ϑ - 1) * η k`,
then `V⋆_ρ - V_ρ (π_k) ≤ (1 - 1 / ϑ) ^ k * (V⋆_ρ - V_ρ (π_0) + D⋆_0 / ((1 - γ) η 0 (ϑ - 1)))`,
where `D⋆_k = ∑ s, d_ρ (π⋆) s * KL (π⋆ s ‖ π_k s)`. `pmd_linear_convergence'` is Xiao's displayed
form, with `D⋆_0 / (η 0 γ)`, for a start distribution `ρ` and `γ > 0`.
-/

@[expose] public section

noncomputable section

namespace Rlib

namespace MDP

variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty A] [DecidableEq S]
variable (m : MDP S A) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)

omit [Nonempty A] in
/-- **Performance difference lemma, weighted by start states.** -/
theorem sum_sub_policyValue_eq_weightedVisitation (π π' : StationaryPolicy S A) (ρ : S → ℝ) :
    (1 - γ) * ∑ s₀, ρ s₀ * (m.policyValue π' hγ0 hγ1 s₀ - m.policyValue π hγ0 hγ1 s₀) =
      ∑ s, m.weightedVisitation π' hγ0 hγ1 ρ s * expect (π' s) (m.advantage π hγ0 hγ1 s) := by
  simp only [Finset.mul_sum, weightedVisitation, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s₀ _ => ?_
  rw [mul_left_comm, m.sub_policyValue_eq_sum_visitation π _ hγ0 hγ1 s₀, Finset.mul_sum]
  exact Finset.sum_congr rfl fun s _ => by ring

omit [Fintype S] [DecidableEq S] in
/-- **Three-point identity for the KL divergence.** Adding `g` to softmax scores `θ` gives the
policy `π'` with `E_u g - KL (u ‖ π s) = E_{π' s} g - KL (π' s ‖ π s) - KL (u ‖ π' s)` for every
action distribution `u`. -/
theorem three_point_softmax (θ g : S → A → ℝ) (s : S) (u : PMF A) :
    expect u (g s) - kl u (softmaxPolicy θ s) =
      expect (softmaxPolicy (fun s a => θ s a + g s a) s) (g s) -
        kl (softmaxPolicy (fun s a => θ s a + g s a) s) (softmaxPolicy θ s) -
        kl u (softmaxPolicy (fun s a => θ s a + g s a) s) := by
  have e : (fun s a => θ s a + g s a / 1) = fun s a => θ s a + g s a := by simp
  have hr := softmaxPolicy_add_div θ g 1 s
  rw [e] at hr
  set r := softmaxPolicy (fun s a => θ s a + g s a) s
  have hid (p : PMF A) := expect_sub_mul_kl_eq p (softmaxPolicy θ s) r (g s) one_ne_zero
    (sum_softmaxPolicy_mul_exp_pos θ g 1 s) (softmaxPolicy_ne_zero θ s) hr
  have h1 := hid u
  have h2 := hid r
  rw [kl_self] at h2
  linarith

/-- The action scores of policy mirror descent with the KL divergence and step sizes `η k`,
starting from `θ₀`: each step adds `η k` times the advantage of the current softmax policy. -/
def pmdScores (m : MDP S A) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (η : ℕ → ℝ)
    (θ₀ : S → A → ℝ) : ℕ → S → A → ℝ
  | 0 => θ₀
  | k + 1 => fun s a => m.pmdScores hγ0 hγ1 η θ₀ k s a +
      η k * m.advantage (softmaxPolicy (m.pmdScores hγ0 hγ1 η θ₀ k)) hγ0 hγ1 s a

/-- **Xiao's Proposition 9, for the KL divergence.** With `η k > 0`, comparison policy `π⋆`,
weights `ρ ≥ 0`, and `d_ρ (π⋆) ≤ (1 - γ) ϑ ρ` with `ϑ ≥ 0`, one step of policy mirror descent
satisfies `η (1 - γ) δ_k ≤ η ϑ (1 - γ) (δ_k - δ_{k+1}) + D⋆_k - D⋆_{k+1}`, where `δ_k` is the
`ρ`-weighted gap to `π⋆` and `D⋆_k = ∑ s, d_ρ (π⋆) s * KL (π⋆ s ‖ π_k s)`. -/
theorem pmd_step (η : ℕ → ℝ) (θ₀ : S → A → ℝ) (k : ℕ) (hη : 0 < η k)
    (πstar : StationaryPolicy S A) {ρ : S → ℝ} (hρ : ∀ s, 0 ≤ ρ s) {ϑ : ℝ} (hϑ0 : 0 ≤ ϑ)
    (hϑ : ∀ s, m.weightedVisitation πstar hγ0 hγ1 ρ s ≤ (1 - γ) * ϑ * ρ s) :
    let π : ℕ → StationaryPolicy S A := fun k => softmaxPolicy (m.pmdScores hγ0 hγ1 η θ₀ k)
    let δ : ℕ → ℝ := fun k =>
      ∑ s₀, ρ s₀ * (m.policyValue πstar hγ0 hγ1 s₀ - m.policyValue (π k) hγ0 hγ1 s₀)
    let D : ℕ → ℝ := fun k =>
      ∑ s, m.weightedVisitation πstar hγ0 hγ1 ρ s * kl (πstar s) (π k s)
    η k * (1 - γ) * δ k ≤ η k * ϑ * (1 - γ) * (δ k - δ (k + 1)) + D k - D (k + 1) := by
  intro π δ D
  set dstar := m.weightedVisitation πstar hγ0 hγ1 ρ
  set dnext := m.weightedVisitation (π (k + 1)) hγ0 hγ1 ρ
  set Adv := m.advantage (π k) hγ0 hγ1
  set g : S → A → ℝ := fun s a => η k * Adv s a
  have hnext : π (k + 1) = softmaxPolicy (fun s a => m.pmdScores hγ0 hγ1 η θ₀ k s a + g s a) :=
    rfl
  have hγ : 0 ≤ 1 - γ := sub_nonneg.mpr hγ1.le
  have hexp (p : PMF A) (s : S) : expect p (g s) = η k * expect p (Adv s) := by
    simp only [g]
    exact expect_mul p (η k) (Adv s)
  -- The new policy has nonnegative expected advantage at every state.
  have hx (s : S) : 0 ≤ expect (π (k + 1) s) (Adv s) := by
    have h := three_point_softmax (m.pmdScores hγ0 hγ1 η θ₀ k) g s (π k s)
    rw [← hnext, kl_self, hexp, hexp] at h
    have h0 : expect (π k s) (Adv s) = 0 := m.expect_advantage (π k) hγ0 hγ1 s
    rw [h0] at h
    have := kl_nonneg_of_ne_zero (π (k + 1) s) (π k s) (softmaxPolicy_ne_zero _ s)
    have := kl_nonneg_of_ne_zero (π k s) (π (k + 1) s) (softmaxPolicy_ne_zero _ s)
    nlinarith
  -- The three-point identity at `u = π⋆ s`.
  have hy (s : S) : η k * expect (πstar s) (Adv s) ≤ η k * expect (π (k + 1) s) (Adv s) +
      kl (πstar s) (π k s) - kl (πstar s) (π (k + 1) s) := by
    have h := three_point_softmax (m.pmdScores hγ0 hγ1 η θ₀ k) g s (πstar s)
    rw [← hnext, hexp, hexp] at h
    have := kl_nonneg_of_ne_zero (π (k + 1) s) (π k s) (softmaxPolicy_ne_zero _ s)
    change _ - kl (πstar s) (π k s) = _ at h
    linarith
  have hpdl_star := m.sum_sub_policyValue_eq_weightedVisitation hγ0 hγ1 (π k) πstar ρ
  have hpdl_next := m.sum_sub_policyValue_eq_weightedVisitation hγ0 hγ1 (π k) (π (k + 1)) ρ
  have hδ : δ k - δ (k + 1) = ∑ s₀, ρ s₀ *
      (m.policyValue (π (k + 1)) hγ0 hγ1 s₀ - m.policyValue (π k) hγ0 hγ1 s₀) := by
    simp only [δ, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun s _ => by ring
  have hsum1 : η k * ∑ s, dstar s * expect (πstar s) (Adv s) ≤
      η k * ∑ s, dstar s * expect (π (k + 1) s) (Adv s) + D k - D (k + 1) := by
    simp only [D, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun s _ => ?_
    have hd : 0 ≤ dstar s := Finset.sum_nonneg fun s₀ _ =>
      mul_nonneg (hρ s₀) (m.discountedVisitation_nonneg πstar hγ0 hγ1 s₀ s)
    nlinarith [mul_le_mul_of_nonneg_left (hy s) hd]
  have hsum2 : ∑ s, dstar s * expect (π (k + 1) s) (Adv s) ≤
      ϑ * ∑ s, dnext s * expect (π (k + 1) s) (Adv s) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun s _ => ?_
    have hlow := m.mul_le_weightedVisitation (π (k + 1)) hγ0 hγ1 hρ s
    have h1 : dstar s ≤ ϑ * dnext s := by
      calc dstar s ≤ (1 - γ) * ϑ * ρ s := hϑ s
        _ = ϑ * ((1 - γ) * ρ s) := by ring
        _ ≤ ϑ * dnext s := mul_le_mul_of_nonneg_left hlow hϑ0
    nlinarith [mul_le_mul_of_nonneg_right h1 (hx s)]
  have hstar : ∑ s, dstar s * expect (πstar s) (Adv s) = (1 - γ) * δ k := by
    rw [← hpdl_star]
  have hnext' : ∑ s, dnext s * expect (π (k + 1) s) (Adv s) = (1 - γ) * (δ k - δ (k + 1)) := by
    rw [← hpdl_next, hδ]
  rw [hstar] at hsum1
  rw [hnext'] at hsum2
  nlinarith [mul_le_mul_of_nonneg_left hsum2 hη.le]

/-- **Linear convergence of policy mirror descent (Xiao, Theorem 10), for the KL divergence.**
With positive step sizes satisfying `ϑ * η k ≤ (ϑ - 1) * η (k + 1)`, weights `ρ ≥ 0`, and
`d_ρ (π⋆) ≤ (1 - γ) ϑ ρ` with `ϑ > 1`, the `ρ`-weighted gap to `π⋆` after `k` steps is at most
`(1 - 1 / ϑ) ^ k * (δ_0 + D⋆_0 / ((1 - γ) η 0 (ϑ - 1)))`. -/
theorem pmd_linear_convergence (η : ℕ → ℝ) (θ₀ : S → A → ℝ) (hη : ∀ k, 0 < η k)
    (πstar : StationaryPolicy S A) {ρ : S → ℝ} (hρ : ∀ s, 0 ≤ ρ s) {ϑ : ℝ} (hϑ1 : 1 < ϑ)
    (hϑ : ∀ s, m.weightedVisitation πstar hγ0 hγ1 ρ s ≤ (1 - γ) * ϑ * ρ s)
    (hstep : ∀ k, ϑ * η k ≤ (ϑ - 1) * η (k + 1)) (k : ℕ) :
    ∑ s₀, ρ s₀ * (m.policyValue πstar hγ0 hγ1 s₀ -
        m.policyValue (softmaxPolicy (m.pmdScores hγ0 hγ1 η θ₀ k)) hγ0 hγ1 s₀) ≤
      (1 - 1 / ϑ) ^ k * (∑ s₀, ρ s₀ * (m.policyValue πstar hγ0 hγ1 s₀ -
          m.policyValue (softmaxPolicy θ₀) hγ0 hγ1 s₀) +
        (∑ s, m.weightedVisitation πstar hγ0 hγ1 ρ s * kl (πstar s) (softmaxPolicy θ₀ s)) /
          ((1 - γ) * η 0 * (ϑ - 1))) := by
  set π : ℕ → StationaryPolicy S A := fun k => softmaxPolicy (m.pmdScores hγ0 hγ1 η θ₀ k)
  set δ : ℕ → ℝ := fun k =>
    ∑ s₀, ρ s₀ * (m.policyValue πstar hγ0 hγ1 s₀ - m.policyValue (π k) hγ0 hγ1 s₀)
  set D : ℕ → ℝ := fun k => ∑ s, m.weightedVisitation πstar hγ0 hγ1 ρ s * kl (πstar s) (π k s)
  set a : ℕ → ℝ := fun k => δ k + D k / ((1 - γ) * η k * (ϑ - 1))
  have hγ : 0 < 1 - γ := sub_pos.mpr hγ1
  have hϑ0 : 0 < ϑ := zero_lt_one.trans hϑ1
  have hϑm : 0 < ϑ - 1 := sub_pos.mpr hϑ1
  have hr0 : 0 ≤ 1 - 1 / ϑ := by
    rw [sub_nonneg, div_le_one hϑ0]; exact hϑ1.le
  have hD (k : ℕ) : 0 ≤ D k := Finset.sum_nonneg fun s _ => mul_nonneg
    (Finset.sum_nonneg fun s₀ _ => mul_nonneg (hρ s₀)
      (m.discountedVisitation_nonneg πstar hγ0 hγ1 s₀ s))
    (kl_nonneg_of_ne_zero _ _ (softmaxPolicy_ne_zero _ s))
  have hrec (k : ℕ) : a (k + 1) ≤ (1 - 1 / ϑ) * a k := by
    have h := m.pmd_step hγ0 hγ1 η θ₀ k (hη k) πstar hρ hϑ0.le hϑ
    change η k * (1 - γ) * δ k ≤ η k * ϑ * (1 - γ) * (δ k - δ (k + 1)) + D k - D (k + 1) at h
    have hηk := hη k
    have hηk1 := hη (k + 1)
    set E := η k * (1 - γ) * ϑ
    have hE : 0 < E := by positivity
    have hc : D (k + 1) / ((1 - γ) * η (k + 1) * (ϑ - 1)) ≤ D (k + 1) / E := by
      refine div_le_div_of_nonneg_left (hD _) hE ?_
      have := hstep k
      simp only [E]
      nlinarith
    have hrhs : (1 - 1 / ϑ) * a k = ((1 - γ) * η k * (ϑ - 1) * δ k + D k) / E := by
      simp only [a, E]
      field_simp
    have hlhs : δ (k + 1) + D (k + 1) / E = (E * δ (k + 1) + D (k + 1)) / E := by
      field_simp
    calc a (k + 1) = δ (k + 1) + D (k + 1) / ((1 - γ) * η (k + 1) * (ϑ - 1)) := rfl
      _ ≤ δ (k + 1) + D (k + 1) / E := by linarith
      _ = (E * δ (k + 1) + D (k + 1)) / E := hlhs
      _ ≤ ((1 - γ) * η k * (ϑ - 1) * δ k + D k) / E := by
          refine div_le_div_of_nonneg_right ?_ hE.le
          simp only [E]
          nlinarith
      _ = (1 - 1 / ϑ) * a k := hrhs.symm
  have hunroll (k : ℕ) : a k ≤ (1 - 1 / ϑ) ^ k * a 0 := by
    induction k with
    | zero => simp
    | succ k ih =>
      calc a (k + 1) ≤ (1 - 1 / ϑ) * a k := hrec k
        _ ≤ (1 - 1 / ϑ) * ((1 - 1 / ϑ) ^ k * a 0) := mul_le_mul_of_nonneg_left ih hr0
        _ = (1 - 1 / ϑ) ^ (k + 1) * a 0 := by ring
  have hδa : δ k ≤ a k := by
    have : 0 ≤ D k / ((1 - γ) * η k * (ϑ - 1)) := div_nonneg (hD k) (by
      have := hη k; positivity)
    simp only [a]
    linarith
  exact hδa.trans (hunroll k)

/-- **Xiao's Theorem 10 in his displayed form.** For a start distribution `ρ`, `γ > 0`, and
`ϑ` as in `pmd_linear_convergence`, the gap after `k` steps is at most
`(1 - 1 / ϑ) ^ k * (δ_0 + D⋆_0 / (η 0 * γ))`; `ϑ ≥ 1 / (1 - γ)` holds automatically. -/
theorem pmd_linear_convergence' (η : ℕ → ℝ) (θ₀ : S → A → ℝ) (hη : ∀ k, 0 < η k)
    (hγpos : 0 < γ) (πstar : StationaryPolicy S A) {ρ : S → ℝ} (hρ : ∀ s, 0 ≤ ρ s)
    (hρ1 : ∑ s, ρ s = 1) {ϑ : ℝ} (hϑ1 : 1 < ϑ)
    (hϑ : ∀ s, m.weightedVisitation πstar hγ0 hγ1 ρ s ≤ (1 - γ) * ϑ * ρ s)
    (hstep : ∀ k, ϑ * η k ≤ (ϑ - 1) * η (k + 1)) (k : ℕ) :
    ∑ s₀, ρ s₀ * (m.policyValue πstar hγ0 hγ1 s₀ -
        m.policyValue (softmaxPolicy (m.pmdScores hγ0 hγ1 η θ₀ k)) hγ0 hγ1 s₀) ≤
      (1 - 1 / ϑ) ^ k * (∑ s₀, ρ s₀ * (m.policyValue πstar hγ0 hγ1 s₀ -
          m.policyValue (softmaxPolicy θ₀) hγ0 hγ1 s₀) +
        (∑ s, m.weightedVisitation πstar hγ0 hγ1 ρ s * kl (πstar s) (softmaxPolicy θ₀ s)) /
          (η 0 * γ)) := by
  refine (m.pmd_linear_convergence hγ0 hγ1 η θ₀ hη πstar hρ hϑ1 hϑ hstep k).trans ?_
  have hγ : 0 < 1 - γ := sub_pos.mpr hγ1
  have hϑ0 : 0 < ϑ := zero_lt_one.trans hϑ1
  have hr0 : 0 ≤ (1 - 1 / ϑ) ^ k := pow_nonneg (by
    rw [sub_nonneg, div_le_one hϑ0]; exact hϑ1.le) k
  -- Summing `hϑ` over states gives `1 ≤ (1 - γ) ϑ`.
  have hsum : ∑ s, m.weightedVisitation πstar hγ0 hγ1 ρ s = 1 := by
    simp only [weightedVisitation]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, m.sum_discountedVisitation, mul_one, hρ1]
  have hϑγ : 1 ≤ (1 - γ) * ϑ := by
    have := Finset.sum_le_sum fun s (_ : s ∈ Finset.univ) => hϑ s
    rw [hsum, ← Finset.mul_sum, hρ1, mul_one] at this
    exact this
  have hD : 0 ≤ ∑ s, m.weightedVisitation πstar hγ0 hγ1 ρ s * kl (πstar s) (softmaxPolicy θ₀ s) :=
    Finset.sum_nonneg fun s _ => mul_nonneg
      (Finset.sum_nonneg fun s₀ _ => mul_nonneg (hρ s₀)
        (m.discountedVisitation_nonneg πstar hγ0 hγ1 s₀ s))
      (kl_nonneg_of_ne_zero _ _ (softmaxPolicy_ne_zero _ s))
  have h0 := hη 0
  refine mul_le_mul_of_nonneg_left (add_le_add le_rfl ?_) hr0
  refine div_le_div_of_nonneg_left hD (by positivity) ?_
  nlinarith

end MDP

end Rlib
