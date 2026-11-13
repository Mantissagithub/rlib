module

public import Rlib.MDP.SoftmaxPolicyGradient
public import Mathlib.Topology.Order.MonotoneConvergence

/-! # Asymptotic behavior of exact softmax policy gradient

This file starts the asymptotic argument of Agarwal, Kakade, Lee, and Mahajan, *On the Theory of
Policy Gradient Methods* (JMLR 2021), Theorem 10. Exact softmax policy gradient with any step
size `η ≥ 0` and start weights `μ ≥ 0` improves the value at every state, so the values, action
values, and advantages of the iterates converge.
-/

@[expose] public section

noncomputable section

namespace Rlib

variable {S A : Type*} [Fintype A] [Nonempty A]

/-- **A softmax step along `π * A` does not hurt.** If the advantages `A s` average to zero under
the softmax policy of `θ`, then after adding `κ * π a * A s a` to each score with `κ ≥ 0`, the
new policy's average of `A s` is nonnegative. -/
theorem sum_softmaxPolicy_mul_nonneg (θ Adv : S → A → ℝ) (s : S) {κ : ℝ} (hκ : 0 ≤ κ)
    (h0 : ∑ a, (softmaxPolicy θ s a).toReal * Adv s a = 0) :
    0 ≤ ∑ a, (softmaxPolicy (fun s a => θ s a + κ * ((softmaxPolicy θ s a).toReal * Adv s a))
      s a).toReal * Adv s a := by
  set p : A → ℝ := fun a => (softmaxPolicy θ s a).toReal with hp
  have hZ : 0 < ∑ b, Real.exp (θ s b) :=
    Finset.sum_pos (fun b _ => Real.exp_pos _) Finset.univ_nonempty
  have hZ' : 0 < ∑ b, Real.exp (θ s b + κ * (p b * Adv s b)) :=
    Finset.sum_pos (fun b _ => Real.exp_pos _) Finset.univ_nonempty
  have hexp (a : A) : Real.exp (θ s a) = p a * ∑ b, Real.exp (θ s b) := by
    have h := softmaxPolicy_apply θ s a
    change p a = Real.exp (θ s a) / ∑ b, Real.exp (θ s b) at h
    rw [h, div_mul_cancel₀ _ hZ.ne']
  have hterm (a : A) : (softmaxPolicy (fun s a => θ s a + κ * ((softmaxPolicy θ s a).toReal *
      Adv s a)) s a).toReal * Adv s a =
      (∑ b, Real.exp (θ s b)) / (∑ b, Real.exp (θ s b + κ * (p b * Adv s b))) *
        (p a * Adv s a * Real.exp (κ * (p a * Adv s a))) := by
    rw [softmaxPolicy_apply, Real.exp_add, hexp]
    ring
  have hy (a : A) : p a * Adv s a ≤ p a * Adv s a * Real.exp (κ * (p a * Adv s a)) := by
    rcases le_or_gt 0 (p a * Adv s a) with h | h
    · exact le_mul_of_one_le_right h (Real.one_le_exp (mul_nonneg hκ h))
    · have : Real.exp (κ * (p a * Adv s a)) ≤ 1 :=
        Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos hκ h.le)
      nlinarith
  rw [Finset.sum_congr rfl fun a _ => hterm a, ← Finset.mul_sum]
  refine mul_nonneg (div_nonneg hZ.le hZ'.le) ?_
  calc (0 : ℝ) = ∑ a, p a * Adv s a := h0.symm
    _ ≤ _ := Finset.sum_le_sum fun a _ => hy a

namespace MDP

variable [Fintype S] [DecidableEq S]

/-- One step of exact softmax policy gradient adds `κ s * π a * A s a` to the scores at `s`,
with `κ s = η * (1 - γ)⁻¹ * d s` for the `μ`-weighted visitation `d`. -/
theorem pgScores_succ (m : MDP S A) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (μ : S → ℝ) (η : ℝ)
    (θ₁ : S → A → ℝ) (t : ℕ) :
    m.pgScores hγ0 hγ1 μ η θ₁ (t + 1) = fun s a => m.pgScores hγ0 hγ1 μ η θ₁ t s a +
      η * (1 - γ)⁻¹ * m.weightedVisitation (softmaxPolicy (m.pgScores hγ0 hγ1 μ η θ₁ t))
        hγ0 hγ1 μ s *
        ((softmaxPolicy (m.pgScores hγ0 hγ1 μ η θ₁ t) s a).toReal *
          m.advantage (softmaxPolicy (m.pgScores hγ0 hγ1 μ η θ₁ t)) hγ0 hγ1 s a) := by
  funext s a
  simp only [pgScores, softmaxGradient]
  ring

/-- **Exact softmax policy gradient improves every state.** For any step size `η ≥ 0` and start
weights `μ ≥ 0`, each step raises the value at every state. -/
theorem policyValue_pg_le_succ (m : MDP S A) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    {μ : S → ℝ} (hμ : ∀ s, 0 ≤ μ s) {η : ℝ} (hη : 0 ≤ η) (θ₁ : S → A → ℝ) (t : ℕ) (s : S) :
    m.policyValue (softmaxPolicy (m.pgScores hγ0 hγ1 μ η θ₁ t)) hγ0 hγ1 s ≤
      m.policyValue (softmaxPolicy (m.pgScores hγ0 hγ1 μ η θ₁ (t + 1))) hγ0 hγ1 s := by
  set θ := m.pgScores hγ0 hγ1 μ η θ₁ t
  refine m.policyValue_le_of_expect_advantage_nonneg _ _ hγ0 hγ1 (fun s' => ?_) s
  have hκ : 0 ≤ η * (1 - γ)⁻¹ * m.weightedVisitation (softmaxPolicy θ) hγ0 hγ1 μ s' := by
    have hd : 0 ≤ m.weightedVisitation (softmaxPolicy θ) hγ0 hγ1 μ s' :=
      Finset.sum_nonneg fun s₀ _ =>
        mul_nonneg (hμ s₀) (m.discountedVisitation_nonneg _ hγ0 hγ1 s₀ s')
    have : 0 ≤ (1 - γ)⁻¹ := inv_nonneg.mpr (sub_nonneg.mpr hγ1.le)
    positivity
  have h := sum_softmaxPolicy_mul_nonneg (S := S) θ
    (m.advantage (softmaxPolicy θ) hγ0 hγ1) s' hκ (m.expect_advantage (softmaxPolicy θ) hγ0 hγ1 s')
  rw [pgScores_succ]
  exact h

/-- With any step size `η ≥ 0`, the values of the exact softmax policy gradient iterates never
decrease along the iteration. -/
theorem monotone_policyValue_pg (m : MDP S A) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    {μ : S → ℝ} (hμ : ∀ s, 0 ≤ μ s) {η : ℝ} (hη : 0 ≤ η) (θ₁ : S → A → ℝ) (s : S) :
    Monotone fun t => m.policyValue (softmaxPolicy (m.pgScores hγ0 hγ1 μ η θ₁ t)) hγ0 hγ1 s :=
  monotone_nat_of_le_succ fun t => m.policyValue_pg_le_succ hγ0 hγ1 hμ hη θ₁ t s

/-- The limit of the values of the exact softmax policy gradient iterates. -/
def pgLimitValue (m : MDP S A) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (μ : S → ℝ) (η : ℝ)
    (θ₁ : S → A → ℝ) (s : S) : ℝ :=
  ⨆ t, m.policyValue (softmaxPolicy (m.pgScores hγ0 hγ1 μ η θ₁ t)) hγ0 hγ1 s

/-- **The values converge.** With rewards in `[0, 1]`, any step size `η ≥ 0`, and start weights
`μ ≥ 0`, the values of the iterates converge at every state. -/
theorem tendsto_policyValue_pg (m : MDP S A) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hr : ∀ s a, m.reward s a ∈ Set.Icc (0 : ℝ) 1) {μ : S → ℝ} (hμ : ∀ s, 0 ≤ μ s) {η : ℝ}
    (hη : 0 ≤ η) (θ₁ : S → A → ℝ) (s : S) :
    Filter.Tendsto
      (fun t => m.policyValue (softmaxPolicy (m.pgScores hγ0 hγ1 μ η θ₁ t)) hγ0 hγ1 s)
      Filter.atTop (nhds (m.pgLimitValue hγ0 hγ1 μ η θ₁ s)) :=
  tendsto_atTop_ciSup (m.monotone_policyValue_pg hγ0 hγ1 hμ hη θ₁ s)
    ⟨1 / (1 - γ), by
      rintro _ ⟨t, rfl⟩
      exact (m.policyValue_mem_Icc _ hγ0 hγ1 hr s).2⟩

/-- **The action values and advantages converge.** Under the same conditions, the action value
of each pair converges to `r s a + γ * E [V∞]` and the advantage to that minus `V∞ s`, where
`V∞` is the limit of the values. -/
theorem tendsto_advantage_pg (m : MDP S A) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hr : ∀ s a, m.reward s a ∈ Set.Icc (0 : ℝ) 1) {μ : S → ℝ} (hμ : ∀ s, 0 ≤ μ s) {η : ℝ}
    (hη : 0 ≤ η) (θ₁ : S → A → ℝ) (s : S) (a : A) :
    Filter.Tendsto
      (fun t => m.advantage (softmaxPolicy (m.pgScores hγ0 hγ1 μ η θ₁ t)) hγ0 hγ1 s a)
      Filter.atTop (nhds (m.oneStepActionValue γ (m.pgLimitValue hγ0 hγ1 μ η θ₁) s a -
        m.pgLimitValue hγ0 hγ1 μ η θ₁ s)) := by
  have hV (s' : S) := m.tendsto_policyValue_pg hγ0 hγ1 hr hμ hη θ₁ s'
  simp only [advantage, policyActionValue, oneStepActionValue, expect]
  refine Filter.Tendsto.sub (Filter.Tendsto.const_add _ (Filter.Tendsto.const_mul _ ?_)) (hV s)
  exact tendsto_finsetSum _ fun s' _ => (hV s').const_mul _

/-- **The gradient vanishes.** With rewards in `[0, 1]`, a start distribution `μ`, and Mei et
al.'s step `η = (1 - γ) ^ 3 / 8`, the squared lengths of the gradients are summable, so every
gradient entry tends to zero. -/
theorem tendsto_softmaxGradient_pg (m : MDP S A) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hr : ∀ s a, m.reward s a ∈ Set.Icc (0 : ℝ) 1) {μ : S → ℝ} (hμ : ∀ s, 0 ≤ μ s)
    (hμ1 : ∑ s, μ s = 1) (θ₁ : S → A → ℝ) (s : S) (a : A) :
    Filter.Tendsto (fun t => m.softmaxGradient
        (softmaxPolicy (m.pgScores hγ0 hγ1 μ ((1 - γ) ^ 3 / 8) θ₁ t)) hγ0 hγ1 μ s a)
      Filter.atTop (nhds 0) := by
  have hγ : 0 < 1 - γ := sub_pos.mpr hγ1
  set θ := m.pgScores hγ0 hγ1 μ ((1 - γ) ^ 3 / 8) θ₁
  set G : ℕ → S → A → ℝ := fun t => m.softmaxGradient (softmaxPolicy (θ t)) hγ0 hγ1 μ
  set N : ℕ → ℝ := fun t => ∑ s, ∑ a, G t s a ^ 2
  set J : ℕ → ℝ := fun t => ∑ s₀, μ s₀ * m.policyValue (softmaxPolicy (θ t)) hγ0 hγ1 s₀
  have hN (t : ℕ) : 0 ≤ N t :=
    Finset.sum_nonneg fun s _ => Finset.sum_nonneg fun a _ => sq_nonneg _
  have hstep (t : ℕ) : (1 - γ) ^ 3 / 16 * N t ≤ J (t + 1) - J t := by
    have h := m.sum_policyValue_pg_succ_ge hγ0 hγ1 hr hμ hμ1 θ₁ t
    change J t + (1 - γ) ^ 3 / 16 * N t ≤ J (t + 1) at h
    linarith
  have hJ (t : ℕ) : J t ∈ Set.Icc 0 (1 / (1 - γ)) := by
    have hV (s₀ : S) := m.policyValue_mem_Icc (softmaxPolicy (θ t)) hγ0 hγ1 hr s₀
    constructor
    · exact Finset.sum_nonneg fun s₀ _ => mul_nonneg (hμ s₀) (hV s₀).1
    · calc J t ≤ ∑ s₀, μ s₀ * (1 / (1 - γ)) :=
            Finset.sum_le_sum fun s₀ _ => mul_le_mul_of_nonneg_left (hV s₀).2 (hμ s₀)
        _ = 1 / (1 - γ) := by rw [← Finset.sum_mul, hμ1, one_mul]
  have hsum : Summable fun t => (1 - γ) ^ 3 / 16 * N t := by
    refine summable_of_sum_range_le (c := 1 / (1 - γ))
      (fun t => mul_nonneg (by positivity) (hN t)) fun n => ?_
    calc ∑ t ∈ Finset.range n, (1 - γ) ^ 3 / 16 * N t
        ≤ ∑ t ∈ Finset.range n, (J (t + 1) - J t) := Finset.sum_le_sum fun t _ => hstep t
      _ = J n - J 0 := Finset.sum_range_sub J n
      _ ≤ 1 / (1 - γ) := by linarith [(hJ n).2, (hJ 0).1]
  have hNlim : Filter.Tendsto N Filter.atTop (nhds 0) := by
    have h := (hsum.tendsto_atTop_zero).const_mul (16 / (1 - γ) ^ 3)
    rw [mul_zero] at h
    refine h.congr fun t => ?_
    field_simp
  have hsq (t : ℕ) : G t s a ^ 2 ≤ N t := by
    calc G t s a ^ 2 ≤ ∑ a', G t s a' ^ 2 :=
          Finset.single_le_sum (f := fun a' => G t s a' ^ 2) (fun _ _ => sq_nonneg _)
            (Finset.mem_univ a)
      _ ≤ N t := Finset.single_le_sum (f := fun s' => ∑ a', G t s' a' ^ 2)
            (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ s)
  have hsqlim : Filter.Tendsto (fun t => G t s a ^ 2) Filter.atTop (nhds 0) :=
    squeeze_zero (fun t => sq_nonneg _) hsq hNlim
  have habs : Filter.Tendsto (fun t => |G t s a|) Filter.atTop (nhds 0) := by
    have h := hsqlim.sqrt
    rw [Real.sqrt_zero] at h
    exact h.congr fun t => Real.sqrt_sq_eq_abs _
  exact (tendsto_zero_iff_abs_tendsto_zero _).mpr habs

/-- **Advantages weighted by probabilities vanish.** Under the same conditions, if `μ s > 0`
then `π_t (a | s) * A_t (s, a)` tends to zero. -/
theorem tendsto_mul_advantage_pg (m : MDP S A) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hr : ∀ s a, m.reward s a ∈ Set.Icc (0 : ℝ) 1) {μ : S → ℝ} (hμ : ∀ s, 0 ≤ μ s)
    (hμ1 : ∑ s, μ s = 1) (θ₁ : S → A → ℝ) {s : S} (hs : 0 < μ s) (a : A) :
    Filter.Tendsto (fun t =>
        (softmaxPolicy (m.pgScores hγ0 hγ1 μ ((1 - γ) ^ 3 / 8) θ₁ t) s a).toReal *
          m.advantage (softmaxPolicy (m.pgScores hγ0 hγ1 μ ((1 - γ) ^ 3 / 8) θ₁ t)) hγ0 hγ1 s a)
      Filter.atTop (nhds 0) := by
  have hγ : 0 < 1 - γ := sub_pos.mpr hγ1
  set θ := m.pgScores hγ0 hγ1 μ ((1 - γ) ^ 3 / 8) θ₁
  have hG := m.tendsto_softmaxGradient_pg hγ0 hγ1 hr hμ hμ1 θ₁ s a
  have hbound (t : ℕ) : |(softmaxPolicy (θ t) s a).toReal *
      m.advantage (softmaxPolicy (θ t)) hγ0 hγ1 s a| ≤
      1 / μ s * |m.softmaxGradient (softmaxPolicy (θ t)) hγ0 hγ1 μ s a| := by
    set d := m.weightedVisitation (softmaxPolicy (θ t)) hγ0 hγ1 μ s
    have hd : (1 - γ) * μ s ≤ d := m.mul_le_weightedVisitation _ hγ0 hγ1 hμ s
    have hdpos : 0 < d := lt_of_lt_of_le (mul_pos hγ hs) hd
    have heq : m.softmaxGradient (softmaxPolicy (θ t)) hγ0 hγ1 μ s a =
        (1 - γ)⁻¹ * d * ((softmaxPolicy (θ t) s a).toReal *
          m.advantage (softmaxPolicy (θ t)) hγ0 hγ1 s a) := by
      simp only [softmaxGradient, d]; ring
    set y := (softmaxPolicy (θ t) s a).toReal * m.advantage (softmaxPolicy (θ t)) hγ0 hγ1 s a
    have habs : |(1 - γ)⁻¹ * d * y| = (1 - γ)⁻¹ * d * |y| := by
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (1 - γ)⁻¹ * d)]
    rw [heq, habs]
    have hk : 1 ≤ 1 / μ s * ((1 - γ)⁻¹ * d) := by
      rw [show 1 / μ s * ((1 - γ)⁻¹ * d) = d / ((1 - γ) * μ s) by field_simp,
        le_div_iff₀ (by positivity)]
      linarith
    calc |y| = 1 * |y| := (one_mul _).symm
      _ ≤ (1 / μ s * ((1 - γ)⁻¹ * d)) * |y| := mul_le_mul_of_nonneg_right hk (abs_nonneg _)
      _ = _ := by ring
  have hlim : Filter.Tendsto (fun t => 1 / μ s *
      |m.softmaxGradient (softmaxPolicy (θ t)) hγ0 hγ1 μ s a|) Filter.atTop (nhds 0) := by
    have h := ((tendsto_zero_iff_abs_tendsto_zero _).mp hG).const_mul (1 / μ s)
    rwa [mul_zero] at h
  exact (tendsto_zero_iff_abs_tendsto_zero _).mpr
    (squeeze_zero (fun t => abs_nonneg _) hbound hlim)

end MDP

end Rlib
