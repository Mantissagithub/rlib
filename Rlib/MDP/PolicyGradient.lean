module

public import Rlib.MDP.Visitation
public import Mathlib.Analysis.Calculus.Deriv.Slope

/-! # The policy gradient theorem

For a family of stationary policies whose action probabilities are differentiable in a real
parameter, the policy value is differentiable, and its derivative is `1 / (1 - γ)` times the
discounted visitation average of the derivative of the action probabilities weighted by the
advantages, or equivalently by the action values. The proof uses the performance difference
lemma, so it needs no matrix inverse.
-/

@[expose] public section

noncomputable section

open Filter Topology

namespace Rlib.MDP

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S]

/-- Discounted visitation is at most one. -/
theorem discountedVisitation_le_one (m : MDP S A) (π : StationaryPolicy S A) {γ : ℝ}
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (s₀ s : S) : m.discountedVisitation π hγ0 hγ1 s₀ s ≤ 1 := by
  rw [← m.sum_discountedVisitation π hγ0 hγ1 s₀]
  exact Finset.single_le_sum (fun t _ => m.discountedVisitation_nonneg π hγ0 hγ1 s₀ t)
    (Finset.mem_univ s)

omit [DecidableEq S] in
/-- The expected advantage of `π₀` under another policy is the advantage weighted by the change
in action probabilities. -/
theorem expect_advantage_eq_sum_sub (m : MDP S A) (π₀ π : StationaryPolicy S A) {γ : ℝ}
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (s : S) :
    expect (π s) (m.advantage π₀ hγ0 hγ1 s) =
      ∑ a, ((π s a).toReal - (π₀ s a).toReal) * m.advantage π₀ hγ0 hγ1 s a := by
  have h0 := m.expect_advantage π₀ hγ0 hγ1 s
  unfold expect at h0 ⊢
  simp only [sub_mul, Finset.sum_sub_distrib, h0, sub_zero]

/-- The gain of `π` over `π₀`, written with the change in action probabilities. -/
theorem policyValue_sub_eq_sum (m : MDP S A) (π₀ π : StationaryPolicy S A) {γ : ℝ}
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (s₀ : S) :
    (1 - γ) * (m.policyValue π hγ0 hγ1 s₀ - m.policyValue π₀ hγ0 hγ1 s₀) =
      ∑ s, m.discountedVisitation π hγ0 hγ1 s₀ s *
        ∑ a, ((π s a).toReal - (π₀ s a).toReal) * m.advantage π₀ hγ0 hγ1 s a := by
  rw [m.sub_policyValue_eq_sum_visitation π₀ π hγ0 hγ1 s₀]
  exact Finset.sum_congr rfl fun s _ => by rw [m.expect_advantage_eq_sum_sub π₀ π hγ0 hγ1 s]

/-- **Continuity of policy values.** If the action probabilities of a family of policies
converge to those of `π₀`, then their values converge to the value of `π₀`. -/
theorem tendsto_policyValue (m : MDP S A) {ι : Type*} {l : Filter ι}
    (π : ι → StationaryPolicy S A) (π₀ : StationaryPolicy S A) {γ : ℝ} (hγ0 : 0 ≤ γ)
    (hγ1 : γ < 1) (h : ∀ s a, Tendsto (fun i => (π i s a).toReal) l (𝓝 (π₀ s a).toReal))
    (s₀ : S) :
    Tendsto (fun i => m.policyValue (π i) hγ0 hγ1 s₀) l (𝓝 (m.policyValue π₀ hγ0 hγ1 s₀)) := by
  have hγ : 0 < 1 - γ := sub_pos.mpr hγ1
  set e : ι → S → ℝ := fun i s =>
    ∑ a, ((π i s a).toReal - (π₀ s a).toReal) * m.advantage π₀ hγ0 hγ1 s a
  have he (s : S) : Tendsto (fun i => e i s) l (𝓝 0) := by
    have := tendsto_finsetSum Finset.univ fun a _ =>
      ((h s a).sub_const (π₀ s a).toReal).mul_const (m.advantage π₀ hγ0 hγ1 s a)
    simpa [e] using this
  have hsum : Tendsto (fun i => ∑ s, m.discountedVisitation (π i) hγ0 hγ1 s₀ s * e i s) l
      (𝓝 0) := by
    have hbound : Tendsto (fun i => ∑ s, |e i s|) l (𝓝 0) := by
      simpa using tendsto_finsetSum Finset.univ fun s _ => (he s).abs
    refine squeeze_zero_norm (fun i => ?_) hbound
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun s _ => ?_)
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (m.discountedVisitation_nonneg _ hγ0 hγ1 s₀ s)]
    exact mul_le_of_le_one_left (abs_nonneg _) (m.discountedVisitation_le_one _ hγ0 hγ1 s₀ s)
  have hdiff : Tendsto (fun i => m.policyValue (π i) hγ0 hγ1 s₀ - m.policyValue π₀ hγ0 hγ1 s₀)
      l (𝓝 0) := by
    have := hsum.const_mul (1 - γ)⁻¹
    rw [mul_zero] at this
    refine this.congr fun i => ?_
    rw [← m.policyValue_sub_eq_sum π₀ (π i) hγ0 hγ1 s₀]
    field_simp
  simpa using hdiff.add_const (m.policyValue π₀ hγ0 hγ1 s₀)

/-- If the action probabilities of a family of policies converge to those of `π₀`, then their
discounted visitations converge to that of `π₀`. -/
theorem tendsto_discountedVisitation (m : MDP S A) {ι : Type*} {l : Filter ι}
    (π : ι → StationaryPolicy S A) (π₀ : StationaryPolicy S A) {γ : ℝ} (hγ0 : 0 ≤ γ)
    (hγ1 : γ < 1) (h : ∀ s a, Tendsto (fun i => (π i s a).toReal) l (𝓝 (π₀ s a).toReal))
    (s₀ s : S) :
    Tendsto (fun i => m.discountedVisitation (π i) hγ0 hγ1 s₀ s) l
      (𝓝 (m.discountedVisitation π₀ hγ0 hγ1 s₀ s)) :=
  ((m.withReward fun t _ => if t = s then 1 else 0).tendsto_policyValue π π₀ hγ0 hγ1 h
    s₀).const_mul (1 - γ)

/-- **Policy gradient theorem, advantage form.** If the action probabilities of a family of
policies `π t` have derivatives `π' s a` at `t₀`, then the value of `π t` has derivative
`(1 - γ)⁻¹ * ∑ s, d s * ∑ a, π' s a * A s a` at `t₀`, where `d` is the discounted visitation and
`A` the advantage of `π t₀`. -/
theorem hasDerivAt_policyValue (m : MDP S A) (π : ℝ → StationaryPolicy S A) {γ : ℝ}
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) {t₀ : ℝ} (π' : S → A → ℝ)
    (hπ : ∀ s a, HasDerivAt (fun t => (π t s a).toReal) (π' s a) t₀) (s₀ : S) :
    HasDerivAt (fun t => m.policyValue (π t) hγ0 hγ1 s₀)
      ((1 - γ)⁻¹ * ∑ s, m.discountedVisitation (π t₀) hγ0 hγ1 s₀ s *
        ∑ a, π' s a * m.advantage (π t₀) hγ0 hγ1 s a) t₀ := by
  have hγ : 0 < 1 - γ := sub_pos.mpr hγ1
  rw [hasDerivAt_iff_tendsto_slope]
  have hcont (s : S) (a : A) :
      Tendsto (fun t => (π t s a).toReal) (𝓝[≠] t₀) (𝓝 (π t₀ s a).toReal) :=
    tendsto_nhdsWithin_of_tendsto_nhds (hπ s a).continuousAt.tendsto
  have hslope (s : S) (a : A) :
      Tendsto (fun t => (t - t₀)⁻¹ * ((π t s a).toReal - (π t₀ s a).toReal)) (𝓝[≠] t₀)
        (𝓝 (π' s a)) := by
    have := hasDerivAt_iff_tendsto_slope.1 (hπ s a)
    refine this.congr fun t => ?_
    rw [slope_def_field]
    ring
  have hlim := ((tendsto_finsetSum Finset.univ fun s _ =>
    (m.tendsto_discountedVisitation (fun t => π t) (π t₀) hγ0 hγ1 hcont s₀ s).mul
      (tendsto_finsetSum Finset.univ fun a _ =>
        (hslope s a).mul_const (m.advantage (π t₀) hγ0 hγ1 s a))).const_mul (1 - γ)⁻¹)
  refine hlim.congr fun t => ?_
  have hV : m.policyValue (π t) hγ0 hγ1 s₀ - m.policyValue (π t₀) hγ0 hγ1 s₀ =
      (1 - γ)⁻¹ * ∑ s, m.discountedVisitation (π t) hγ0 hγ1 s₀ s *
        ∑ a, ((π t s a).toReal - (π t₀ s a).toReal) * m.advantage (π t₀) hγ0 hγ1 s a := by
    rw [← m.policyValue_sub_eq_sum (π t₀) (π t) hγ0 hγ1 s₀]
    field_simp
  have hin (s : S) : ∑ a, (t - t₀)⁻¹ * ((π t s a).toReal - (π t₀ s a).toReal) *
      m.advantage (π t₀) hγ0 hγ1 s a = (t - t₀)⁻¹ *
        ∑ a, ((π t s a).toReal - (π t₀ s a).toReal) * m.advantage (π t₀) hγ0 hγ1 s a := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => by ring
  simp only [hin]
  rw [show (∑ s, m.discountedVisitation (π t) hγ0 hγ1 s₀ s * ((t - t₀)⁻¹ *
      ∑ a, ((π t s a).toReal - (π t₀ s a).toReal) * m.advantage (π t₀) hγ0 hγ1 s a)) =
      (t - t₀)⁻¹ * ∑ s, m.discountedVisitation (π t) hγ0 hγ1 s₀ s *
        ∑ a, ((π t s a).toReal - (π t₀ s a).toReal) * m.advantage (π t₀) hγ0 hγ1 s a by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun s _ => by ring]
  rw [slope_def_field, hV]
  ring

omit [Fintype S] [DecidableEq S] in
/-- The derivatives of a family of action distributions sum to zero over actions. -/
theorem sum_deriv_eq_zero (π : ℝ → StationaryPolicy S A) {t₀ : ℝ} (π' : S → A → ℝ)
    (hπ : ∀ s a, HasDerivAt (fun t => (π t s a).toReal) (π' s a) t₀) (s : S) :
    ∑ a, π' s a = 0 := by
  have hsum := HasDerivAt.fun_sum (u := Finset.univ) (A := fun a t => (π t s a).toReal)
    (A' := π' s) fun a _ => hπ s a
  have hconst : (fun t => ∑ a, (π t s a).toReal) = fun _ => (1 : ℝ) :=
    funext fun t => probability_sum (π t s)
  rw [hconst] at hsum
  exact hsum.unique (hasDerivAt_const t₀ 1)

/-- **Policy gradient theorem.** If the action probabilities of a family of policies `π t` have
derivatives `π' s a` at `t₀`, then the value of `π t` has derivative
`(1 - γ)⁻¹ * ∑ s, d s * ∑ a, π' s a * Q s a` at `t₀`, where `d` is the discounted visitation and
`Q` the action value of `π t₀`. -/
theorem hasDerivAt_policyValue_actionValue (m : MDP S A) (π : ℝ → StationaryPolicy S A)
    {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) {t₀ : ℝ} (π' : S → A → ℝ)
    (hπ : ∀ s a, HasDerivAt (fun t => (π t s a).toReal) (π' s a) t₀) (s₀ : S) :
    HasDerivAt (fun t => m.policyValue (π t) hγ0 hγ1 s₀)
      ((1 - γ)⁻¹ * ∑ s, m.discountedVisitation (π t₀) hγ0 hγ1 s₀ s *
        ∑ a, π' s a * m.policyActionValue (π t₀) hγ0 hγ1 s a) t₀ := by
  have heq : (∑ s, m.discountedVisitation (π t₀) hγ0 hγ1 s₀ s *
      ∑ a, π' s a * m.advantage (π t₀) hγ0 hγ1 s a) =
      ∑ s, m.discountedVisitation (π t₀) hγ0 hγ1 s₀ s *
        ∑ a, π' s a * m.policyActionValue (π t₀) hγ0 hγ1 s a :=
    Finset.sum_congr rfl fun s _ => by
      congr 1
      simp only [advantage, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul,
        sum_deriv_eq_zero π π' hπ s, zero_mul, sub_zero]
  rw [← heq]
  exact m.hasDerivAt_policyValue π hγ0 hγ1 π' hπ s₀

end Rlib.MDP
