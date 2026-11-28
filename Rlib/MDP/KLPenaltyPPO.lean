module

public import Rlib.MDP.NaturalPolicyGradient
public import Rlib.MDP.GRPO

/-! # PPO with a KL penalty

The KL-penalized variant of PPO (Schulman, Wolski, Dhariwal, Radford, and Klimov 2017,
Section 4) maximizes the surrogate objective minus `c` times a KL divergence between the new and
the old action distributions. With exact advantages, the maximization separates over states. This
file follows Liu, Cai, Yang, and Wang, *Neural Proximal/Trust Region Policy Optimization Attains
Globally Optimal Policy* (NeurIPS 2019), Section 3, who penalize `KL (π' s ‖ π s)` and solve each
step in closed form: `π' s a ∝ π s a * exp (A s a / c)`.

`expect_sub_mul_kl_eq` is the Gibbs variational identity behind that closed form, and
`eq_softmaxPolicy_iff_isKLPenaltyStep` shows that the maximizer is unique. For softmax policies
the step adds `A / c` to the scores, which is the natural policy gradient step with
`c = (1 - γ) / η`. So exact KL-penalized PPO started from the uniform policy converges at the
rate of Agarwal, Kakade, Lee, and Mahajan's Theorem 16 (`klPenaltyPPO_rate`).

The PPO paper writes the penalty as `KL (π s ‖ π' s)`, with the old policy first. That direction
has no closed-form maximizer and no known convergence proof; the formal statements use the
direction of Liu et al., which is also the one of mirror descent and TRPO analyses.
-/

@[expose] public section

noncomputable section

namespace Rlib

section Gibbs

variable {X : Type*} [Fintype X]

/-- `x - y ≤ x * log (x / y)` for `x ≥ 0` and `y > 0`. -/
theorem sub_le_mul_log_div {x y : ℝ} (hx : 0 ≤ x) (hy : 0 < y) :
    x - y ≤ x * Real.log (x / y) := by
  rcases hx.eq_or_lt with rfl | hx
  · simp [hy.le]
  · have h := Real.one_sub_inv_le_log_of_pos (div_pos hx hy)
    rw [inv_div] at h
    have : x * (1 - y / x) = x - y := by field_simp
    nlinarith

/-- Equality in `sub_le_mul_log_div` forces `x = y`. -/
theorem eq_of_mul_log_div_eq_sub {x y : ℝ} (hx : 0 ≤ x) (hy : 0 < y)
    (h : x * Real.log (x / y) = x - y) : x = y := by
  rcases hx.eq_or_lt with rfl | hx
  · simp at h; linarith
  · by_contra hne
    have hz : y / x ≠ 1 := fun h1 => hne ((div_eq_one_iff_eq hx.ne').mp h1).symm
    have hlt := Real.log_lt_sub_one_of_pos (div_pos hy hx) hz
    rw [Real.log_div hy.ne' hx.ne', ← neg_sub, ← Real.log_div hx.ne' hy.ne'] at hlt
    have : x * (y / x - 1) = y - x := by field_simp
    nlinarith

/-- **Gibbs' inequality.** The KL divergence from a distribution with full support is
nonnegative. -/
theorem kl_nonneg_of_ne_zero (p r : PMF X) (hr : ∀ x, r x ≠ 0) : 0 ≤ kl p r := by
  have hsub : ∑ x, ((p x).toReal - (r x).toReal) = 0 := by
    rw [Finset.sum_sub_distrib, probability_sum, probability_sum, sub_self]
  rw [kl, ← hsub]
  exact Finset.sum_le_sum fun x _ => sub_le_mul_log_div ENNReal.toReal_nonneg
    (ENNReal.toReal_pos (hr x) (r.apply_ne_top x))

/-- The KL divergence from a distribution with full support vanishes only at that
distribution. -/
theorem eq_of_kl_eq_zero (p r : PMF X) (hr : ∀ x, r x ≠ 0) (h : kl p r = 0) : p = r := by
  set f : X → ℝ := fun x =>
    (p x).toReal * Real.log ((p x).toReal / (r x).toReal) - ((p x).toReal - (r x).toReal)
  have hf (x : X) : 0 ≤ f x := sub_nonneg.mpr (sub_le_mul_log_div ENNReal.toReal_nonneg
    (ENNReal.toReal_pos (hr x) (r.apply_ne_top x)))
  have hsum : ∑ x, f x = 0 := by
    simp only [f, Finset.sum_sub_distrib, probability_sum, sub_self, sub_zero]
    exact h
  ext x
  have hx := (Finset.sum_eq_zero_iff_of_nonneg fun x _ => hf x).mp hsum x (Finset.mem_univ x)
  have := eq_of_mul_log_div_eq_sub ENNReal.toReal_nonneg
    (ENNReal.toReal_pos (hr x) (r.apply_ne_top x)) (sub_eq_zero.mp hx)
  exact (ENNReal.toReal_eq_toReal_iff' (p.apply_ne_top x) (r.apply_ne_top x)).mp this

/-- A distribution has zero KL divergence from itself. -/
theorem kl_self (p : PMF X) : kl p p = 0 := by
  refine Finset.sum_eq_zero fun x _ => ?_
  by_cases hp : (p x).toReal = 0
  · simp [hp]
  · simp [div_self hp]

/-- **Gibbs variational identity.** If `r` tilts a full-support distribution `q` by
`exp (g / c)`, normalized by `Z`, then the KL-penalized expectation of `g` under any `p` equals
`c * log Z - c * kl p r`. -/
theorem expect_sub_mul_kl_eq (p q r : PMF X) (g : X → ℝ) {c Z : ℝ} (hc : c ≠ 0) (hZ : 0 < Z)
    (hq : ∀ x, q x ≠ 0) (hr : ∀ x, (r x).toReal = (q x).toReal * Real.exp (g x / c) / Z) :
    expect p g - c * kl p q = c * Real.log Z - c * kl p r := by
  have hterm (x : X) : (p x).toReal * Real.log ((p x).toReal / (r x).toReal) =
      (p x).toReal * Real.log ((p x).toReal / (q x).toReal) - (p x).toReal * g x / c +
        (p x).toReal * Real.log Z := by
    by_cases hp : (p x).toReal = 0
    · simp [hp]
    have hp' : 0 < (p x).toReal := lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hp)
    have hq' : 0 < (q x).toReal := ENNReal.toReal_pos (hq x) (q.apply_ne_top x)
    rw [hr x, Real.log_div hp'.ne' (by positivity), Real.log_div (by positivity) hZ.ne',
      Real.log_mul hq'.ne' (Real.exp_pos _).ne', Real.log_exp, Real.log_div hp'.ne' hq'.ne']
    field_simp
    ring
  have hkl : kl p r = kl p q - expect p g / c + Real.log Z := by
    simp only [kl, hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib, expect,
      ← Finset.sum_mul, probability_sum, one_mul, Finset.sum_div]
  rw [hkl]
  field_simp
  ring

end Gibbs

namespace MDP

variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty A] [DecidableEq S]
variable (m : MDP S A) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)

/-- The KL-penalized PPO objective at state `s`: the expected advantage of `π` under the
candidate action distribution `p`, minus `c` times the KL divergence of `p` from `π s`. -/
def klPenaltyObjective (π : StationaryPolicy S A) (c : ℝ) (s : S) (p : PMF A) : ℝ :=
  expect p (m.advantage π hγ0 hγ1 s) - c * kl p (π s)

/-- `π'` is an exact KL-penalized PPO step from `π` with penalty `c`: at every state it
maximizes the KL-penalized objective. -/
def IsKLPenaltyStep (c : ℝ) (π π' : StationaryPolicy S A) : Prop :=
  ∀ s p, m.klPenaltyObjective hγ0 hγ1 π c s p ≤ m.klPenaltyObjective hγ0 hγ1 π c s (π' s)

omit [Fintype S] [DecidableEq S] in
/-- Softmax policies give every action positive probability. -/
theorem softmaxPolicy_ne_zero (θ : S → A → ℝ) (s : S) (a : A) : softmaxPolicy θ s a ≠ 0 := by
  intro h
  have := softmaxPolicy_apply θ s a
  rw [h, ENNReal.toReal_zero] at this
  exact (div_pos (Real.exp_pos _) (Finset.sum_pos (fun b _ => Real.exp_pos _)
    Finset.univ_nonempty)).ne' this.symm

omit [Fintype S] [DecidableEq S] in
/-- Adding `g / c` to softmax scores tilts the softmax policy by `exp (g / c)`. -/
theorem softmaxPolicy_add_div (θ g : S → A → ℝ) (c : ℝ) (s : S) (a : A) :
    (softmaxPolicy (fun s a => θ s a + g s a / c) s a).toReal =
      (softmaxPolicy θ s a).toReal * Real.exp (g s a / c) /
        ∑ b, (softmaxPolicy θ s b).toReal * Real.exp (g s b / c) := by
  have hZ : 0 < ∑ b, Real.exp (θ s b) :=
    Finset.sum_pos (fun b _ => Real.exp_pos _) Finset.univ_nonempty
  simp only [softmaxPolicy_apply, Real.exp_add, div_mul_eq_mul_div, ← Finset.sum_div]
  rw [div_div_div_cancel_right₀ hZ.ne']

omit [Fintype S] [DecidableEq S] in
/-- The tilting normalizer of a softmax policy is positive. -/
theorem sum_softmaxPolicy_mul_exp_pos (θ g : S → A → ℝ) (c : ℝ) (s : S) :
    0 < ∑ b, (softmaxPolicy θ s b).toReal * Real.exp (g s b / c) :=
  Finset.sum_pos (fun b _ => mul_pos (ENNReal.toReal_pos (softmaxPolicy_ne_zero θ s b)
    ((softmaxPolicy θ s).apply_ne_top b)) (Real.exp_pos _)) Finset.univ_nonempty

omit [DecidableEq S] in
/-- **The KL-penalized PPO step for softmax policies.** With penalty `c > 0`, the step from
`softmaxPolicy θ` adds `A / c` to the scores, and it is the only step: a policy is an exact
KL-penalized PPO step exactly when it equals this softmax policy. -/
theorem eq_softmaxPolicy_iff_isKLPenaltyStep (θ : S → A → ℝ) {c : ℝ} (hc : 0 < c)
    (π' : StationaryPolicy S A) :
    m.IsKLPenaltyStep hγ0 hγ1 c (softmaxPolicy θ) π' ↔
      π' = softmaxPolicy (fun s a => θ s a + m.advantage (softmaxPolicy θ) hγ0 hγ1 s a / c) := by
  set g := m.advantage (softmaxPolicy θ) hγ0 hγ1
  set r := softmaxPolicy (fun s a => θ s a + g s a / c)
  set Z := fun s => ∑ b, (softmaxPolicy θ s b).toReal * Real.exp (g s b / c)
  have hid (s : S) (p : PMF A) : m.klPenaltyObjective hγ0 hγ1 (softmaxPolicy θ) c s p =
      c * Real.log (Z s) - c * kl p (r s) :=
    expect_sub_mul_kl_eq p (softmaxPolicy θ s) (r s) (g s) hc.ne'
      (sum_softmaxPolicy_mul_exp_pos θ g c s) (softmaxPolicy_ne_zero θ s)
      (softmaxPolicy_add_div θ g c s)
  have hr (s : S) (a : A) : r s a ≠ 0 := softmaxPolicy_ne_zero _ s a
  constructor
  · intro h
    funext s
    have h1 := h s (r s)
    rw [hid, hid, kl_self] at h1
    have h2 := kl_nonneg_of_ne_zero (π' s) (r s) (hr s)
    exact eq_of_kl_eq_zero (π' s) (r s) (hr s) (le_antisymm (by nlinarith) h2)
  · rintro rfl s p
    rw [hid, hid, kl_self]
    nlinarith [kl_nonneg_of_ne_zero p (r s) (hr s)]

/-- **The exact KL-penalized PPO step maximizes the PPO objective.** With the old policy a
softmax policy, the surrogate objective minus `c` times the visitation average of
`KL (π' s ‖ π s)` is largest at the KL-penalized PPO step, among all stationary policies. -/
theorem surrogate_sub_kl_le (θ : S → A → ℝ) {c : ℝ} (hc : 0 < c) (π'' : StationaryPolicy S A)
    (s₀ : S) :
    let π := softmaxPolicy θ
    let π' := softmaxPolicy (fun s a => θ s a + m.advantage π hγ0 hγ1 s a / c)
    m.surrogate π π'' hγ0 hγ1 s₀ -
        c * ∑ s, m.discountedVisitation π hγ0 hγ1 s₀ s * kl (π'' s) (π s) ≤
      m.surrogate π π' hγ0 hγ1 s₀ -
        c * ∑ s, m.discountedVisitation π hγ0 hγ1 s₀ s * kl (π' s) (π s) := by
  intro π π'
  have hstep := (m.eq_softmaxPolicy_iff_isKLPenaltyStep hγ0 hγ1 θ hc π').mpr rfl
  have hsupp (σ : StationaryPolicy S A) : ∀ s a, σ s a ≠ 0 → π s a ≠ 0 :=
    fun s a _ => softmaxPolicy_ne_zero θ s a
  rw [m.surrogate_eq π π'' hγ0 hγ1 (hsupp π'') s₀, m.surrogate_eq π π' hγ0 hγ1 (hsupp π') s₀,
    Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun s _ => ?_
  have h := hstep s (π'' s)
  have hd := m.discountedVisitation_nonneg π hγ0 hγ1 s₀ s
  simp only [klPenaltyObjective] at h
  nlinarith

variable (θ₀ : S → A → ℝ)

omit [DecidableEq S] in
/-- **Exact KL-penalized PPO is natural policy gradient.** Any sequence of policies that starts
at `softmaxPolicy θ₀` and takes exact KL-penalized PPO steps with penalty `(1 - γ) / η` is the
natural policy gradient sequence with step size `η`. -/
theorem klPenaltyPPO_eq_npg {η : ℝ} (hη : 0 < η) (π : ℕ → StationaryPolicy S A)
    (h0 : π 0 = softmaxPolicy θ₀)
    (hstep : ∀ t, m.IsKLPenaltyStep hγ0 hγ1 ((1 - γ) / η) (π t) (π (t + 1))) (t : ℕ) :
    π t = softmaxPolicy (m.npgScores hγ0 hγ1 η θ₀ t) := by
  induction t with
  | zero => exact h0
  | succ t ih =>
    have hc : 0 < (1 - γ) / η := div_pos (sub_pos.mpr hγ1) hη
    have h := hstep t
    rw [ih, m.eq_softmaxPolicy_iff_isKLPenaltyStep hγ0 hγ1 _ hc] at h
    rw [h]
    congr 1
    funext s a
    simp only [npgScores]
    rw [div_div_eq_mul_div]
    ring

/-- **Exact KL-penalized PPO converges at rate `1 / T`.** With rewards in `[0, 1]`, start at the
uniform policy and take exact KL-penalized PPO steps with penalty `(1 - γ) / η`, `η > 0`. For any
start distribution `ρ` and any policy `π'`, after `T > 0` steps
`V^{π'} ρ - V⁽ᵀ⁾ ρ ≤ log |A| / (η * T) + 1 / ((1 - γ) ^ 2 * T)`. -/
theorem klPenaltyPPO_rate (hr : ∀ s a, m.reward s a ∈ Set.Icc (0 : ℝ) 1) {η : ℝ} (hη : 0 < η)
    (π : ℕ → StationaryPolicy S A) (h0 : π 0 = softmaxPolicy fun _ _ => 0)
    (hstep : ∀ t, m.IsKLPenaltyStep hγ0 hγ1 ((1 - γ) / η) (π t) (π (t + 1)))
    (π' : StationaryPolicy S A) {ρ : S → ℝ} (hρ : ∀ s, 0 ≤ ρ s) (hρ1 : ∑ s, ρ s = 1) {T : ℕ}
    (hT : 0 < T) :
    ∑ s₀, ρ s₀ * (m.policyValue π' hγ0 hγ1 s₀ - m.policyValue (π T) hγ0 hγ1 s₀) ≤
      Real.log (Fintype.card A) / (η * T) + 1 / ((1 - γ) ^ 2 * T) := by
  rw [m.klPenaltyPPO_eq_npg hγ0 hγ1 _ hη π h0 hstep T]
  exact m.sum_sub_policyValue_npg_le hγ0 hγ1 hr hη π' hρ hρ1 hT

end MDP

end Rlib
