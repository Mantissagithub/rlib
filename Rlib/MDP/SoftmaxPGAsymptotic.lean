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

/-- **Scores with a persistently negative push go to `-∞` (abstract form of Agarwal et al.,
Lemma C.11).** Suppose scores `θ t` move by `g t`, the moves sum to zero over actions, each move
is at most `K` times the softmax probability of its action, and from time `T` on the move of
`a₀` is at most `-κ` times its probability, with `κ > 0`. Then the score of `a₀` tends to `-∞`.
The proof bounds the total of `1 / Z t` by the finite descent of `θ a₀`, which bounds every
score from below, hence from above, and so bounds `Z t`. -/
theorem tendsto_atBot_of_softmax_step [DecidableEq A] {θ g : ℕ → A → ℝ}
    (hθ : ∀ t a, θ (t + 1) a = θ t a + g t a) (hsum : ∀ t, ∑ a, g t a = 0) {K : ℝ}
    (hK : ∀ t a, |g t a| ≤ K * (Real.exp (θ t a) / ∑ b, Real.exp (θ t b)))
    {a₀ : A} {κ : ℝ} (hκ : 0 < κ) {T : ℕ}
    (hdec : ∀ t, T ≤ t → g t a₀ ≤ -κ * (Real.exp (θ t a₀) / ∑ b, Real.exp (θ t b))) :
    Filter.Tendsto (fun t => θ t a₀) Filter.atTop Filter.atBot := by
  set Z : ℕ → ℝ := fun t => ∑ b, Real.exp (θ t b) with hZdef
  have hZ (t : ℕ) : 0 < Z t := Finset.sum_pos (fun b _ => Real.exp_pos _) Finset.univ_nonempty
  have hp (t : ℕ) (a : A) : 0 < Real.exp (θ t a) / Z t := div_pos (Real.exp_pos _) (hZ t)
  have hp1 (t : ℕ) (a : A) : Real.exp (θ t a) / Z t ≤ 1 := by
    rw [div_le_one (hZ t)]
    exact Finset.single_le_sum (f := fun b => Real.exp (θ t b)) (fun b _ => (Real.exp_pos _).le)
      (Finset.mem_univ a)
  have hK0 : 0 ≤ K := nonneg_of_mul_nonneg_left ((abs_nonneg _).trans (hK 0 a₀)) (hp 0 a₀)
  have hmono (n k : ℕ) : θ (T + n + k) a₀ ≤ θ (T + n) a₀ := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [← add_assoc, hθ]
      have := hdec (T + n + k) (by omega)
      nlinarith [hp (T + n + k) a₀]
  rw [Filter.tendsto_atBot]
  intro b
  by_contra hne
  rw [Filter.not_eventually] at hne
  have hb (n : ℕ) : b < θ (T + n) a₀ := by
    obtain ⟨t, hbt, ht⟩ := (hne.and_eventually (Filter.eventually_ge_atTop (T + n))).exists
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le ht
    exact lt_of_lt_of_le (not_le.mp hbt) (hmono n k)
  -- The descent of `a₀` bounds the sum of `1 / Z`.
  have hdesc (n : ℕ) : ∑ i ∈ Finset.range n, κ * (Real.exp b / Z (T + i)) ≤ θ T a₀ - b := by
    calc ∑ i ∈ Finset.range n, κ * (Real.exp b / Z (T + i))
        ≤ ∑ i ∈ Finset.range n, (θ (T + i) a₀ - θ (T + (i + 1)) a₀) := by
          refine Finset.sum_le_sum fun i _ => ?_
          have h1 : Real.exp b / Z (T + i) ≤ Real.exp (θ (T + i) a₀) / Z (T + i) :=
            div_le_div_of_nonneg_right (Real.exp_le_exp.mpr (hb i).le) (hZ _).le
          have h2 := hdec (T + i) (by omega)
          have h3 : θ (T + (i + 1)) a₀ = θ (T + i) a₀ + g (T + i) a₀ := hθ (T + i) a₀
          nlinarith
      _ = θ T a₀ - θ (T + n) a₀ := Finset.sum_range_sub' (fun i => θ (T + i) a₀) n
      _ ≤ θ T a₀ - b := by linarith [hb n]
  set C2 := K / κ * (θ T a₀ - b)
  set S : ℕ → ℝ := fun n => ∑ i ∈ Finset.range n, K * (Real.exp b / Z (T + i))
  have hS0 (n : ℕ) : 0 ≤ S n := Finset.sum_nonneg fun i _ =>
    mul_nonneg hK0 (div_nonneg (Real.exp_pos _).le (hZ _).le)
  have hS (n : ℕ) : S n ≤ C2 := by
    have h := mul_le_mul_of_nonneg_left (hdesc n) (div_nonneg hK0 hκ.le)
    refine le_trans (le_of_eq ?_) h
    simp only [S, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by field_simp
  -- Every score stays above a fixed level.
  have hlow (a : A) (n : ℕ) : min (θ T a) (b - K) - S n ≤ θ (T + n) a := by
    induction n with
    | zero => simp [S]
    | succ n ih =>
      have hstep : θ (T + (n + 1)) a = θ (T + n) a + g (T + n) a := hθ (T + n) a
      have hSs : S (n + 1) = S n + K * (Real.exp b / Z (T + n)) := Finset.sum_range_succ _ _
      have hg := neg_abs_le (g (T + n) a)
      have hgK := hK (T + n) a
      rw [hstep, hSs]
      by_cases h : b ≤ θ (T + n) a
      · have : K * (Real.exp (θ (T + n) a) / Z (T + n)) ≤ K :=
          mul_le_of_le_one_right hK0 (hp1 _ _)
        have := min_le_right (θ T a) (b - K)
        have := hS0 n
        have : 0 ≤ K * (Real.exp b / Z (T + n)) :=
          mul_nonneg hK0 (div_nonneg (Real.exp_pos _).le (hZ _).le)
        linarith
      · have : K * (Real.exp (θ (T + n) a) / Z (T + n)) ≤ K * (Real.exp b / Z (T + n)) :=
          mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right
            (Real.exp_le_exp.mpr (not_le.mp h).le) (hZ _).le) hK0
        linarith
  -- The scores keep their total, so they are bounded above, and so is `Z`.
  have hconst (t : ℕ) : ∑ a, θ t a = ∑ a, θ 0 a := by
    induction t with
    | zero => rfl
    | succ t ih => simp only [hθ, Finset.sum_add_distrib, hsum, add_zero, ih]
  set m : A → ℝ := fun a => min (θ T a) (b - K) - C2
  have hlow' (a : A) (n : ℕ) : m a ≤ θ (T + n) a := (sub_le_sub_left (hS n) _).trans (hlow a n)
  set U : A → ℝ := fun a => ∑ a', θ 0 a' - ∑ a' ∈ Finset.univ.erase a, m a'
  have hup (a : A) (n : ℕ) : θ (T + n) a ≤ U a := by
    have h := Finset.add_sum_erase Finset.univ (fun a' => θ (T + n) a') (Finset.mem_univ a)
    rw [hconst] at h
    have := Finset.sum_le_sum fun a' (_ : a' ∈ Finset.univ.erase a) => hlow' a' n
    simp only [U]
    linarith
  set Zm := ∑ a, Real.exp (U a)
  have hZm : 0 < Zm := Finset.sum_pos (fun a _ => Real.exp_pos _) Finset.univ_nonempty
  have hZle (n : ℕ) : Z (T + n) ≤ Zm :=
    Finset.sum_le_sum fun a _ => Real.exp_le_exp.mpr (hup a n)
  obtain ⟨n, hn⟩ := exists_nat_gt ((θ T a₀ - b) / (κ * (Real.exp b / Zm)))
  have hpos : 0 < κ * (Real.exp b / Zm) := mul_pos hκ (div_pos (Real.exp_pos _) hZm)
  have hlowsum : n * (κ * (Real.exp b / Zm)) ≤
      ∑ i ∈ Finset.range n, κ * (Real.exp b / Z (T + i)) := by
    have hc : ∑ _i ∈ Finset.range n, κ * (Real.exp b / Zm) = n * (κ * (Real.exp b / Zm)) := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [← hc]
    exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_left (Real.exp_pos _).le (hZ _) (hZle i)) hκ.le
  rw [div_lt_iff₀ hpos] at hn
  linarith [hdesc n]

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

/-- **Improvement for any small step (Agarwal et al.).** With rewards in `[0, 1]`, a start
distribution `μ`, and a step `0 ≤ η ≤ (1 - γ) ^ 3 / 8`, each step of exact softmax policy
gradient raises `V (μ)` by at least `η / 2` times the squared length of the gradient. -/
theorem sum_policyValue_pg_succ_ge_of_le (m : MDP S A) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hr : ∀ s a, m.reward s a ∈ Set.Icc (0 : ℝ) 1) {μ : S → ℝ} (hμ : ∀ s, 0 ≤ μ s)
    (hμ1 : ∑ s, μ s = 1) {η : ℝ} (hη0 : 0 ≤ η) (hη : η ≤ (1 - γ) ^ 3 / 8)
    (θ₁ : S → A → ℝ) (t : ℕ) :
    ∑ s₀, μ s₀ * m.policyValue (softmaxPolicy (m.pgScores hγ0 hγ1 μ η θ₁ t)) hγ0 hγ1 s₀ +
        η / 2 * ∑ s, ∑ a, m.softmaxGradient
          (softmaxPolicy (m.pgScores hγ0 hγ1 μ η θ₁ t)) hγ0 hγ1 μ s a ^ 2 ≤
      ∑ s₀, μ s₀ * m.policyValue
        (softmaxPolicy (m.pgScores hγ0 hγ1 μ η θ₁ (t + 1))) hγ0 hγ1 s₀ := by
  have hγ : 0 < 1 - γ := sub_pos.mpr hγ1
  set θ := m.pgScores hγ0 hγ1 μ η θ₁ t
  set G := m.softmaxGradient (softmaxPolicy θ) hγ0 hγ1 μ
  set N := ∑ s, ∑ a, G s a ^ 2
  have hN : 0 ≤ N := Finset.sum_nonneg fun s _ => Finset.sum_nonneg fun a _ => sq_nonneg _
  have h := m.sum_policyValue_softmax_ge hγ0 hγ1 hr hμ hμ1 θ
    (m.pgScores hγ0 hγ1 μ η θ₁ (t + 1))
  have hdiff (s : S) (a : A) : m.pgScores hγ0 hγ1 μ η θ₁ (t + 1) s a - θ s a = η * G s a := by
    simp only [pgScores, θ, G]; ring
  simp only [hdiff] at h
  have h1 : ∑ s, ∑ a, G s a * (η * G s a) = η * N := by
    simp only [N, Finset.mul_sum]
    exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun a _ => by ring
  have h2 : ∑ s, ∑ a, (η * G s a) ^ 2 = η ^ 2 * N := by
    simp only [N, Finset.mul_sum]
    exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun a _ => by ring
  rw [h1, h2] at h
  have hq : 4 / (1 - γ) ^ 3 * η ≤ 1 / 2 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    linarith
  have hpen : 4 / (1 - γ) ^ 3 * (η ^ 2 * N) ≤ 1 / 2 * (η * N) := by
    calc 4 / (1 - γ) ^ 3 * (η ^ 2 * N) = (4 / (1 - γ) ^ 3 * η) * (η * N) := by ring
      _ ≤ 1 / 2 * (η * N) := mul_le_mul_of_nonneg_right hq (mul_nonneg hη0 hN)
  linarith

/-- **The gradient vanishes.** With rewards in `[0, 1]`, a start distribution `μ`, and a step
`0 < η ≤ (1 - γ) ^ 3 / 8`, the squared lengths of the gradients are summable, so every gradient
entry tends to zero. -/
theorem tendsto_softmaxGradient_pg (m : MDP S A) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hr : ∀ s a, m.reward s a ∈ Set.Icc (0 : ℝ) 1) {μ : S → ℝ} (hμ : ∀ s, 0 ≤ μ s)
    (hμ1 : ∑ s, μ s = 1) {η : ℝ} (hη0 : 0 < η) (hη : η ≤ (1 - γ) ^ 3 / 8) (θ₁ : S → A → ℝ)
    (s : S) (a : A) :
    Filter.Tendsto (fun t => m.softmaxGradient
        (softmaxPolicy (m.pgScores hγ0 hγ1 μ η θ₁ t)) hγ0 hγ1 μ s a)
      Filter.atTop (nhds 0) := by
  have hγ : 0 < 1 - γ := sub_pos.mpr hγ1
  set θ := m.pgScores hγ0 hγ1 μ η θ₁
  set G : ℕ → S → A → ℝ := fun t => m.softmaxGradient (softmaxPolicy (θ t)) hγ0 hγ1 μ
  set N : ℕ → ℝ := fun t => ∑ s, ∑ a, G t s a ^ 2
  set J : ℕ → ℝ := fun t => ∑ s₀, μ s₀ * m.policyValue (softmaxPolicy (θ t)) hγ0 hγ1 s₀
  have hN (t : ℕ) : 0 ≤ N t :=
    Finset.sum_nonneg fun s _ => Finset.sum_nonneg fun a _ => sq_nonneg _
  have hstep (t : ℕ) : η / 2 * N t ≤ J (t + 1) - J t := by
    have h := m.sum_policyValue_pg_succ_ge_of_le hγ0 hγ1 hr hμ hμ1 hη0.le hη θ₁ t
    change J t + η / 2 * N t ≤ J (t + 1) at h
    linarith
  have hJ (t : ℕ) : J t ∈ Set.Icc 0 (1 / (1 - γ)) := by
    have hV (s₀ : S) := m.policyValue_mem_Icc (softmaxPolicy (θ t)) hγ0 hγ1 hr s₀
    constructor
    · exact Finset.sum_nonneg fun s₀ _ => mul_nonneg (hμ s₀) (hV s₀).1
    · calc J t ≤ ∑ s₀, μ s₀ * (1 / (1 - γ)) :=
            Finset.sum_le_sum fun s₀ _ => mul_le_mul_of_nonneg_left (hV s₀).2 (hμ s₀)
        _ = 1 / (1 - γ) := by rw [← Finset.sum_mul, hμ1, one_mul]
  have hsum : Summable fun t => η / 2 * N t := by
    refine summable_of_sum_range_le (c := 1 / (1 - γ))
      (fun t => mul_nonneg (by positivity) (hN t)) fun n => ?_
    calc ∑ t ∈ Finset.range n, η / 2 * N t
        ≤ ∑ t ∈ Finset.range n, (J (t + 1) - J t) := Finset.sum_le_sum fun t _ => hstep t
      _ = J n - J 0 := Finset.sum_range_sub J n
      _ ≤ 1 / (1 - γ) := by linarith [(hJ n).2, (hJ 0).1]
  have hNlim : Filter.Tendsto N Filter.atTop (nhds 0) := by
    have h := (hsum.tendsto_atTop_zero).const_mul (2 / η)
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
    (hμ1 : ∑ s, μ s = 1) {η : ℝ} (hη0 : 0 < η) (hη : η ≤ (1 - γ) ^ 3 / 8) (θ₁ : S → A → ℝ)
    {s : S} (hs : 0 < μ s) (a : A) :
    Filter.Tendsto (fun t =>
        (softmaxPolicy (m.pgScores hγ0 hγ1 μ η θ₁ t) s a).toReal *
          m.advantage (softmaxPolicy (m.pgScores hγ0 hγ1 μ η θ₁ t)) hγ0 hγ1 s a)
      Filter.atTop (nhds 0) := by
  have hγ : 0 < 1 - γ := sub_pos.mpr hγ1
  set θ := m.pgScores hγ0 hγ1 μ η θ₁
  have hG := m.tendsto_softmaxGradient_pg hγ0 hγ1 hr hμ hμ1 hη0 hη θ₁ s a
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

omit [Nonempty A] in
/-- With start weights summing to one, the weighted visitation is at most one. -/
theorem weightedVisitation_le_one (m : MDP S A) (π : StationaryPolicy S A)
    {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) {μ : S → ℝ} (hμ : ∀ s, 0 ≤ μ s)
    (hμ1 : ∑ s, μ s = 1) (s : S) : m.weightedVisitation π hγ0 hγ1 μ s ≤ 1 := by
  calc m.weightedVisitation π hγ0 hγ1 μ s ≤ ∑ s₀, μ s₀ * 1 :=
        Finset.sum_le_sum fun s₀ _ => mul_le_mul_of_nonneg_left
          (m.discountedVisitation_le_one π hγ0 hγ1 s₀ s) (hμ s₀)
    _ = 1 := by rw [← Finset.sum_mul, hμ1, one_mul]

/-- **Scores of persistently bad actions go to `-∞` (Agarwal et al., Lemma C.11).** With rewards
in `[0, 1]`, a start distribution `μ`, and any step `η > 0`, if `μ s > 0` and from some time on
the advantage of `a₀` at `s` stays below `-ε < 0`, then the score of `a₀` at `s` tends to `-∞`. -/
theorem tendsto_pgScores_atBot (m : MDP S A) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hr : ∀ s a, m.reward s a ∈ Set.Icc (0 : ℝ) 1) {μ : S → ℝ} (hμ : ∀ s, 0 ≤ μ s)
    (hμ1 : ∑ s, μ s = 1) {η : ℝ} (hη0 : 0 < η) (θ₁ : S → A → ℝ) {s : S} (hs : 0 < μ s)
    {a₀ : A} {ε : ℝ} (hε : 0 < ε) {T : ℕ}
    (hA : ∀ t, T ≤ t → m.advantage (softmaxPolicy (m.pgScores hγ0 hγ1 μ η θ₁ t)) hγ0 hγ1 s a₀ ≤
      -ε) :
    Filter.Tendsto (fun t => m.pgScores hγ0 hγ1 μ η θ₁ t s a₀) Filter.atTop Filter.atBot := by
  classical
  have hγ : 0 < 1 - γ := sub_pos.mpr hγ1
  set θ := m.pgScores hγ0 hγ1 μ η θ₁
  set p : ℕ → A → ℝ := fun t a => (softmaxPolicy (θ t) s a).toReal
  set d : ℕ → ℝ := fun t => m.weightedVisitation (softmaxPolicy (θ t)) hγ0 hγ1 μ s
  set Ad : ℕ → A → ℝ := fun t a => m.advantage (softmaxPolicy (θ t)) hγ0 hγ1 s a
  have hpexp (t : ℕ) (a : A) :
      p t a = Real.exp (θ t s a) / ∑ b, Real.exp (θ t s b) := softmaxPolicy_apply _ _ _
  have hg (t : ℕ) (a : A) : η * m.softmaxGradient (softmaxPolicy (θ t)) hγ0 hγ1 μ s a =
      η * (1 - γ)⁻¹ * d t * (p t a * Ad t a) := by
    simp only [softmaxGradient, d, p, Ad]; ring
  have hd1 (t : ℕ) : d t ≤ 1 := m.weightedVisitation_le_one _ hγ0 hγ1 hμ hμ1 s
  have hd0 (t : ℕ) : (1 - γ) * μ s ≤ d t := m.mul_le_weightedVisitation _ hγ0 hγ1 hμ s
  have hp0 (t : ℕ) (a : A) : 0 ≤ p t a := ENNReal.toReal_nonneg
  refine tendsto_atBot_of_softmax_step (θ := fun t a => θ t s a)
    (g := fun t a => η * m.softmaxGradient (softmaxPolicy (θ t)) hγ0 hγ1 μ s a)
    (K := η * (1 - γ)⁻¹ * (1 / (1 - γ))) (κ := η * μ s * ε) (T := T)
    (fun t a => by simp only [θ, pgScores]) (fun t => ?_) (fun t a => ?_) (by positivity)
    (fun t ht => ?_)
  · have h0 := m.expect_advantage (softmaxPolicy (θ t)) hγ0 hγ1 s
    unfold expect at h0
    simp only [hg, ← Finset.mul_sum]
    change η * (1 - γ)⁻¹ * d t * ∑ a, p t a * Ad t a = 0
    simp only [p, Ad, h0, mul_zero]
  · rw [hg, ← hpexp, abs_mul, abs_of_nonneg (mul_nonneg (by positivity)
      ((by positivity : (0 : ℝ) ≤ (1 - γ) * μ s).trans (hd0 t))), abs_mul,
      abs_of_nonneg (hp0 t a)]
    have hAb := m.abs_advantage_le (softmaxPolicy (θ t)) hγ0 hγ1 hr s a
    have hc : 0 ≤ η * (1 - γ)⁻¹ := by positivity
    calc η * (1 - γ)⁻¹ * d t * (p t a * |Ad t a|)
        ≤ η * (1 - γ)⁻¹ * 1 * (p t a * (1 / (1 - γ))) := by
          have hd1t := hd1 t
          gcongr
      _ = _ := by ring
  · rw [hg, ← hpexp]
    have hAt : Ad t a₀ ≤ -ε := hA t ht
    have hc : 0 ≤ η * (1 - γ)⁻¹ := by positivity
    have hpA : p t a₀ * Ad t a₀ ≤ -(p t a₀ * ε) := by nlinarith [hp0 t a₀]
    have hpA0 : p t a₀ * Ad t a₀ ≤ 0 := by nlinarith [hp0 t a₀]
    calc η * (1 - γ)⁻¹ * d t * (p t a₀ * Ad t a₀)
        ≤ η * (1 - γ)⁻¹ * ((1 - γ) * μ s) * (p t a₀ * Ad t a₀) := by
          have := mul_le_mul_of_nonpos_right (hd0 t) hpA0
          nlinarith
      _ ≤ η * (1 - γ)⁻¹ * ((1 - γ) * μ s) * (-(p t a₀ * ε)) :=
          mul_le_mul_of_nonneg_left hpA (by positivity)
      _ = -(η * μ s * ε) * p t a₀ := by field_simp

end MDP

end Rlib
