module

public import Rlib.MDP.GradientDomination

/-! # Convergence rate of exact softmax policy gradient

This file follows Mei, Xiao, Szepesvári, and Schuurmans, *On the Global Convergence Rates of
Softmax Policy Gradient Methods* (ICML 2020). Rewards lie in `[0, 1]`, start states are drawn
from `μ` with `μ s > 0`, and the softmax scores follow the gradient of `V (μ)` with step
`η = (1 - γ) ^ 3 / 8`, starting from arbitrary scores `θ₁`.

* `sum_policyValue_softmax_ge` is the smoothness inequality of their Lemma 7, in the form
  `V θ' ≥ V θ + ⟪∇ V θ, θ' - θ⟫ - 4 / (1 - γ) ^ 3 * ‖θ' - θ‖ ^ 2` used by the proof.
* `sum_policyValue_pg_succ_ge` is the improvement `V θ_{t+1} - V θ_t ≥ (1 - γ) ^ 3 / 16 * ‖∇‖ ^ 2`.
* `sum_sub_policyValue_pg_le` is their Theorem 4: for every `t ≥ 1`,
  `V* ρ - V θ_t ρ ≤ 16 * |S| / (c ^ 2 * (1 - γ) ^ 6 * t) * ‖d*_μ / μ‖∞ ^ 2 * ‖1 / μ‖∞`.

As in the paper, `c` is a lower bound on the probability that every iterate gives the optimal
action. The paper proves `c > 0` (their Lemma 9) from the asymptotic convergence of policy
gradient; that proof is not formalized, so `c` enters as a hypothesis. Sup norms enter as bounds
`D` and `M` with `d*_μ s ≤ D * μ s` and `1 ≤ M * μ s`.
-/

@[expose] public section

noncomputable section

namespace Rlib

/-- **A `1 / t` rate from a quadratic decrease.** If a sequence never increases, drops by at
least `κ * δ t ^ 2` whenever it is nonnegative, and starts at most `1 / κ`, then
`δ t ≤ 1 / (κ * (t + 1))`. -/
theorem le_one_div_mul_of_le_sub_mul_sq {δ : ℕ → ℝ} {κ : ℝ} (hκ : 0 < κ)
    (hmono : ∀ t, δ (t + 1) ≤ δ t) (hstep : ∀ t, 0 ≤ δ t → δ (t + 1) ≤ δ t - κ * δ t ^ 2)
    (h0 : δ 0 ≤ 1 / κ) (t : ℕ) : δ t ≤ 1 / (κ * (t + 1)) := by
  have key : ∀ n : ℕ, δ n ≤ 0 ∨ (0 < δ n ∧ κ * (n + 1) ≤ 1 / δ n) := by
    intro n
    induction n with
    | zero =>
      rcases le_or_gt (δ 0) 0 with h | h
      · exact Or.inl h
      · refine Or.inr ⟨h, ?_⟩
        rw [le_div_iff₀ h]
        rw [le_div_iff₀ hκ] at h0
        push_cast
        linarith
    | succ n ih =>
      rcases ih with h | ⟨h, hn⟩
      · exact Or.inl ((hmono n).trans h)
      · rcases le_or_gt (δ (n + 1)) 0 with h' | h'
        · exact Or.inl h'
        · refine Or.inr ⟨h', ?_⟩
          have hs := hstep n h.le
          have hrec : 1 / δ n + κ ≤ 1 / δ (n + 1) := by
            rw [div_add' _ _ _ h.ne', div_le_div_iff₀ h h', one_mul]
            have hpos : 0 ≤ 1 + κ * δ n := by positivity
            nlinarith [mul_le_mul_of_nonneg_left hs hpos, sq_nonneg (κ * δ n),
              mul_pos hκ h]
          push_cast
          linarith
  rcases key t with h | ⟨h, hn⟩
  · exact h.trans (by positivity)
  · rw [le_div_iff₀ (by positivity)]
    rw [le_div_iff₀ h] at hn
    linarith

namespace MDP

variable {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [Nonempty A]

/-- **Smoothness of the softmax value (Mei et al., Lemma 7).** For rewards in `[0, 1]` and a
start distribution `μ`, the weighted value satisfies
`V θ' ≥ V θ + ⟪∇ V θ, θ' - θ⟫ - 4 / (1 - γ) ^ 3 * ‖θ' - θ‖ ^ 2`. -/
theorem sum_policyValue_softmax_ge (m : MDP S A) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hr : ∀ s a, m.reward s a ∈ Set.Icc (0 : ℝ) 1) {μ : S → ℝ} (hμ : ∀ s, 0 ≤ μ s)
    (hμ1 : ∑ s, μ s = 1) (θ θ' : S → A → ℝ) :
    ∑ s₀, μ s₀ * m.policyValue (softmaxPolicy θ) hγ0 hγ1 s₀ +
        ∑ s, ∑ a, m.softmaxGradient (softmaxPolicy θ) hγ0 hγ1 μ s a * (θ' s a - θ s a) -
          4 / (1 - γ) ^ 3 * ∑ s, ∑ a, (θ' s a - θ s a) ^ 2 ≤
      ∑ s₀, μ s₀ * m.policyValue (softmaxPolicy θ') hγ0 hγ1 s₀ := by
  have hγ : 0 < 1 - γ := sub_pos.mpr hγ1
  set u : S → A → ℝ := fun s a => θ' s a - θ s a
  set N := ∑ s, ∑ a, u s a ^ 2
  have hN : 0 ≤ N := Finset.sum_nonneg fun s _ => Finset.sum_nonneg fun a _ => sq_nonneg _
  have hu (s : S) (a : A) : |u s a| ≤ Real.sqrt N := by
    refine Real.abs_le_sqrt ?_
    calc u s a ^ 2 ≤ ∑ a', u s a' ^ 2 :=
          Finset.single_le_sum (f := fun a' => u s a' ^ 2) (fun _ _ => sq_nonneg _)
            (Finset.mem_univ a)
      _ ≤ N := Finset.single_le_sum (f := fun s' => ∑ a', u s' a' ^ 2)
            (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ s)
  have hθ' : (fun s a => θ s a + 1 * u s a) = θ' := by
    funext s a; simp only [u]; ring
  have hstep (s₀ : S) := m.policyValue_softmax_line_ge hγ0 hγ1 hr θ u hu s₀ zero_le_one
  rw [Real.sq_sqrt hN, hθ'] at hstep
  have hsum := Finset.sum_le_sum fun s₀ (_ : s₀ ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_left (hstep s₀) (hμ s₀)
  have hlin := m.sum_directionalGain_eq (softmaxPolicy θ) hγ0 hγ1 μ u
  have hexpand : ∑ s₀, μ s₀ * (m.policyValue (softmaxPolicy θ) hγ0 hγ1 s₀ +
      1 * ((1 - γ)⁻¹ * m.directionalGain (softmaxPolicy θ) hγ0 hγ1 u s₀) -
        3 * N * 1 ^ 2 / (1 - γ) ^ 3) =
      ∑ s₀, μ s₀ * m.policyValue (softmaxPolicy θ) hγ0 hγ1 s₀ +
        ∑ s, ∑ a, m.softmaxGradient (softmaxPolicy θ) hγ0 hγ1 μ s a * u s a -
          3 / (1 - γ) ^ 3 * N := by
    simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, one_mul]
    rw [← Finset.sum_mul, hμ1, hlin]
    ring
  have hpen : 3 / (1 - γ) ^ 3 * N ≤ 4 / (1 - γ) ^ 3 * N :=
    mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (by norm_num) (by positivity)) hN
  rw [hexpand] at hsum
  linarith

/-- The action scores after `t` steps of exact softmax policy gradient on `V (μ)` with step
size `η`, starting from scores `θ₁`. In the paper's indexing these are the scores `θ_{t+1}`. -/
def pgScores (m : MDP S A) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (μ : S → ℝ) (η : ℝ)
    (θ₁ : S → A → ℝ) : ℕ → S → A → ℝ
  | 0 => θ₁
  | t + 1 => fun s a => m.pgScores hγ0 hγ1 μ η θ₁ t s a +
      η * m.softmaxGradient (softmaxPolicy (m.pgScores hγ0 hγ1 μ η θ₁ t)) hγ0 hγ1 μ s a

/-- **Improvement per step.** With step `η = (1 - γ) ^ 3 / 8`, each step of exact softmax policy
gradient raises `V (μ)` by at least `(1 - γ) ^ 3 / 16` times the squared length of the
gradient. -/
theorem sum_policyValue_pg_succ_ge (m : MDP S A) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hr : ∀ s a, m.reward s a ∈ Set.Icc (0 : ℝ) 1) {μ : S → ℝ} (hμ : ∀ s, 0 ≤ μ s)
    (hμ1 : ∑ s, μ s = 1) (θ₁ : S → A → ℝ) (t : ℕ) :
    ∑ s₀, μ s₀ * m.policyValue
        (softmaxPolicy (m.pgScores hγ0 hγ1 μ ((1 - γ) ^ 3 / 8) θ₁ t)) hγ0 hγ1 s₀ +
        (1 - γ) ^ 3 / 16 * ∑ s, ∑ a, m.softmaxGradient
          (softmaxPolicy (m.pgScores hγ0 hγ1 μ ((1 - γ) ^ 3 / 8) θ₁ t)) hγ0 hγ1 μ s a ^ 2 ≤
      ∑ s₀, μ s₀ * m.policyValue
        (softmaxPolicy (m.pgScores hγ0 hγ1 μ ((1 - γ) ^ 3 / 8) θ₁ (t + 1))) hγ0 hγ1 s₀ := by
  have hγ : 0 < 1 - γ := sub_pos.mpr hγ1
  set η := (1 - γ) ^ 3 / 8
  set θ := m.pgScores hγ0 hγ1 μ η θ₁ t
  set G := m.softmaxGradient (softmaxPolicy θ) hγ0 hγ1 μ
  have h := m.sum_policyValue_softmax_ge hγ0 hγ1 hr hμ hμ1 θ
    (m.pgScores hγ0 hγ1 μ η θ₁ (t + 1))
  have hdiff (s : S) (a : A) : m.pgScores hγ0 hγ1 μ η θ₁ (t + 1) s a - θ s a = η * G s a := by
    simp only [pgScores, θ, G]; ring
  simp only [hdiff] at h
  have h1 : ∑ s, ∑ a, G s a * (η * G s a) = η * ∑ s, ∑ a, G s a ^ 2 := by
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun a _ => by ring
  have h2 : ∑ s, ∑ a, (η * G s a) ^ 2 = η ^ 2 * ∑ s, ∑ a, G s a ^ 2 := by
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun a _ => by ring
  rw [h1, h2] at h
  have hcoef : η - 4 / (1 - γ) ^ 3 * η ^ 2 = (1 - γ) ^ 3 / 16 := by
    simp only [η]; field_simp; ring
  have : η * ∑ s, ∑ a, G s a ^ 2 - 4 / (1 - γ) ^ 3 * (η ^ 2 * ∑ s, ∑ a, G s a ^ 2) =
      (1 - γ) ^ 3 / 16 * ∑ s, ∑ a, G s a ^ 2 := by rw [← hcoef]; ring
  linarith

omit [Nonempty A] in
/-- With start weights `μ ≥ 0`, the weighted visitation is at least `(1 - γ) * μ`. -/
theorem mul_le_weightedVisitation (m : MDP S A) (π : StationaryPolicy S A) {γ : ℝ}
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) {μ : S → ℝ} (hμ : ∀ s, 0 ≤ μ s) (s : S) :
    (1 - γ) * μ s ≤ m.weightedVisitation π hγ0 hγ1 μ s := by
  calc (1 - γ) * μ s ≤ μ s * m.discountedVisitation π hγ0 hγ1 s s := by
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_left (m.one_sub_le_discountedVisitation_self π hγ0 hγ1 s)
          (hμ s)
    _ ≤ _ := Finset.single_le_sum (f := fun s₀ => μ s₀ * m.discountedVisitation π hγ0 hγ1 s₀ s)
          (fun s₀ _ => mul_nonneg (hμ s₀) (m.discountedVisitation_nonneg π hγ0 hγ1 s₀ s))
          (Finset.mem_univ s)

/-- **Exact softmax policy gradient converges at rate `1 / t` (Mei et al., Theorem 4).** Take
rewards in `[0, 1]`, a start distribution `μ` with `μ s > 0`, any distribution `ρ`, step
`η = (1 - γ) ^ 3 / 8`, and initial scores `θ₁`. Let `b` be an optimal deterministic policy and
suppose every iterate gives `b` probability at least `c > 0` at every state. If
`d*_μ s ≤ D * μ s` and `1 ≤ M * μ s` for all `s`, then for every `t ≥ 1` the iterate `θ_t`
satisfies `V* ρ - V θ_t ρ ≤ 16 * |S| / (c ^ 2 * (1 - γ) ^ 6 * t) * D ^ 2 * M`. -/
theorem sum_sub_policyValue_pg_le [Nonempty S] (m : MDP S A) {γ : ℝ} (hγ0 : 0 ≤ γ)
    (hγ1 : γ < 1) (hr : ∀ s a, m.reward s a ∈ Set.Icc (0 : ℝ) 1) {μ ρ : S → ℝ}
    (hμ : ∀ s, 0 < μ s) (hμ1 : ∑ s, μ s = 1) (hρ : ∀ s, 0 ≤ ρ s) (hρ1 : ∑ s, ρ s = 1)
    (θ₁ : S → A → ℝ) (b : S → A)
    (hb : ∀ (π : StationaryPolicy S A) s,
      m.policyValue π hγ0 hγ1 s ≤ m.policyValue (fun s => PMF.pure (b s)) hγ0 hγ1 s)
    {c : ℝ} (hc : 0 < c)
    (hπ : ∀ t s, c ≤ (softmaxPolicy (m.pgScores hγ0 hγ1 μ ((1 - γ) ^ 3 / 8) θ₁ t) s
      (b s)).toReal)
    {D M : ℝ} (hD : ∀ s, m.weightedVisitation (fun s => PMF.pure (b s)) hγ0 hγ1 μ s ≤ D * μ s)
    (hM : ∀ s, 1 ≤ M * μ s) (t : ℕ) (ht : 1 ≤ t) :
    ∑ s₀, ρ s₀ * (m.policyValue (fun s => PMF.pure (b s)) hγ0 hγ1 s₀ -
        m.policyValue (softmaxPolicy (m.pgScores hγ0 hγ1 μ ((1 - γ) ^ 3 / 8) θ₁ (t - 1)))
          hγ0 hγ1 s₀) ≤
      16 * Fintype.card S / (c ^ 2 * (1 - γ) ^ 6 * t) * D ^ 2 * M := by
  have hγ : 0 < 1 - γ := sub_pos.mpr hγ1
  have hμ0 (s : S) : 0 ≤ μ s := (hμ s).le
  set η := (1 - γ) ^ 3 / 8
  set θ := m.pgScores hγ0 hγ1 μ η θ₁
  set Vb := m.policyValue (fun s => PMF.pure (b s)) hγ0 hγ1
  set V : ℕ → S → ℝ := fun n => m.policyValue (softmaxPolicy (θ n)) hγ0 hγ1
  set N : ℕ → ℝ := fun n =>
    ∑ s, ∑ a, m.softmaxGradient (softmaxPolicy (θ n)) hγ0 hγ1 μ s a ^ 2
  set δ : ℕ → ℝ := fun n => ∑ s₀, μ s₀ * (Vb s₀ - V n s₀)
  set S' : ℝ := (Fintype.card S : ℝ)
  have hS : 1 ≤ S' := Nat.one_le_cast.mpr Fintype.card_pos
  -- Basic facts about the constants.
  obtain ⟨s₁⟩ := ‹Nonempty S›
  have hc1 : c ≤ 1 := (hπ 0 s₁).trans (by
    rw [← probability_sum (softmaxPolicy (θ 0) s₁)]
    exact Finset.single_le_sum (f := fun a => (softmaxPolicy (θ 0) s₁ a).toReal)
      (fun _ _ => ENNReal.toReal_nonneg) (Finset.mem_univ (b s₁)))
  have hD1 : 1 ≤ D := by
    have hsum : ∑ s, m.weightedVisitation (fun s => PMF.pure (b s)) hγ0 hγ1 μ s = 1 := by
      simp only [weightedVisitation]
      rw [Finset.sum_comm]
      simp only [← Finset.mul_sum, m.sum_discountedVisitation, mul_one, hμ1]
    calc (1 : ℝ) = _ := hsum.symm
      _ ≤ ∑ s, D * μ s := Finset.sum_le_sum fun s _ => hD s
      _ = D := by rw [← Finset.mul_sum, hμ1, mul_one]
  have hμle (s : S) : μ s ≤ 1 := by
    rw [← hμ1]
    exact Finset.single_le_sum (fun s' _ => hμ0 s') (Finset.mem_univ s)
  have hM0 : 0 < M := pos_of_mul_pos_left (lt_of_lt_of_le one_pos (hM s₁)) (hμ0 s₁)
  -- The visitation ratio against every iterate.
  set C := D / (1 - γ)
  have hvis (n : ℕ) (s : S) : m.weightedVisitation (fun s => PMF.pure (b s)) hγ0 hγ1 μ s ≤
      C * m.weightedVisitation (softmaxPolicy (θ n)) hγ0 hγ1 μ s := by
    have h := m.mul_le_weightedVisitation (softmaxPolicy (θ n)) hγ0 hγ1 hμ0 s
    calc _ ≤ D * μ s := hD s
      _ = C * ((1 - γ) * μ s) := by simp only [C]; field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left h (by positivity)
  -- The recursion for the gap under `μ`.
  set β := (C / c) ^ 2 * S'
  have hβ1 : 1 ≤ β := by
    have hCc : 1 ≤ C / c := by
      rw [le_div_iff₀ hc, one_mul]
      calc c ≤ 1 := hc1
        _ ≤ 1 / (1 - γ) := by rw [le_div_iff₀ hγ, one_mul]; linarith
        _ ≤ C := by simp only [C]; exact div_le_div_of_nonneg_right hD1 hγ.le
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ (C / c) ^ 2 * S' := mul_le_mul (one_le_pow₀ hCc) hS zero_le_one (by positivity)
  have hgap (n : ℕ) (s : S) : 0 ≤ Vb s - V n s := sub_nonneg.mpr (hb _ s)
  have hδ0 (n : ℕ) : 0 ≤ δ n :=
    Finset.sum_nonneg fun s _ => mul_nonneg (hμ0 s) (hgap n s)
  have hN (n : ℕ) : 0 ≤ N n :=
    Finset.sum_nonneg fun s _ => Finset.sum_nonneg fun a _ => sq_nonneg _
  have hdesc (n : ℕ) : δ (n + 1) ≤ δ n - (1 - γ) ^ 3 / 16 * N n := by
    have h := m.sum_policyValue_pg_succ_ge hγ0 hγ1 hr hμ0 hμ1 θ₁ n
    have hsplit (k : ℕ) : δ k = ∑ s₀, μ s₀ * Vb s₀ - ∑ s₀, μ s₀ * V k s₀ := by
      simp only [δ, mul_sub, Finset.sum_sub_distrib]
    rw [hsplit, hsplit]
    change ∑ s₀, μ s₀ * V n s₀ + (1 - γ) ^ 3 / 16 * N n ≤ ∑ s₀, μ s₀ * V (n + 1) s₀ at h
    linarith
  have hdom (n : ℕ) : δ n ^ 2 ≤ β * N n :=
    m.sq_sum_sub_policyValue_le (softmaxPolicy (θ n)) hγ0 hγ1 hμ0 hμ0 b hc (by positivity)
      (hπ n) (hvis n) (hδ0 n)
  set κ := (1 - γ) ^ 3 / (16 * β)
  have hκ : 0 < κ := by positivity
  have hstart : δ 0 ≤ 1 / κ := by
    have hle : δ 0 ≤ 1 / (1 - γ) := by
      calc δ 0 ≤ ∑ s₀, μ s₀ * (1 / (1 - γ)) := Finset.sum_le_sum fun s _ => by
            refine mul_le_mul_of_nonneg_left ?_ (hμ0 s)
            have h1 := (m.policyValue_mem_Icc (fun s => PMF.pure (b s)) hγ0 hγ1 hr s).2
            have h2 := (m.policyValue_mem_Icc (softmaxPolicy (θ 0)) hγ0 hγ1 hr s).1
            change Vb s - V 0 s ≤ _
            linarith
        _ = 1 / (1 - γ) := by rw [← Finset.sum_mul, hμ1, one_mul]
    refine hle.trans ?_
    simp only [κ, one_div_div]
    rw [div_le_div_iff₀ hγ (by positivity), one_mul]
    have h2 : (1 - γ) ^ 2 ≤ 1 := pow_le_one₀ hγ.le (by linarith)
    have h3 : (1 - γ) ^ 3 ≤ 1 - γ := by
      calc (1 - γ) ^ 3 = (1 - γ) ^ 2 * (1 - γ) := by ring
        _ ≤ 1 * (1 - γ) := mul_le_mul_of_nonneg_right h2 hγ.le
        _ = 1 - γ := one_mul _
    nlinarith [mul_le_mul_of_nonneg_right hβ1 hγ.le]
  have hrate := le_one_div_mul_of_le_sub_mul_sq (δ := δ) hκ
    (fun n => (hdesc n).trans (by
      have := mul_nonneg (by positivity : (0 : ℝ) ≤ (1 - γ) ^ 3 / 16) (hN n); linarith))
    (fun n _ => by
      have h1 := hdesc n
      have h2 := hdom n
      have : κ * δ n ^ 2 ≤ (1 - γ) ^ 3 / 16 * N n := by
        simp only [κ]
        rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        nlinarith [pow_pos hγ 3]
      linarith) hstart (t - 1)
  -- Pass from `μ` to `ρ`.
  have hρμ : ∑ s₀, ρ s₀ * (Vb s₀ - V (t - 1) s₀) ≤ M * δ (t - 1) := by
    simp only [δ, Finset.mul_sum]
    refine Finset.sum_le_sum fun s _ => ?_
    have hρs : ρ s ≤ 1 := by
      rw [← hρ1]; exact Finset.single_le_sum (fun s' _ => hρ s') (Finset.mem_univ s)
    calc ρ s * (Vb s - V (t - 1) s) ≤ (M * μ s) * (Vb s - V (t - 1) s) :=
          mul_le_mul_of_nonneg_right (hρs.trans (hM s)) (hgap _ s)
      _ = _ := by ring
  have ht' : ((t - 1 : ℕ) : ℝ) + 1 = t := by
    rw [Nat.cast_sub ht]; push_cast; ring
  rw [ht'] at hrate
  have htpos : (0 : ℝ) < t := by exact_mod_cast ht
  calc _ ≤ M * δ (t - 1) := hρμ
    _ ≤ M * (1 / (κ * t)) := mul_le_mul_of_nonneg_left hrate hM0.le
    _ = 16 * S' / (c ^ 2 * (1 - γ) ^ 5 * t) * D ^ 2 * M := by
        simp only [κ, β, C]; field_simp
    _ ≤ 16 * S' / (c ^ 2 * (1 - γ) ^ 6 * t) * D ^ 2 * M := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ (sq_nonneg _))
          hM0.le
        refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
        have h6 : (1 - γ) ^ 6 ≤ (1 - γ) ^ 5 :=
          pow_le_pow_of_le_one hγ.le (by linarith) (by norm_num)
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h6 (sq_nonneg _))
          htpos.le

end MDP

end Rlib
