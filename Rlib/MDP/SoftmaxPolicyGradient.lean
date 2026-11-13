module

public import Rlib.MDP.GradientDomination

/-! # Convergence rate of exact softmax policy gradient

Exact softmax policy gradient adds `η` times the gradient of the `μ`-weighted value to the
scores. With rewards bounded by `R > 0` and step `η = (1 - γ) ^ 3 / (12 * R)`, each step raises
the weighted value by at least `η / 2` times the squared length of the gradient. Combined with
gradient domination, the gap to a deterministic policy `b` after `T` steps is at most
`24 * R * C ^ 2 * |S| / ((1 - γ) ^ 3 * c ^ 2 * T)`, provided every iterate gives `b` probability
at least `c` and its visitation stays within a factor `C` of the iterate's.

The lower bound `c` on the probability of `b` is a hypothesis here. For an optimal `b`, the
literature proves it from the asymptotic convergence of policy gradient; that proof is not
formalized.
-/

@[expose] public section

noncomputable section

namespace Rlib

/-- **A `1 / t` rate from a quadratic decrease.** If a sequence never increases and drops by at
least `κ * δ t ^ 2` whenever it is nonnegative, then `δ t ≤ 1 / (κ * t)` for `t > 0`. -/
theorem le_one_div_mul_of_le_sub_mul_sq {δ : ℕ → ℝ} {κ : ℝ} (hκ : 0 < κ)
    (hmono : ∀ t, δ (t + 1) ≤ δ t) (hstep : ∀ t, 0 ≤ δ t → δ (t + 1) ≤ δ t - κ * δ t ^ 2)
    {t : ℕ} (ht : 0 < t) : δ t ≤ 1 / (κ * t) := by
  have key : ∀ n : ℕ, δ n ≤ 0 ∨ (0 < δ n ∧ κ * n ≤ 1 / δ n) := by
    intro n
    induction n with
    | zero =>
      rcases le_or_gt (δ 0) 0 with h | h
      · exact Or.inl h
      · exact Or.inr ⟨h, by simpa using (one_div_pos.mpr h).le⟩
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

/-- **Ascent for the weighted value.** One gradient step of size `η ≥ 0` raises the
`μ`-weighted value by at least `(η - 6 * R * η ^ 2 / (1 - γ) ^ 3)` times the squared length of
the gradient. -/
theorem sum_policyValue_gradient_step_ge (m : MDP S A) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    {R : ℝ} (hR : ∀ s a, |m.reward s a| ≤ R) {μ : S → ℝ} (hμ : ∀ s, 0 ≤ μ s)
    (hμ1 : ∑ s, μ s = 1) (θ : S → A → ℝ) {η : ℝ} (hη : 0 ≤ η) :
    ∑ s₀, μ s₀ * m.policyValue (softmaxPolicy θ) hγ0 hγ1 s₀ +
        (η - 6 * R * η ^ 2 / (1 - γ) ^ 3) *
          ∑ s, ∑ a, m.softmaxGradient (softmaxPolicy θ) hγ0 hγ1 μ s a ^ 2 ≤
      ∑ s₀, μ s₀ * m.policyValue (softmaxPolicy fun s a =>
        θ s a + η * m.softmaxGradient (softmaxPolicy θ) hγ0 hγ1 μ s a) hγ0 hγ1 s₀ := by
  set G := m.softmaxGradient (softmaxPolicy θ) hγ0 hγ1 μ
  set N := ∑ s, ∑ a, G s a ^ 2
  have hN : 0 ≤ N := Finset.sum_nonneg fun s _ => Finset.sum_nonneg fun a _ => sq_nonneg _
  have hG (s : S) (a : A) : |G s a| ≤ Real.sqrt N := by
    refine Real.abs_le_sqrt ?_
    calc G s a ^ 2 ≤ ∑ a', G s a' ^ 2 :=
          Finset.single_le_sum (f := fun a' => G s a' ^ 2) (fun _ _ => sq_nonneg _)
            (Finset.mem_univ a)
      _ ≤ N := Finset.single_le_sum (f := fun s' => ∑ a', G s' a' ^ 2)
            (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ s)
  have hstep (s₀ : S) := m.policyValue_softmax_line_ge hγ0 hγ1 hR θ G hG s₀ hη
  rw [Real.sq_sqrt hN] at hstep
  have hsum := Finset.sum_le_sum fun s₀ (_ : s₀ ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_left (hstep s₀) (hμ s₀)
  have hlin := m.sum_directionalGain_eq (softmaxPolicy θ) hγ0 hγ1 μ G
  have hGG : ∑ s, ∑ a, G s a * G s a = N :=
    Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun a _ => (sq _).symm
  rw [hGG] at hlin
  have hexpand : ∑ s₀, μ s₀ * (m.policyValue (softmaxPolicy θ) hγ0 hγ1 s₀ +
      η * ((1 - γ)⁻¹ * m.directionalGain (softmaxPolicy θ) hγ0 hγ1 G s₀) -
        6 * N * R * η ^ 2 / (1 - γ) ^ 3) =
      ∑ s₀, μ s₀ * m.policyValue (softmaxPolicy θ) hγ0 hγ1 s₀ +
        (η - 6 * R * η ^ 2 / (1 - γ) ^ 3) * N := by
    simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [← Finset.sum_mul, hμ1]
    have : ∑ s₀, μ s₀ * (η * ((1 - γ)⁻¹ * m.directionalGain (softmaxPolicy θ) hγ0 hγ1 G s₀)) =
        η * N := by
      rw [← hlin, Finset.mul_sum]
      exact Finset.sum_congr rfl fun s₀ _ => by ring
    rw [this]
    ring
  rw [← hexpand]
  exact hsum

/-- The action scores after `t` steps of exact softmax policy gradient on the `μ`-weighted value
with step size `η`, starting from scores `θ₀`. -/
def pgScores (m : MDP S A) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (μ : S → ℝ) (η : ℝ)
    (θ₀ : S → A → ℝ) : ℕ → S → A → ℝ
  | 0 => θ₀
  | t + 1 => fun s a => m.pgScores hγ0 hγ1 μ η θ₀ t s a +
      η * m.softmaxGradient (softmaxPolicy (m.pgScores hγ0 hγ1 μ η θ₀ t)) hγ0 hγ1 μ s a

/-- **Exact softmax policy gradient converges at rate `1 / T`.** Take rewards bounded by
`R > 0`, a start distribution `μ`, and step `η = (1 - γ) ^ 3 / (12 * R)`. Suppose every iterate
gives the deterministic policy `b` probability at least `c > 0` at every state, and the
`μ`-weighted visitation of `b` is at most `C > 0` times that of every iterate. Then after
`T > 0` steps the `μ`-weighted gap to `b` is at most
`24 * R * C ^ 2 * |S| / ((1 - γ) ^ 3 * c ^ 2 * T)`. -/
theorem sum_sub_policyValue_pg_le [Nonempty S] (m : MDP S A) {γ : ℝ} (hγ0 : 0 ≤ γ)
    (hγ1 : γ < 1) {R : ℝ} (hR0 : 0 < R) (hR : ∀ s a, |m.reward s a| ≤ R) {μ : S → ℝ}
    (hμ : ∀ s, 0 ≤ μ s) (hμ1 : ∑ s, μ s = 1) (θ₀ : S → A → ℝ) (b : S → A) {c C : ℝ}
    (hc : 0 < c) (hC : 0 < C)
    (hπ : ∀ t s, c ≤ (softmaxPolicy (m.pgScores hγ0 hγ1 μ ((1 - γ) ^ 3 / (12 * R)) θ₀ t) s
      (b s)).toReal)
    (hvis : ∀ t s, m.weightedVisitation (fun s => PMF.pure (b s)) hγ0 hγ1 μ s ≤
      C * m.weightedVisitation
        (softmaxPolicy (m.pgScores hγ0 hγ1 μ ((1 - γ) ^ 3 / (12 * R)) θ₀ t)) hγ0 hγ1 μ s)
    {T : ℕ} (hT : 0 < T) :
    ∑ s₀, μ s₀ * (m.policyValue (fun s => PMF.pure (b s)) hγ0 hγ1 s₀ -
        m.policyValue (softmaxPolicy (m.pgScores hγ0 hγ1 μ ((1 - γ) ^ 3 / (12 * R)) θ₀ T))
          hγ0 hγ1 s₀) ≤
      24 * R * C ^ 2 * Fintype.card S / ((1 - γ) ^ 3 * c ^ 2 * T) := by
  have hγ : 0 < 1 - γ := sub_pos.mpr hγ1
  set η := (1 - γ) ^ 3 / (12 * R)
  have hη : 0 < η := by positivity
  set θ := m.pgScores hγ0 hγ1 μ η θ₀
  set G : ℕ → S → A → ℝ := fun t => m.softmaxGradient (softmaxPolicy (θ t)) hγ0 hγ1 μ
  set N : ℕ → ℝ := fun t => ∑ s, ∑ a, G t s a ^ 2
  set Vb := m.policyValue (fun s => PMF.pure (b s)) hγ0 hγ1
  set δ : ℕ → ℝ := fun t =>
    ∑ s₀, μ s₀ * (Vb s₀ - m.policyValue (softmaxPolicy (θ t)) hγ0 hγ1 s₀)
  set β := (C / c) ^ 2 * Fintype.card S
  have hβ : 0 < β := by
    have : (0 : ℝ) < Fintype.card S := by exact_mod_cast Fintype.card_pos
    positivity
  have hcoef : η - 6 * R * η ^ 2 / (1 - γ) ^ 3 = η / 2 := by
    simp only [η]; field_simp; ring
  have hN (t : ℕ) : 0 ≤ N t :=
    Finset.sum_nonneg fun s _ => Finset.sum_nonneg fun a _ => sq_nonneg _
  have hdesc (t : ℕ) : δ (t + 1) ≤ δ t - η / 2 * N t := by
    have h := m.sum_policyValue_gradient_step_ge hγ0 hγ1 hR hμ hμ1 (θ t) hη.le
    rw [hcoef] at h
    have hsplit (k : ℕ) : δ k = ∑ s₀, μ s₀ * Vb s₀ -
        ∑ s₀, μ s₀ * m.policyValue (softmaxPolicy (θ k)) hγ0 hγ1 s₀ := by
      simp only [δ, mul_sub, Finset.sum_sub_distrib]
    rw [hsplit, hsplit]
    change _ ≤ ∑ s₀, μ s₀ * m.policyValue (softmaxPolicy (θ (t + 1))) hγ0 hγ1 s₀ at h
    linarith
  have hdom (t : ℕ) (ht : 0 ≤ δ t) : δ t ^ 2 ≤ β * N t :=
    m.sq_sum_sub_policyValue_le (softmaxPolicy (θ t)) hγ0 hγ1 hμ hμ b hc hC.le (hπ t)
      (hvis t) ht
  have hrate := le_one_div_mul_of_le_sub_mul_sq (δ := δ) (κ := η / (2 * β)) (by positivity)
    (fun t => (hdesc t).trans (by linarith [mul_nonneg hη.le (hN t)]))
    (fun t ht => by
      have h1 := hdesc t
      have h2 := hdom t ht
      have : η / (2 * β) * δ t ^ 2 ≤ η / 2 * N t := by
        rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        nlinarith
      linarith) hT
  refine hrate.trans (le_of_eq ?_)
  simp only [η, β]
  field_simp
  ring

end MDP

end Rlib
