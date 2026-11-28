module

public import Rlib.MDP.SoftmaxPGConvergence
public import Rlib.MDP.KLPenaltyPPO
public import Mathlib.Basic.Real.Sign
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

/-! # Global convergence of tabular PPO-Clip

This file follows Huang, Hsieh, Ho, and Wu, *PPO-Clip Attains Global Optimality: Towards Deeper
Understandings of Clipping* (AAAI 2024), Section 4 and Appendix E. Tabular PPO-Clip
(their Algorithm 7) collects a batch of state-action pairs at each iteration and minimizes the
hinge-loss form of the clipped objective by `K t ≥ 1` steps of entropic mirror descent
(their Algorithm 8). With the loss weights set to one, as in their proof, the gradient at a
batch pair `(s, a)` is `-sign (A s a) / π_t (a | s)` while
`(θ̃ (a | s) / π_t (a | s) - 1) * sign (A s a) < ε`, and zero once the ratio is clipped. Each
mirror-descent step multiplies `θ̃ (a | s)` by `exp (-η g)` and renormalizes.

Policies here are stored as softmax scores: multiplying a strictly positive policy by `exp (-η g)`
and renormalizing is adding `-η g` to its scores, so `ppoClipScores` is their algorithm, and every
strictly positive initial policy has scores. The batch at iteration `t` is `D t : S → Option A`,
at most one action per state, which is their Assumption 3. Advantages are exact, as in their
tabular setting.

`ppoClip_tendsto_optimal` is their Theorem 1: with rewards in `[0, 1]`, `η > 0`, `ε > 0`, and
every state-action pair in infinitely many batches (their Assumption 2), the values converge at
every state to a limit that is at least the value of every stationary policy. The proof follows
theirs: each iteration improves every state (Lemma 12); if an action kept a positive limiting
advantage, the probability of the actions with negative limiting advantage would tend to zero
(Lemma 13) and also stay above a positive constant infinitely often (Lemma 14).
`ppoClip_tendsto_optimal_ae` is the almost-sure form for random batches; the argument is
pathwise. Their Lemma 12 claims strict improvement, which fails at states without batch pairs;
the proof needs only improvement.
-/

@[expose] public section

noncomputable section

namespace Rlib

namespace MDP

variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty A] [DecidableEq S] [DecidableEq A]

/-- One mirror-descent step on the PPO-Clip hinge loss with batch `D`, old scores `θold`,
advantages `Adv`, step `η`, and clip range `ε`, applied to the current scores `ψ`. -/
def clipEMDAStep (η ε : ℝ) (θold Adv : S → A → ℝ) (D : S → Option A) (ψ : S → A → ℝ) :
    S → A → ℝ :=
  fun s a => if D s = some a then
      ψ s a + (if ((softmaxPolicy ψ s a).toReal / (softmaxPolicy θold s a).toReal - 1) *
          Real.sign (Adv s a) < ε
        then η * Real.sign (Adv s a) / (softmaxPolicy θold s a).toReal else 0)
    else ψ s a

/-- `k` mirror-descent steps on the PPO-Clip hinge loss, starting from the old scores. -/
def clipInner (η ε : ℝ) (θold Adv : S → A → ℝ) (D : S → Option A) : ℕ → S → A → ℝ
  | 0 => θold
  | k + 1 => clipEMDAStep η ε θold Adv D (clipInner η ε θold Adv D k)

/-- The scores of tabular PPO-Clip: iteration `t` runs `K t` mirror-descent steps on the batch
`D t` with the exact advantages of the current policy. -/
def ppoClipScores (m : MDP S A) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (η ε : ℝ) (K : ℕ → ℕ)
    (D : ℕ → S → Option A) (θ₀ : S → A → ℝ) : ℕ → S → A → ℝ
  | 0 => θ₀
  | t + 1 => clipInner η ε (m.ppoClipScores hγ0 hγ1 η ε K D θ₀ t)
      (m.advantage (softmaxPolicy (m.ppoClipScores hγ0 hγ1 η ε K D θ₀ t)) hγ0 hγ1) (D t) (K t)

omit [Fintype S] [DecidableEq S] [DecidableEq A] in
/-- Softmax probabilities are positive. -/
theorem softmaxPolicy_toReal_pos (θ : S → A → ℝ) (s : S) (a : A) :
    0 < (softmaxPolicy θ s a).toReal :=
  ENNReal.toReal_pos (softmaxPolicy_ne_zero θ s a) ((softmaxPolicy θ s).apply_ne_top a)

omit [Fintype S] [DecidableEq S] [DecidableEq A] in
/-- Softmax probabilities are at most one. -/
theorem softmaxPolicy_toReal_le_one (θ : S → A → ℝ) (s : S) (a : A) :
    (softmaxPolicy θ s a).toReal ≤ 1 := by
  rw [← probability_sum (softmaxPolicy θ s)]
  exact Finset.single_le_sum (fun b _ => ENNReal.toReal_nonneg) (Finset.mem_univ a)

omit [Fintype S] [DecidableEq S] in
/-- **The shape of the mirror-descent iterates.** Scores off the batch never move. The score of
the batch action moves by `c * sign (A s b)` with `c ≥ 0`, and after at least one step
`c ≥ η / π (b | s)`, because the first step is never clipped. -/
theorem clipInner_spec {η ε : ℝ} (hη : 0 ≤ η) (hε : 0 < ε) (θold Adv : S → A → ℝ)
    (D : S → Option A) (k : ℕ) :
    (∀ s a, D s ≠ some a → clipInner η ε θold Adv D k s a = θold s a) ∧
      ∀ s b, D s = some b → ∃ c, 0 ≤ c ∧
        clipInner η ε θold Adv D k s b = θold s b + c * Real.sign (Adv s b) ∧
        (1 ≤ k → η / (softmaxPolicy θold s b).toReal ≤ c) := by
  induction k with
  | zero =>
    refine ⟨fun s a _ => rfl, fun s b _ => ⟨0, le_rfl, by simp [clipInner], by omega⟩⟩
  | succ k ih =>
    obtain ⟨ih1, ih2⟩ := ih
    refine ⟨fun s a h => ?_, fun s b h => ?_⟩
    · simp only [clipInner, clipEMDAStep, h, ↓reduceIte]
      exact ih1 s a h
    · obtain ⟨c, hc0, hc, hck⟩ := ih2 s b h
      have hp := softmaxPolicy_toReal_pos θold s b
      have hstep : η / (softmaxPolicy θold s b).toReal ≥ 0 := div_nonneg hη hp.le
      simp only [clipInner, clipEMDAStep, h, ↓reduceIte]
      split_ifs with hact
      · refine ⟨c + η / (softmaxPolicy θold s b).toReal, by linarith, ?_, fun _ => by linarith⟩
        rw [hc]
        ring
      · refine ⟨c, hc0, by rw [hc, add_zero], fun _ => ?_⟩
        rcases Nat.eq_zero_or_pos k with rfl | hk
        · exfalso
          apply hact
          simp only [clipInner, div_self hp.ne', sub_self, zero_mul]
          exact hε
        · exact hck hk

omit [Fintype S] [DecidableEq S] [DecidableEq A] in
/-- **Sign-aligned score changes do not hurt.** If the advantages average to zero under the
softmax policy of `θ` and every score change has the sign of the advantage, the advantages
average to at least zero under the new softmax policy. -/
theorem expect_softmaxPolicy_nonneg_of_sign (θ θ' Adv : S → A → ℝ) (s : S)
    (h0 : expect (softmaxPolicy θ s) (Adv s) = 0)
    (h : ∀ a, 0 ≤ (θ' s a - θ s a) * Adv s a) :
    0 ≤ expect (softmaxPolicy θ' s) (Adv s) := by
  set g : S → A → ℝ := fun s a => θ' s a - θ s a
  have e : (fun s a => θ s a + g s a / 1) = θ' := by
    funext s a; simp only [g, div_one]; ring
  have hr := softmaxPolicy_add_div θ g 1 s
  rw [e] at hr
  have hZ := sum_softmaxPolicy_mul_exp_pos θ g 1 s
  set Z := ∑ b, (softmaxPolicy θ s b).toReal * Real.exp (g s b / 1)
  have hterm (a : A) : 0 ≤ (softmaxPolicy θ s a).toReal * (Real.exp (g s a / 1) - 1) * Adv s a := by
    have hp := softmaxPolicy_toReal_pos θ s a
    have ha := h a
    rw [div_one]
    rcases lt_trichotomy (Adv s a) 0 with hA | hA | hA
    · have : g s a ≤ 0 := by
        by_contra hg; push Not at hg; nlinarith
      have := Real.exp_le_one_iff.mpr this
      nlinarith [mul_nonneg hp.le (sub_nonneg.mpr this)]
    · simp [hA]
    · have : 0 ≤ g s a := by
        by_contra hg; push Not at hg; nlinarith
      have := Real.one_le_exp_iff.mpr this
      nlinarith [mul_nonneg hp.le (sub_nonneg.mpr this)]
  have hsum : expect (softmaxPolicy θ' s) (Adv s) =
      (expect (softmaxPolicy θ s) (Adv s) +
        ∑ a, (softmaxPolicy θ s a).toReal * (Real.exp (g s a / 1) - 1) * Adv s a) / Z := by
    simp only [expect, hr, ← Finset.sum_add_distrib, Finset.sum_div]
    exact Finset.sum_congr rfl fun a _ => by ring
  rw [hsum, h0, zero_add]
  exact div_nonneg (Finset.sum_nonneg fun a _ => hterm a) hZ.le

variable (m : MDP S A) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)

omit [DecidableEq S] in
/-- One PPO-Clip iteration moves scores only at batch actions, by `c * sign (A s b)` with
`c ≥ 0`, and by at least `η / π_t (b | s)` when `K t ≥ 1`. -/
theorem ppoClipScores_succ_spec {η ε : ℝ} (hη : 0 ≤ η) (hε : 0 < ε) (K : ℕ → ℕ)
    (D : ℕ → S → Option A) (θ₀ : S → A → ℝ) (t : ℕ) :
    let θ := m.ppoClipScores hγ0 hγ1 η ε K D θ₀
    (∀ s a, D t s ≠ some a → θ (t + 1) s a = θ t s a) ∧
      ∀ s b, D t s = some b → ∃ c, 0 ≤ c ∧
        θ (t + 1) s b = θ t s b + c *
          Real.sign (m.advantage (softmaxPolicy (θ t)) hγ0 hγ1 s b) ∧
        (1 ≤ K t → η / (softmaxPolicy (θ t) s b).toReal ≤ c) :=
  clipInner_spec hη hε _ _ _ _

omit [DecidableEq S] in
/-- **State-wise improvement (Huang et al., Lemma 12).** Each PPO-Clip iteration has
nonnegative expected advantage of the previous policy at every state, so it improves the value
at every state. -/
theorem policyValue_ppoClip_le_succ {η ε : ℝ} (hη : 0 ≤ η) (hε : 0 < ε) (K : ℕ → ℕ)
    (D : ℕ → S → Option A) (θ₀ : S → A → ℝ) (t : ℕ) (s : S) :
    m.policyValue (softmaxPolicy (m.ppoClipScores hγ0 hγ1 η ε K D θ₀ t)) hγ0 hγ1 s ≤
      m.policyValue (softmaxPolicy (m.ppoClipScores hγ0 hγ1 η ε K D θ₀ (t + 1))) hγ0 hγ1 s := by
  obtain ⟨h1, h2⟩ := m.ppoClipScores_succ_spec hγ0 hγ1 hη hε K D θ₀ t
  refine m.policyValue_le_of_expect_advantage_nonneg _ _ hγ0 hγ1 (fun s => ?_) s
  refine expect_softmaxPolicy_nonneg_of_sign _ _ _ s (m.expect_advantage _ hγ0 hγ1 s)
    fun a => ?_
  by_cases ha : D t s = some a
  · obtain ⟨c, hc0, hc, -⟩ := h2 s a ha
    rw [hc, add_sub_cancel_left, mul_assoc]
    exact mul_nonneg hc0 (Real.sign_mul_nonneg _)
  · rw [h1 s a ha, sub_self, zero_mul]

/-- The limit of the values of the PPO-Clip iterates. -/
def ppoClipLimitValue (η ε : ℝ) (K : ℕ → ℕ) (D : ℕ → S → Option A) (θ₀ : S → A → ℝ) (s : S) :
    ℝ :=
  ⨆ t, m.policyValue (softmaxPolicy (m.ppoClipScores hγ0 hγ1 η ε K D θ₀ t)) hγ0 hγ1 s

omit [DecidableEq S] in
/-- **The values converge.** With rewards in `[0, 1]`, the values of the PPO-Clip iterates
converge at every state. -/
theorem tendsto_policyValue_ppoClip (hr : ∀ s a, m.reward s a ∈ Set.Icc (0 : ℝ) 1) {η ε : ℝ}
    (hη : 0 ≤ η) (hε : 0 < ε) (K : ℕ → ℕ) (D : ℕ → S → Option A) (θ₀ : S → A → ℝ) (s : S) :
    Filter.Tendsto
      (fun t => m.policyValue (softmaxPolicy (m.ppoClipScores hγ0 hγ1 η ε K D θ₀ t)) hγ0 hγ1 s)
      Filter.atTop (nhds (m.ppoClipLimitValue hγ0 hγ1 η ε K D θ₀ s)) :=
  tendsto_atTop_ciSup
    (monotone_nat_of_le_succ fun t => m.policyValue_ppoClip_le_succ hγ0 hγ1 hη hε K D θ₀ t s)
    ⟨1 / (1 - γ), by
      rintro _ ⟨t, rfl⟩
      exact (m.policyValue_mem_Icc _ hγ0 hγ1 hr s).2⟩

omit [DecidableEq S] in
/-- **The advantages converge** to `r s a + γ * E [V∞] - V∞ s`. -/
theorem tendsto_advantage_ppoClip (hr : ∀ s a, m.reward s a ∈ Set.Icc (0 : ℝ) 1) {η ε : ℝ}
    (hη : 0 ≤ η) (hε : 0 < ε) (K : ℕ → ℕ) (D : ℕ → S → Option A) (θ₀ : S → A → ℝ) (s : S)
    (a : A) :
    Filter.Tendsto
      (fun t => m.advantage (softmaxPolicy (m.ppoClipScores hγ0 hγ1 η ε K D θ₀ t)) hγ0 hγ1 s a)
      Filter.atTop (nhds (m.oneStepActionValue γ (m.ppoClipLimitValue hγ0 hγ1 η ε K D θ₀) s a -
        m.ppoClipLimitValue hγ0 hγ1 η ε K D θ₀ s)) := by
  have hV (s' : S) := m.tendsto_policyValue_ppoClip hγ0 hγ1 hr hη hε K D θ₀ s'
  simp only [advantage, policyActionValue, oneStepActionValue, expect]
  refine Filter.Tendsto.sub (Filter.Tendsto.const_add _ (Filter.Tendsto.const_mul _ ?_)) (hV s)
  exact tendsto_finsetSum _ fun s' _ => (hV s').const_mul _

/-- `z * exp (η / z) ≥ e * η` for `z > 0`. -/
theorem mul_exp_div_ge {η z : ℝ} (hz : 0 < z) : Real.exp 1 * η ≤ z * Real.exp (η / z) := by
  have h := Real.add_one_le_exp (η / z - 1)
  rw [Real.exp_sub] at h
  have he := Real.exp_pos 1
  rw [sub_add_cancel, le_div_iff₀ he] at h
  have : z * (η / z) = η := by field_simp
  nlinarith

omit [Fintype S] [DecidableEq S] in
/-- **The batch action gains mass (Huang et al., (159)-(162)).** If only the score of `b` moves,
by at least `η / π (b | s)`, the new probability of `b` is at least `e η / (e η + 1)`. -/
theorem softmaxPolicy_ge_chi {η : ℝ} (hη : 0 ≤ η) (θ θ' : S → A → ℝ) (s : S) (b : A)
    (hother : ∀ a, a ≠ b → θ' s a = θ s a)
    (hb : η / (softmaxPolicy θ s b).toReal ≤ θ' s b - θ s b) :
    Real.exp 1 * η / (Real.exp 1 * η + 1) ≤ (softmaxPolicy θ' s b).toReal := by
  set g : S → A → ℝ := fun s a => θ' s a - θ s a
  have e : (fun s a => θ s a + g s a / 1) = θ' := by
    funext s a; simp only [g, div_one]; ring
  have hr := softmaxPolicy_add_div θ g 1 s b
  rw [e] at hr
  set p := (softmaxPolicy θ s b).toReal
  have hp := softmaxPolicy_toReal_pos θ s b
  have hp1 := softmaxPolicy_toReal_le_one θ s b
  set c := g s b
  have hexp (a : A) : Real.exp (g s a / 1) = 1 + if a = b then Real.exp c - 1 else 0 := by
    by_cases hab : a = b
    · subst hab; simp [c]
    · simp only [g, hother a hab, sub_self, zero_div, Real.exp_zero, hab, ↓reduceIte, add_zero]
  have hZ :
      ∑ a, (softmaxPolicy θ s a).toReal * Real.exp (g s a / 1) = 1 + p * (Real.exp c - 1) := by
    simp only [hexp, mul_add, mul_one, Finset.sum_add_distrib, probability_sum, mul_ite, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    rfl
  rw [hr, hZ, div_one]
  set x := p * Real.exp c
  have hc : η / p ≤ c := hb
  have hx : Real.exp 1 * η ≤ x :=
    (mul_exp_div_ge hp).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hc) hp.le)
  have he : 0 ≤ Real.exp 1 * η := mul_nonneg (Real.exp_pos 1).le hη
  have hx0 : 0 < x := mul_pos hp (Real.exp_pos c)
  have hden : 0 < 1 + p * (Real.exp c - 1) := by nlinarith
  rw [div_le_div_iff₀ (by linarith) hden]
  nlinarith

omit [DecidableEq S] in
/-- **No action keeps a positive limiting advantage (Huang et al., Lemmas 13 and 14 and
Theorem 1).** With rewards in `[0, 1]`, `η > 0`, `ε > 0`, `K t ≥ 1`, and every state-action pair
in infinitely many batches, every limiting advantage is at most zero. -/
theorem ppoClip_limit_advantage_nonpos (hr : ∀ s a, m.reward s a ∈ Set.Icc (0 : ℝ) 1)
    {η ε : ℝ} (hη : 0 < η) (hε : 0 < ε) (K : ℕ → ℕ) (hK : ∀ t, 1 ≤ K t)
    (D : ℕ → S → Option A) (hD : ∀ s a N, ∃ t ≥ N, D t s = some a) (θ₀ : S → A → ℝ) (s : S)
    (a' : A) :
    m.oneStepActionValue γ (m.ppoClipLimitValue hγ0 hγ1 η ε K D θ₀) s a' -
      m.ppoClipLimitValue hγ0 hγ1 η ε K D θ₀ s ≤ 0 := by
  set θ := m.ppoClipScores hγ0 hγ1 η ε K D θ₀
  set Vinf := m.ppoClipLimitValue hγ0 hγ1 η ε K D θ₀
  set Adv : ℕ → A → ℝ := fun t a => m.advantage (softmaxPolicy (θ t)) hγ0 hγ1 s a
  set Lim : A → ℝ := fun a => m.oneStepActionValue γ Vinf s a - Vinf s
  have hlim (a : A) : Filter.Tendsto (fun t => Adv t a) Filter.atTop (nhds (Lim a)) :=
    m.tendsto_advantage_ppoClip hγ0 hγ1 hr hη.le hε K D θ₀ s a
  by_contra hpos
  push Not at hpos
  set L := Lim a'
  have hγ : 0 < 1 - γ := sub_pos.mpr hγ1
  set χ := Real.exp 1 * η / (Real.exp 1 * η + 1)
  have hχ : 0 < χ := div_pos (mul_pos (Real.exp_pos 1) hη) (by positivity)
  -- Eventually, every advantage is close to its limit in the needed way.
  have hev (a : A) : ∀ᶠ t in Filter.atTop, (0 < Lim a → 0 ≤ Adv t a) ∧
      (Lim a = 0 → |Adv t a| ≤ χ * L / 4) ∧ (Lim a < 0 → Adv t a < 0) := by
    rcases lt_trichotomy (Lim a) 0 with h | h | h
    · filter_upwards [(hlim a).eventually (gt_mem_nhds h)] with t ht
      exact ⟨fun h' => absurd h' (by linarith), fun h' => absurd h' h.ne, fun _ => ht⟩
    · have hball : ∀ᶠ t in Filter.atTop, |Adv t a - Lim a| < χ * L / 4 :=
        Metric.tendsto_nhds.mp (hlim a) _ (by positivity)
      filter_upwards [hball] with t ht
      rw [h, sub_zero] at ht
      exact ⟨fun h' => absurd h h'.ne', fun _ => ht.le, fun h' => absurd h h'.ne⟩
    · filter_upwards [(hlim a).eventually (lt_mem_nhds h)] with t ht
      exact ⟨fun _ => ht.le, fun h' => absurd h' h.ne', fun h' => absurd h' (by linarith)⟩
  have hev' : ∀ᶠ t in Filter.atTop, 3 * L / 4 ≤ Adv t a' :=
    ((hlim a').eventually (lt_mem_nhds (by linarith : 3 * L / 4 < L))).mono fun _ h => h.le
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp (hev'.and (Filter.eventually_all.mpr hev))
  have hspec (t : ℕ) : (∀ s a, D t s ≠ some a → θ (t + 1) s a = θ t s a) ∧
      ∀ s b, D t s = some b → ∃ c, 0 ≤ c ∧
        θ (t + 1) s b = θ t s b + c * Real.sign (m.advantage (softmaxPolicy (θ t)) hγ0 hγ1 s b) ∧
        (1 ≤ K t → η / (softmaxPolicy (θ t) s b).toReal ≤ c) :=
    m.ppoClipScores_succ_spec hγ0 hγ1 hη.le hε K D θ₀ t
  set Ineg := Finset.univ.filter fun a => Lim a < 0
  have ha'neg : a' ∉ Ineg := by simp [Ineg]; linarith
  -- Lemma 13: the actions with negative limiting advantage lose all their probability.
  have hneg0 : Filter.Tendsto (fun t => ∑ a ∈ Ineg, (softmaxPolicy (θ t) s a).toReal)
      Filter.atTop (nhds 0) := by
    rw [show (0 : ℝ) = ∑ a ∈ Ineg, (0 : ℝ) by simp]
    refine tendsto_finsetSum _ fun a'' ha'' => ?_
    have hneg : Lim a'' < 0 := (Finset.mem_filter.mp ha'').2
    have hne : a'' ≠ a' := fun h => ha'neg (h ▸ ha'')
    set ℓ : ℕ → ℝ := fun t => θ t s a'' - θ t s a'
    have hdec (t : ℕ) (ht : T ≤ t) : ℓ (t + 1) ≤ ℓ t ∧ (D t s = some a' → ℓ (t + 1) ≤ ℓ t - η) := by
      obtain ⟨h1, h2⟩ := hspec t
      obtain ⟨hA', hall⟩ := hT t ht
      have hA'pos : 0 < Adv t a' := by linarith
      have hA''neg : Adv t a'' < 0 := (hall a'').2.2 hneg
      have hd'' : θ (t + 1) s a'' ≤ θ t s a'' := by
        by_cases h : D t s = some a''
        · obtain ⟨c, hc0, hc, -⟩ := h2 s a'' h
          change _ = _ + c * Real.sign (Adv t a'') at hc
          rw [hc, Real.sign_of_neg hA''neg]
          linarith
        · rw [h1 s a'' h]
      have hd' : θ t s a' ≤ θ (t + 1) s a' ∧
          (D t s = some a' → θ t s a' + η ≤ θ (t + 1) s a') := by
        by_cases h : D t s = some a'
        · obtain ⟨c, hc0, hc, hck⟩ := h2 s a' h
          change _ = _ + c * Real.sign (Adv t a') at hc
          have hpc := hck (hK t)
          have hp := softmaxPolicy_toReal_pos (θ t) s a'
          have hp1 := softmaxPolicy_toReal_le_one (θ t) s a'
          have : η ≤ η / (softmaxPolicy (θ t) s a').toReal := by
            rw [le_div_iff₀ hp]; nlinarith
          rw [hc, Real.sign_of_pos hA'pos, mul_one]
          exact ⟨by linarith, fun _ => by linarith⟩
        · rw [h1 s a' h]
          exact ⟨le_rfl, fun h' => absurd h' h⟩
      exact ⟨by simp only [ℓ]; linarith [hd'.1], fun h => by simp only [ℓ]; linarith [hd'.2 h]⟩
    have hmono (t₁ : ℕ) (ht₁ : T ≤ t₁) (t : ℕ) (ht : t₁ ≤ t) : ℓ t ≤ ℓ t₁ := by
      induction t, ht using Nat.le_induction with
      | base => exact le_rfl
      | succ t ht ih => exact (hdec t (ht₁.trans ht)).1.trans ih
    have hdrop (n : ℕ) : ∃ N, ∀ t ≥ N, ℓ t ≤ ℓ T - n * η := by
      induction n with
      | zero => exact ⟨T, fun t ht => by simpa using hmono T le_rfl t ht⟩
      | succ n ih =>
        obtain ⟨N, hN⟩ := ih
        obtain ⟨t₀, ht₀, hDt₀⟩ := hD s a' (max N T)
        refine ⟨t₀ + 1, fun t ht => ?_⟩
        have h1 := hmono (t₀ + 1) (by omega) t ht
        have h2 := (hdec t₀ (le_of_max_le_right ht₀)).2 hDt₀
        have h3 := hN t₀ (le_of_max_le_left ht₀)
        push_cast
        linarith
    have hbot : Filter.Tendsto ℓ Filter.atTop Filter.atBot := by
      refine Filter.tendsto_atBot.mpr fun B => ?_
      obtain ⟨n, hn⟩ := exists_nat_gt ((ℓ T - B) / η)
      obtain ⟨N, hN⟩ := hdrop n
      refine Filter.eventually_atTop.mpr ⟨N, fun t ht => ?_⟩
      have := hN t ht
      rw [div_lt_iff₀ hη] at hn
      linarith
    have hle (t : ℕ) : (softmaxPolicy (θ t) s a'').toReal ≤ Real.exp (ℓ t) := by
      rw [softmaxPolicy_apply, div_le_iff₀ (Finset.sum_pos (fun b _ => Real.exp_pos _)
        Finset.univ_nonempty)]
      calc Real.exp (θ t s a'') = Real.exp (ℓ t) * Real.exp (θ t s a') := by
            rw [← Real.exp_add]; simp only [ℓ]; ring_nf
        _ ≤ Real.exp (ℓ t) * ∑ b, Real.exp (θ t s b) :=
            mul_le_mul_of_nonneg_left (Finset.single_le_sum (fun b _ => (Real.exp_pos _).le)
              (Finset.mem_univ a')) (Real.exp_pos _).le
    exact squeeze_zero (fun t => ENNReal.toReal_nonneg) hle
      (Real.tendsto_exp_atBot.comp hbot)
  -- Lemma 14: right after `a'` is in the batch, those actions keep a fixed share.
  set c₀ := χ * L * (1 - γ) / 2
  have hc₀ : 0 < c₀ := by positivity
  have hfreq (N : ℕ) : ∃ t ≥ N, c₀ ≤ ∑ a ∈ Ineg, (softmaxPolicy (θ t) s a).toReal := by
    obtain ⟨t₀, ht₀, hDt₀⟩ := hD s a' (max N T)
    refine ⟨t₀ + 1, by omega, ?_⟩
    obtain ⟨h1, h2⟩ := hspec t₀
    obtain ⟨hA'0, -⟩ := hT t₀ (le_of_max_le_right ht₀)
    obtain ⟨hA'1, hall⟩ := hT (t₀ + 1) (by omega)
    -- The probability of `a'` is at least `χ`.
    have hχle : χ ≤ (softmaxPolicy (θ (t₀ + 1)) s a').toReal := by
      obtain ⟨c, hc0, hc, hck⟩ := h2 s a' hDt₀
      change _ = _ + c * Real.sign (Adv t₀ a') at hc
      rw [Real.sign_of_pos (by linarith), mul_one] at hc
      refine softmaxPolicy_ge_chi hη.le (θ t₀) (θ (t₀ + 1)) s a' (fun a ha => ?_) ?_
      · exact h1 s a (fun h => ha (Option.some_injective _ (h.symm.trans hDt₀)))
      · rw [hc, add_sub_cancel_left]; exact hck (hK t₀)
    set π := softmaxPolicy (θ (t₀ + 1)) s
    have hsum0 : ∑ a, (π a).toReal * Adv (t₀ + 1) a = 0 :=
      m.expect_advantage (softmaxPolicy (θ (t₀ + 1))) hγ0 hγ1 s
    have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ (fun a => Lim a < 0)
      (fun a => (π a).toReal * Adv (t₀ + 1) a)
    rw [hsum0] at hsplit
    -- The actions outside `Ineg` contribute at least `χ L / 2`.
    have hpos : χ * L / 2 ≤ ∑ a ∈ Finset.univ.filter (fun a => ¬ Lim a < 0),
        (π a).toReal * Adv (t₀ + 1) a := by
      set f : A → ℝ := fun a => (π a).toReal * Adv (t₀ + 1) a + (π a).toReal * (χ * L / 4)
      have hf (a : A) (ha : a ∈ Finset.univ.filter (fun a => ¬ Lim a < 0)) : 0 ≤ f a := by
        have hnn : 0 ≤ Lim a := not_lt.mp (Finset.mem_filter.mp ha).2
        have hp := (softmaxPolicy_toReal_pos (θ (t₀ + 1)) s a).le
        rcases hnn.lt_or_eq with h | h
        · have := (hall a).1 h
          have : 0 ≤ (π a).toReal * (χ * L / 4) := mul_nonneg hp (by positivity)
          simp only [f]; nlinarith
        · have := abs_le.mp ((hall a).2.1 h.symm)
          simp only [f]; nlinarith
      have hfa' : χ * (3 * L / 4) ≤ f a' := by
        have hp := (softmaxPolicy_toReal_pos (θ (t₀ + 1)) s a').le
        have : 0 ≤ (π a').toReal * (χ * L / 4) := mul_nonneg hp (by positivity)
        simp only [f]
        nlinarith [mul_le_mul hχle hA'1 (by positivity) hp]
      have hmem : a' ∈ Finset.univ.filter (fun a => ¬ Lim a < 0) := by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt]; exact hpos.le
      have hsingle := Finset.single_le_sum hf hmem
      have hpsum : ∑ a ∈ Finset.univ.filter (fun a => ¬ Lim a < 0), (π a).toReal ≤ 1 := by
        rw [← probability_sum π]
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          fun a _ _ => ENNReal.toReal_nonneg
      have hfsum : ∑ a ∈ Finset.univ.filter (fun a => ¬ Lim a < 0), f a =
          ∑ a ∈ Finset.univ.filter (fun a => ¬ Lim a < 0), (π a).toReal * Adv (t₀ + 1) a +
            (∑ a ∈ Finset.univ.filter (fun a => ¬ Lim a < 0), (π a).toReal) * (χ * L / 4) := by
        simp only [f, Finset.sum_add_distrib, Finset.sum_mul]
      have : 0 ≤ χ * L / 4 := by positivity
      nlinarith
    -- So the actions in `Ineg` carry at least `χ L / 2` of negative advantage.
    have hneg : ∑ a ∈ Ineg, (π a).toReal * Adv (t₀ + 1) a ≤ -(χ * L / 2) := by
      change ∑ a ∈ Finset.univ.filter (fun a => Lim a < 0), _ ≤ _
      linarith
    have hlow : -(1 / (1 - γ)) * ∑ a ∈ Ineg, (π a).toReal ≤
        ∑ a ∈ Ineg, (π a).toReal * Adv (t₀ + 1) a := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun a _ => ?_
      have := (abs_le.mp (m.abs_advantage_le (softmaxPolicy (θ (t₀ + 1))) hγ0 hγ1 hr s a)).1
      have hp := (softmaxPolicy_toReal_pos (θ (t₀ + 1)) s a).le
      nlinarith
    have : χ * L / 2 ≤ 1 / (1 - γ) * ∑ a ∈ Ineg, (π a).toReal := by linarith
    have h2 : (1 - γ) * (χ * L / 2) ≤ ∑ a ∈ Ineg, (π a).toReal := by
      calc (1 - γ) * (χ * L / 2) ≤ (1 - γ) * (1 / (1 - γ) * ∑ a ∈ Ineg, (π a).toReal) :=
            mul_le_mul_of_nonneg_left this hγ.le
        _ = ∑ a ∈ Ineg, (π a).toReal := by field_simp
    simp only [c₀]
    linarith
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hneg0.eventually (gt_mem_nhds hc₀))
  obtain ⟨t, ht, hct⟩ := hfreq N
  exact absurd (hN t ht) (not_lt.mpr hct)

omit [DecidableEq S] in
/-- **Global convergence of tabular PPO-Clip (Huang et al., Theorem 1).** With rewards in
`[0, 1]`, step `η > 0`, clip range `ε > 0`, at least one mirror-descent step per iteration, any
initial scores, and every state-action pair in infinitely many batches, the values of the
PPO-Clip iterates converge at every state to a limit that is at least the value of every
stationary policy. -/
theorem ppoClip_tendsto_optimal (hr : ∀ s a, m.reward s a ∈ Set.Icc (0 : ℝ) 1) {η ε : ℝ}
    (hη : 0 < η) (hε : 0 < ε) (K : ℕ → ℕ) (hK : ∀ t, 1 ≤ K t) (D : ℕ → S → Option A)
    (hD : ∀ s a N, ∃ t ≥ N, D t s = some a) (θ₀ : S → A → ℝ) :
    ∃ V : S → ℝ, (∀ s, Filter.Tendsto
        (fun t => m.policyValue (softmaxPolicy (m.ppoClipScores hγ0 hγ1 η ε K D θ₀ t)) hγ0 hγ1 s)
        Filter.atTop (nhds (V s))) ∧
      ∀ (π : StationaryPolicy S A) s, m.policyValue π hγ0 hγ1 s ≤ V s :=
  ⟨m.ppoClipLimitValue hγ0 hγ1 η ε K D θ₀,
    fun s => m.tendsto_policyValue_ppoClip hγ0 hγ1 hr hη.le hε K D θ₀ s,
    fun π s => m.policyValue_le_of_oneStepActionValue_le π hγ0 hγ1 (fun s a => by
      have := m.ppoClip_limit_advantage_nonpos hγ0 hγ1 hr hη hε K hK D hD θ₀ s a
      linarith) s⟩

omit [DecidableEq S] in
/-- **Almost-sure form.** If the batches are random and almost surely contain every
state-action pair infinitely often, then almost surely the PPO-Clip values converge to a limit
that is at least the value of every stationary policy. -/
theorem ppoClip_tendsto_optimal_ae {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    (hr : ∀ s a, m.reward s a ∈ Set.Icc (0 : ℝ) 1) {η ε : ℝ} (hη : 0 < η) (hε : 0 < ε)
    (K : ℕ → ℕ) (hK : ∀ t, 1 ≤ K t) (D : Ω → ℕ → S → Option A)
    (hD : ∀ᵐ ω ∂μ, ∀ s a N, ∃ t ≥ N, D ω t s = some a) (θ₀ : S → A → ℝ) :
    ∀ᵐ ω ∂μ, ∃ V : S → ℝ, (∀ s, Filter.Tendsto
        (fun t => m.policyValue (softmaxPolicy (m.ppoClipScores hγ0 hγ1 η ε K (D ω) θ₀ t))
          hγ0 hγ1 s) Filter.atTop (nhds (V s))) ∧
      ∀ (π : StationaryPolicy S A) s, m.policyValue π hγ0 hγ1 s ≤ V s := by
  filter_upwards [hD] with ω hω
  exact m.ppoClip_tendsto_optimal hγ0 hγ1 hr hη hε K hK (D ω) hω θ₀

end MDP

end Rlib
