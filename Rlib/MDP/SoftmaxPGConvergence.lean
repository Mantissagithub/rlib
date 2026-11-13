module

public import Rlib.MDP.SoftmaxPGAsymptotic
public import Rlib.MDP.PolicyImprovement

/-! # Global convergence of exact softmax policy gradient

This file completes the proof of Agarwal, Kakade, Lee, and Mahajan, *On the Theory of Policy
Gradient Methods* (JMLR 2021), Theorem 10: with rewards in `[0, 1]`, a start distribution `μ`
with `μ s > 0` for every state, and a step `0 < η ≤ (1 - γ) ^ 3 / 8`, exact softmax policy
gradient converges to optimal values. In the limit no action has positive advantage
(`advantage_limit_nonpos_pg`), so the limit of the values satisfies the Bellman optimality
equation and dominates the value of every stationary policy.
-/

@[expose] public section

noncomputable section

namespace Rlib.MDP

variable {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [Nonempty A]

/-- The limiting advantage of action `a` at `s`: its action value against the limit of the
values, minus that limit. -/
def pgLimitAdvantage (m : MDP S A) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (μ : S → ℝ) (η : ℝ)
    (θ₁ : S → A → ℝ) (s : S) (a : A) : ℝ :=
  m.oneStepActionValue γ (m.pgLimitValue hγ0 hγ1 μ η θ₁) s a - m.pgLimitValue hγ0 hγ1 μ η θ₁ s

/-- **Probabilities of actions with nonzero limiting advantage vanish (Agarwal et al.,
Lemma C.5).** -/
theorem tendsto_softmaxPolicy_pg_zero (m : MDP S A) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hr : ∀ s a, m.reward s a ∈ Set.Icc (0 : ℝ) 1) {μ : S → ℝ} (hμ : ∀ s, 0 ≤ μ s)
    (hμ1 : ∑ s, μ s = 1) {η : ℝ} (hη0 : 0 < η) (hη : η ≤ (1 - γ) ^ 3 / 8) (θ₁ : S → A → ℝ)
    {s : S} (hs : 0 < μ s) {a : A} (ha : m.pgLimitAdvantage hγ0 hγ1 μ η θ₁ s a ≠ 0) :
    Filter.Tendsto (fun t => (softmaxPolicy (m.pgScores hγ0 hγ1 μ η θ₁ t) s a).toReal)
      Filter.atTop (nhds 0) := by
  have hpA := m.tendsto_mul_advantage_pg hγ0 hγ1 hr hμ hμ1 hη0 hη θ₁ hs a
  have hA := m.tendsto_advantage_pg hγ0 hγ1 hr hμ hη0.le θ₁ s a
  have hdiv := hpA.div hA ha
  rw [zero_div] at hdiv
  refine hdiv.congr' ?_
  filter_upwards [hA.eventually_ne ha] with t ht
  simp only [Pi.div_apply]
  field_simp

omit [Fintype S] [DecidableEq S] in
/-- A larger score gives a larger softmax probability. -/
theorem softmaxPolicy_le_of_le (θ : S → A → ℝ) (s : S) {a b : A} (h : θ s a ≤ θ s b) :
    (softmaxPolicy θ s a).toReal ≤ (softmaxPolicy θ s b).toReal := by
  rw [softmaxPolicy_apply, softmaxPolicy_apply]
  exact div_le_div_of_nonneg_right (Real.exp_le_exp.mpr h)
    (Finset.sum_pos (fun c _ => Real.exp_pos _) Finset.univ_nonempty).le

omit [Fintype S] [DecidableEq S] in
/-- Softmax probabilities compare like the exponentials of the score gaps. -/
theorem softmaxPolicy_le_mul (θ : S → A → ℝ) (s : S) (a b : A) {c : ℝ}
    (h : Real.exp (θ s a) ≤ c * Real.exp (θ s b)) :
    (softmaxPolicy θ s a).toReal ≤ c * (softmaxPolicy θ s b).toReal := by
  rw [softmaxPolicy_apply, softmaxPolicy_apply, mul_div_assoc']
  exact div_le_div_of_nonneg_right h
    (Finset.sum_pos (fun c _ => Real.exp_pos _) Finset.univ_nonempty).le

/-- **No action keeps a positive advantage (Agarwal et al., proof of Theorem 10).** With rewards
in `[0, 1]`, `μ s > 0` for every state, and a step `0 < η ≤ (1 - γ) ^ 3 / 8`, every limiting
advantage is nonpositive. -/
theorem advantage_limit_nonpos_pg (m : MDP S A) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hr : ∀ s a, m.reward s a ∈ Set.Icc (0 : ℝ) 1) {μ : S → ℝ} (hμ : ∀ s, 0 < μ s)
    (hμ1 : ∑ s, μ s = 1) {η : ℝ} (hη0 : 0 < η) (hη : η ≤ (1 - γ) ^ 3 / 8) (θ₁ : S → A → ℝ)
    (s : S) (a₁ : A) : m.pgLimitAdvantage hγ0 hγ1 μ η θ₁ s a₁ ≤ 0 := by
  classical
  have hγ : 0 < 1 - γ := sub_pos.mpr hγ1
  have hμ0 (s : S) : 0 ≤ μ s := (hμ s).le
  set θ := m.pgScores hγ0 hγ1 μ η θ₁
  set π : ℕ → A → ℝ := fun t a => (softmaxPolicy (θ t) s a).toReal
  set Ad : ℕ → A → ℝ := fun t a => m.advantage (softmaxPolicy (θ t)) hγ0 hγ1 s a
  set c : ℕ → ℝ := fun t =>
    η * (1 - γ)⁻¹ * m.weightedVisitation (softmaxPolicy (θ t)) hγ0 hγ1 μ s
  set Ainf : A → ℝ := m.pgLimitAdvantage hγ0 hγ1 μ η θ₁ s
  have hstep (t : ℕ) (a : A) : θ (t + 1) s a = θ t s a + c t * (π t a * Ad t a) :=
    congrFun (congrFun (m.pgScores_succ hγ0 hγ1 μ η θ₁ t) s) a
  have hc (t : ℕ) : 0 ≤ c t := by
    have : 0 ≤ m.weightedVisitation (softmaxPolicy (θ t)) hγ0 hγ1 μ s :=
      Finset.sum_nonneg fun s₀ _ =>
        mul_nonneg (hμ0 s₀) (m.discountedVisitation_nonneg _ hγ0 hγ1 s₀ s)
    have : 0 ≤ (1 - γ)⁻¹ := inv_nonneg.mpr hγ.le
    positivity
  have hπ0 (t : ℕ) (a : A) : 0 ≤ π t a := ENNReal.toReal_nonneg
  have hπpos (t : ℕ) (a : A) : 0 < π t a := by
    simp only [π, softmaxPolicy_apply]
    exact div_pos (Real.exp_pos _) (Finset.sum_pos (fun b _ => Real.exp_pos _)
      Finset.univ_nonempty)
  have hsum1 (t : ℕ) : ∑ a, π t a = 1 := probability_sum _
  have h0 (t : ℕ) : ∑ a, π t a * Ad t a = 0 := m.expect_advantage _ hγ0 hγ1 s
  have hAd (a : A) : Filter.Tendsto (fun t => Ad t a) Filter.atTop (nhds (Ainf a)) :=
    m.tendsto_advantage_pg hγ0 hγ1 hr hμ0 hη0.le θ₁ s a
  have hAb (t : ℕ) (a : A) : |Ad t a| ≤ 1 / (1 - γ) :=
    m.abs_advantage_le _ hγ0 hγ1 hr s a
  have hlim0 {a : A} (ha : Ainf a ≠ 0) : Filter.Tendsto (fun t => π t a) Filter.atTop (nhds 0) :=
    m.tendsto_softmaxPolicy_pg_zero hγ0 hγ1 hr hμ0 hμ1 hη0 hη θ₁ (hμ s) ha
  by_contra hpos
  rw [not_le] at hpos
  set ap := a₁
  set δ := Ainf ap
  set n : ℝ := (Fintype.card A : ℝ)
  have hn : 1 ≤ n := Nat.one_le_cast.mpr Fintype.card_pos
  set ε0 := δ / (8 * n)
  have hε0 : 0 < ε0 := by positivity
  have hε0δ : ε0 ≤ δ / 8 := by
    simp only [ε0]
    exact div_le_div_of_nonneg_left hpos.le (by norm_num) (by linarith)
  set c0 := (1 - γ) * ε0
  have hc0 : 0 < c0 := mul_pos hγ hε0
  -- The advantage of `ap` stays above `δ / 2`, so its score never decreases.
  obtain ⟨T1, hT1⟩ := Filter.eventually_atTop.mp
    ((hAd ap).eventually (lt_mem_nhds (by linarith : δ / 2 < δ)))
  set L := θ T1 s ap
  have hL (k : ℕ) : L ≤ θ (T1 + k) s ap := by
    induction k with
    | zero => simp [L]
    | succ k ih =>
      rw [← add_assoc, hstep]
      have := hT1 (T1 + k) (by omega)
      have : 0 ≤ c (T1 + k) * (π (T1 + k) ap * Ad (T1 + k) ap) :=
        mul_nonneg (hc _) (mul_nonneg (hπ0 _ _) (by linarith))
      linarith
  have hL' (t : ℕ) (ht : T1 ≤ t) : L ≤ θ t s ap := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le ht
    exact hL k
  -- Eventual sign information on the advantages.
  have e2 : ∀ᶠ t in Filter.atTop, ∀ a, Ainf a = 0 → |Ad t a| < ε0 := by
    refine Filter.eventually_all.mpr fun a => ?_
    by_cases ha : Ainf a = 0
    · have h := hAd a
      rw [ha] at h
      filter_upwards [h.eventually (isOpen_Ioo.mem_nhds (show (0 : ℝ) ∈ Set.Ioo (-ε0) ε0 from
        ⟨by linarith, hε0⟩))] with t ht _
      exact abs_lt.mpr ht
    · exact Filter.Eventually.of_forall fun t h => absurd h ha
  have e3 : ∀ᶠ t in Filter.atTop, ∀ a, 0 < Ainf a → 0 < Ad t a := by
    refine Filter.eventually_all.mpr fun a => ?_
    by_cases ha : 0 < Ainf a
    · filter_upwards [(hAd a).eventually (lt_mem_nhds ha)] with t ht _ using ht
    · exact Filter.Eventually.of_forall fun t h => absurd h ha
  -- Scores of actions with negative limiting advantage fall far below that of `ap`.
  have e5 : ∀ᶠ t in Filter.atTop, ∀ a, Ainf a < 0 → θ t s a ≤ L + Real.log c0 := by
    refine Filter.eventually_all.mpr fun a => ?_
    by_cases ha : Ainf a < 0
    · obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp
        ((hAd a).eventually (gt_mem_nhds (by linarith : Ainf a < Ainf a / 2)))
      have hbot := m.tendsto_pgScores_atBot hγ0 hγ1 hr hμ0 hμ1 hη0 θ₁ (hμ s) (a₀ := a)
        (ε := -(Ainf a / 2)) (by linarith) (T := T) fun t ht => by
          have := hT t ht; simp only [Ad] at this; linarith
      filter_upwards [hbot.eventually (Filter.eventually_le_atBot (L + Real.log c0))]
        with t ht _ using ht
    · exact Filter.Eventually.of_forall fun t h => absurd h ha
  -- Persistence (Agarwal et al., Lemma C.8).
  obtain ⟨T2, hT2⟩ := Filter.eventually_atTop.mp (e2.and (Filter.eventually_ge_atTop T1))
  have hpersist (t : ℕ) (ht : T2 ≤ t) (a : A) (ha : Ainf a = 0)
      (hle : θ t s a ≤ θ t s ap) : θ (t + 1) s a ≤ θ (t + 1) s ap := by
    have hAa := (hT2 t ht).1 a ha
    have hAp := hT1 t (hT2 t ht).2
    have hπle : π t a ≤ π t ap := softmaxPolicy_le_of_le (θ t) s hle
    have hprod : π t a * Ad t a ≤ π t ap * Ad t ap := by
      rcases le_or_gt (Ad t a) 0 with h | h
      · nlinarith [hπ0 t a, hπ0 t ap]
      · have : Ad t a ≤ Ad t ap := by linarith [le_abs_self (Ad t a)]
        calc π t a * Ad t a ≤ π t ap * Ad t a := mul_le_mul_of_nonneg_right hπle h.le
          _ ≤ π t ap * Ad t ap := mul_le_mul_of_nonneg_left this (hπ0 t ap)
    rw [hstep, hstep]
    nlinarith [mul_le_mul_of_nonneg_left hprod (hc t)]
  set P : A → Prop := fun a => Ainf a = 0 ∧ ∃ t, T2 ≤ t ∧ θ t s a ≤ θ t s ap
  set Q : A → Prop := fun a => Ainf a = 0 ∧ ∀ t, T2 ≤ t → θ t s ap < θ t s a
  have e6 : ∀ᶠ t in Filter.atTop, ∀ a, P a → θ t s a ≤ θ t s ap := by
    refine Filter.eventually_all.mpr fun a => ?_
    by_cases ha : P a
    · obtain ⟨ha0, t₀, ht₀, hle⟩ := ha
      have hk (k : ℕ) : θ (t₀ + k) s a ≤ θ (t₀ + k) s ap := by
        induction k with
        | zero => simpa using hle
        | succ k ih => exact hpersist (t₀ + k) (by omega) a ha0 ih
      filter_upwards [Filter.eventually_ge_atTop t₀] with t ht _
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le ht
      exact hk k
    · exact Filter.Eventually.of_forall fun t h => absurd h ha
  obtain ⟨T3, hT3⟩ := Filter.eventually_atTop.mp
    ((((e2.and e3).and e5).and e6).and (Filter.eventually_ge_atTop T2))
  -- After `T3`, the actions in `Q` lose probability-weighted advantage in total.
  have hQneg (t : ℕ) (ht : T3 ≤ t) :
      ∑ a ∈ Finset.univ.filter Q, π t a * Ad t a ≤ 0 := by
    obtain ⟨⟨⟨⟨h2, h3⟩, h5⟩, h6⟩, hT2t⟩ := hT3 t ht
    have hT1t : T1 ≤ t := (hT2 T2 le_rfl).2.trans hT2t
    have hAp := hT1 t hT1t
    have hLt := hL' t hT1t
    have hterm (a : A) (ha : ¬ Q a) :
        (if a = ap then π t ap * (δ / 2) else 0) - π t ap * ε0 ≤ π t a * Ad t a := by
      by_cases hap : a = ap
      · simp only [hap, ↓reduceIte]
        have h1 := mul_le_mul_of_nonneg_left hAp.le (hπ0 t ap)
        have h2 := mul_nonneg (hπ0 t ap) hε0.le
        linarith
      · simp only [hap, ↓reduceIte, zero_sub]
        rcases lt_trichotomy (Ainf a) 0 with hneg | hzero | hposa
        · have hθ := h5 a hneg
          have hexp : Real.exp (θ t s a) ≤ c0 * Real.exp (θ t s ap) := by
            calc Real.exp (θ t s a) ≤ Real.exp (L + Real.log c0) := Real.exp_le_exp.mpr hθ
              _ = c0 * Real.exp L := by rw [Real.exp_add, Real.exp_log hc0]; ring
              _ ≤ c0 * Real.exp (θ t s ap) :=
                  mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hLt) hc0.le
          have hπa : π t a ≤ c0 * π t ap := softmaxPolicy_le_mul (θ t) s a ap hexp
          have hA := neg_abs_le (Ad t a)
          have hAb' := hAb t a
          have : -(π t a * (1 / (1 - γ))) ≤ π t a * Ad t a := by
            nlinarith [hπ0 t a]
          have : π t a * (1 / (1 - γ)) ≤ c0 * π t ap * (1 / (1 - γ)) :=
            mul_le_mul_of_nonneg_right hπa (by positivity)
          have hc0e : c0 * π t ap * (1 / (1 - γ)) = π t ap * ε0 := by
            simp only [c0]; field_simp
          linarith
        · have hP : P a := by
            refine ⟨hzero, ?_⟩
            by_contra hnot
            exact ha ⟨hzero, fun t' ht' => lt_of_not_ge fun h => hnot ⟨t', ht', h⟩⟩
          have hle := h6 a hP
          have hπle : π t a ≤ π t ap := softmaxPolicy_le_of_le (θ t) s hle
          have hA := h2 a hzero
          have : -(π t a * ε0) ≤ π t a * Ad t a := by
            nlinarith [hπ0 t a, neg_abs_le (Ad t a)]
          nlinarith [mul_le_mul_of_nonneg_right hπle hε0.le]
        · have := h3 a hposa
          nlinarith [hπ0 t a, hπ0 t ap, mul_pos (hπpos t a) this]
    have hrest : 0 ≤ ∑ a ∈ Finset.univ.filter (fun a => ¬ Q a), π t a * Ad t a := by
      have hap : ap ∈ Finset.univ.filter (fun a => ¬ Q a) := by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rintro ⟨h, _⟩
        exact absurd h hpos.ne'
      calc (0 : ℝ) ≤ π t ap * (δ / 2) - n * (π t ap * ε0) := by
            have : n * ε0 = δ / 8 := by simp only [ε0]; field_simp
            nlinarith [hπ0 t ap]
        _ ≤ π t ap * (δ / 2) - (Finset.univ.filter (fun a => ¬ Q a)).card * (π t ap * ε0) := by
            have : ((Finset.univ.filter (fun a => ¬ Q a)).card : ℝ) ≤ n := by
              have h := Finset.card_filter_le (Finset.univ : Finset A) (fun a => ¬ Q a)
              rw [Finset.card_univ] at h
              simp only [n]
              exact_mod_cast h
            nlinarith [mul_nonneg (hπ0 t ap) hε0.le]
        _ = ∑ a ∈ Finset.univ.filter (fun a => ¬ Q a),
              ((if a = ap then π t ap * (δ / 2) else 0) - π t ap * ε0) := by
            rw [Finset.sum_sub_distrib, Finset.sum_ite_eq']
            simp only [hap, ↓reduceIte, Finset.sum_const, nsmul_eq_mul]
        _ ≤ _ := Finset.sum_le_sum fun a ha => hterm a (Finset.mem_filter.mp ha).2
    have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ Q
      (fun a => π t a * Ad t a)
    rw [h0] at hsplit
    linarith
  -- So the total score over `Q` never increases after `T3`.
  set M0 := ∑ a ∈ Finset.univ.filter Q, θ T3 s a
  have hM (k : ℕ) : ∑ a ∈ Finset.univ.filter Q, θ (T3 + k) s a ≤ M0 := by
    induction k with
    | zero => simp [M0]
    | succ k ih =>
      rw [← add_assoc]
      simp only [hstep, Finset.sum_add_distrib, ← Finset.mul_sum]
      have := mul_nonpos_of_nonneg_of_nonpos (hc (T3 + k)) (hQneg (T3 + k) (by omega))
      linarith
  -- Each action in `Q` sits above `ap`, so its probability is a bounded multiple of `ap`'s.
  have hQbound (a : A) (ha : Q a) : ∀ᶠ t in Filter.atTop,
      π t a ≤ Real.exp (M0 - (((Finset.univ.filter Q).erase a).card : ℝ) * L - L) * π t ap := by
    filter_upwards [Filter.eventually_ge_atTop T3] with t ht
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le ht
    have hT1t : T1 ≤ T3 + k := ((hT2 T2 le_rfl).2.trans (hT3 T3 le_rfl).2).trans (by omega)
    have hT2t : T2 ≤ T3 + k := (hT3 T3 le_rfl).2.trans (by omega)
    have hmem : a ∈ Finset.univ.filter Q := Finset.mem_filter.mpr ⟨Finset.mem_univ a, ha⟩
    have hlowQ (b : A) (hb : b ∈ Finset.univ.filter Q) : L ≤ θ (T3 + k) s b :=
      (hL' _ hT1t).trans ((Finset.mem_filter.mp hb).2.2 _ hT2t).le
    have hsplit := Finset.add_sum_erase (Finset.univ.filter Q) (fun b => θ (T3 + k) s b) hmem
    have hrest := Finset.sum_le_sum fun b (hb : b ∈ (Finset.univ.filter Q).erase a) =>
      hlowQ b (Finset.mem_of_mem_erase hb)
    rw [Finset.sum_const, nsmul_eq_mul] at hrest
    have hθa : θ (T3 + k) s a ≤ M0 - (((Finset.univ.filter Q).erase a).card : ℝ) * L := by
      have := hM k
      linarith
    refine softmaxPolicy_le_mul (θ (T3 + k)) s a ap ?_
    calc Real.exp (θ (T3 + k) s a)
        ≤ Real.exp (M0 - (((Finset.univ.filter Q).erase a).card : ℝ) * L) :=
          Real.exp_le_exp.mpr hθa
      _ = Real.exp (M0 - (((Finset.univ.filter Q).erase a).card : ℝ) * L - L) *
            Real.exp L := by rw [← Real.exp_add]; ring_nf
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (hL' _ hT1t)) (Real.exp_pos _).le
  -- Every probability at `s` tends to zero, which is impossible.
  have hap0 : Filter.Tendsto (fun t => π t ap) Filter.atTop (nhds 0) := hlim0 hpos.ne'
  have hall (a : A) : Filter.Tendsto (fun t => π t a) Filter.atTop (nhds 0) := by
    by_cases ha : Ainf a = 0
    · by_cases hq : Q a
      · have hlim := hap0.const_mul
          (Real.exp (M0 - (((Finset.univ.filter Q).erase a).card : ℝ) * L - L))
        rw [mul_zero] at hlim
        exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
          (Filter.Eventually.of_forall fun t => hπ0 t a) (hQbound a hq)
      · have hP : P a := by
          refine ⟨ha, ?_⟩
          by_contra hnot
          exact hq ⟨ha, fun t' ht' => lt_of_not_ge fun h => hnot ⟨t', ht', h⟩⟩
        refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hap0
          (Filter.Eventually.of_forall fun t => hπ0 t a) ?_
        filter_upwards [e6] with t ht
        exact softmaxPolicy_le_of_le (θ t) s (ht a hP)
    · exact hlim0 ha
  have hsumlim : Filter.Tendsto (fun t => ∑ a, π t a) Filter.atTop (nhds 0) := by
    have := tendsto_finsetSum Finset.univ fun a _ => hall a
    simpa using this
  have hone : Filter.Tendsto (fun t => ∑ a, π t a) Filter.atTop (nhds 1) := by
    simp only [hsum1]
    exact tendsto_const_nhds
  exact one_ne_zero (tendsto_nhds_unique hone hsumlim)

omit [DecidableEq S] [Nonempty A] in
/-- A function that no one-step action value exceeds dominates the value of every stationary
policy, for a discount in `[0, 1)`. -/
theorem policyValue_le_of_oneStepActionValue_le (m : MDP S A) (π : StationaryPolicy S A)
    {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) {v : S → ℝ}
    (hv : ∀ s a, m.oneStepActionValue γ v s a ≤ v s) (s : S) :
    m.policyValue π hγ0 hγ1 s ≤ v s := by
  set V := m.policyValue π hγ0 hγ1
  have : Nonempty S := ⟨s⟩
  obtain ⟨t, ht⟩ := Finite.exists_max fun s => V s - v s
  suffices V t - v t ≤ 0 by linarith [ht s]
  have hfix : m.oneStepValue π γ V t = V t := congrFun (m.oneStepValue_policyValue π hγ0 hγ1) t
  have hvt : expect (π t) (m.oneStepActionValue γ v t) ≤ v t :=
    (expect_mono _ fun a => hv t a).trans (expect_const _ _).le
  have hdiff (a : A) : m.oneStepActionValue γ V t a - m.oneStepActionValue γ v t a ≤
      γ * (V t - v t) := by
    have hE : expect (m.transition t a) V - expect (m.transition t a) v ≤ V t - v t := by
      have h := expect_mono (m.transition t a) (f := fun s' => V s' - v s')
        (g := fun _ => V t - v t) ht
      rw [expect_const] at h
      refine le_trans (le_of_eq ?_) h
      simp only [expect, ← Finset.sum_sub_distrib, ← mul_sub]
    simp only [oneStepActionValue]
    nlinarith [mul_le_mul_of_nonneg_left hE hγ0]
  have hle : expect (π t) (m.oneStepActionValue γ V t) -
      expect (π t) (m.oneStepActionValue γ v t) ≤ γ * (V t - v t) := by
    have h := expect_mono (π t) (f := fun a => m.oneStepActionValue γ V t a -
      m.oneStepActionValue γ v t a) (g := fun _ => γ * (V t - v t)) hdiff
    rw [expect_const] at h
    refine le_trans (le_of_eq ?_) h
    simp only [expect, ← Finset.sum_sub_distrib, ← mul_sub]
  change m.oneStepValue π γ V t = V t at hfix
  simp only [oneStepValue] at hfix
  nlinarith [sub_pos.mpr hγ1]

/-- **Exact softmax policy gradient converges to optimal values (Agarwal et al., Theorem 10).**
With rewards in `[0, 1]`, `μ s > 0` for every state, and a step `0 < η ≤ (1 - γ) ^ 3 / 8`, the
limit of the values of the iterates is at least the value of every stationary policy at every
state. Since the values converge to that limit (`tendsto_policyValue_pg`), they converge to the
optimal values. -/
theorem policyValue_le_pgLimitValue (m : MDP S A) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hr : ∀ s a, m.reward s a ∈ Set.Icc (0 : ℝ) 1) {μ : S → ℝ} (hμ : ∀ s, 0 < μ s)
    (hμ1 : ∑ s, μ s = 1) {η : ℝ} (hη0 : 0 < η) (hη : η ≤ (1 - γ) ^ 3 / 8) (θ₁ : S → A → ℝ)
    (π : StationaryPolicy S A) (s : S) :
    m.policyValue π hγ0 hγ1 s ≤ m.pgLimitValue hγ0 hγ1 μ η θ₁ s :=
  m.policyValue_le_of_oneStepActionValue_le π hγ0 hγ1 (fun s a => by
    have := m.advantage_limit_nonpos_pg hγ0 hγ1 hr hμ hμ1 hη0 hη θ₁ s a
    simp only [pgLimitAdvantage] at this
    linarith) s

/-- **The limit satisfies the Bellman optimality equation.** Under the same conditions, the
limit of the values is a fixed point of the Bellman optimality operator. -/
theorem optimalityOperator_pgLimitValue (m : MDP S A) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hr : ∀ s a, m.reward s a ∈ Set.Icc (0 : ℝ) 1) {μ : S → ℝ} (hμ : ∀ s, 0 < μ s)
    (hμ1 : ∑ s, μ s = 1) {η : ℝ} (hη0 : 0 < η) (hη : η ≤ (1 - γ) ^ 3 / 8)
    (θ₁ : S → A → ℝ) :
    m.optimalityOperator γ (m.pgLimitValue hγ0 hγ1 μ η θ₁) = m.pgLimitValue hγ0 hγ1 μ η θ₁ := by
  set Vinf := m.pgLimitValue hγ0 hγ1 μ η θ₁
  set V : ℕ → S → ℝ := fun t =>
    m.policyValue (softmaxPolicy (m.pgScores hγ0 hγ1 μ η θ₁ t)) hγ0 hγ1
  have hbdd (s : S) : BddAbove (Set.range fun t => V t s) :=
    ⟨1 / (1 - γ), by
      rintro _ ⟨t, rfl⟩
      exact (m.policyValue_mem_Icc _ hγ0 hγ1 hr s).2⟩
  have hVle (t : ℕ) : V t ≤ Vinf := fun s => le_ciSup (hbdd s) t
  funext s
  apply le_antisymm
  · refine Finset.sup'_le _ _ fun a _ => ?_
    have := m.advantage_limit_nonpos_pg hγ0 hγ1 hr hμ hμ1 hη0 hη θ₁ s a
    simp only [pgLimitAdvantage] at this
    linarith
  · refine ciSup_le fun t => ?_
    have hfix := congrFun (m.oneStepValue_policyValue
      (softmaxPolicy (m.pgScores hγ0 hγ1 μ η θ₁ t)) hγ0 hγ1) s
    change m.oneStepValue _ γ (V t) s = V t s at hfix
    change V t s ≤ _
    rw [← hfix]
    calc m.oneStepValue _ γ (V t) s ≤ m.oneStepValue _ γ Vinf s :=
          expect_mono _ fun a => by
            simp only [oneStepActionValue]
            have := expect_mono (m.transition s a) (hVle t)
            nlinarith
      _ ≤ m.optimalityOperator γ Vinf s := m.oneStepValue_le_optimalityOperator _ γ Vinf s

/-- If `b` is an optimal deterministic policy, the limit of the values of exact softmax policy
gradient is the value of `b`. -/
theorem pgLimitValue_eq_policyValue (m : MDP S A) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hr : ∀ s a, m.reward s a ∈ Set.Icc (0 : ℝ) 1) {μ : S → ℝ} (hμ : ∀ s, 0 < μ s)
    (hμ1 : ∑ s, μ s = 1) {η : ℝ} (hη0 : 0 < η) (hη : η ≤ (1 - γ) ^ 3 / 8) (θ₁ : S → A → ℝ)
    (b : S → A) (hb : ∀ (π : StationaryPolicy S A) s,
      m.policyValue π hγ0 hγ1 s ≤ m.policyValue (fun s => PMF.pure (b s)) hγ0 hγ1 s) :
    m.pgLimitValue hγ0 hγ1 μ η θ₁ = m.policyValue (fun s => PMF.pure (b s)) hγ0 hγ1 := by
  funext s
  exact le_antisymm (ciSup_le fun t => hb _ s)
    (m.policyValue_le_pgLimitValue hγ0 hγ1 hr hμ hμ1 hη0 hη θ₁ _ s)

/-- **The optimal action takes over (Mei et al., proof of Lemma 9, Claim III).** If `b` is an
optimal deterministic policy whose action is the unique optimal action at every state, the
probability that the iterates give `b` tends to one. -/
theorem tendsto_softmaxPolicy_pg_one (m : MDP S A) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hr : ∀ s a, m.reward s a ∈ Set.Icc (0 : ℝ) 1) {μ : S → ℝ} (hμ : ∀ s, 0 < μ s)
    (hμ1 : ∑ s, μ s = 1) {η : ℝ} (hη0 : 0 < η) (hη : η ≤ (1 - γ) ^ 3 / 8) (θ₁ : S → A → ℝ)
    (b : S → A) (hb : ∀ (π : StationaryPolicy S A) s,
      m.policyValue π hγ0 hγ1 s ≤ m.policyValue (fun s => PMF.pure (b s)) hγ0 hγ1 s)
    (hgap : ∀ s a, a ≠ b s → m.oneStepActionValue γ
      (m.policyValue (fun s => PMF.pure (b s)) hγ0 hγ1) s a <
        m.policyValue (fun s => PMF.pure (b s)) hγ0 hγ1 s) (s : S) :
    Filter.Tendsto (fun t => (softmaxPolicy (m.pgScores hγ0 hγ1 μ η θ₁ t) s (b s)).toReal)
      Filter.atTop (nhds 1) := by
  classical
  set π : ℕ → A → ℝ := fun t a => (softmaxPolicy (m.pgScores hγ0 hγ1 μ η θ₁ t) s a).toReal
  have hlim := m.pgLimitValue_eq_policyValue hγ0 hγ1 hr hμ hμ1 hη0 hη θ₁ b hb
  have hzero (a : A) (ha : a ≠ b s) : Filter.Tendsto (fun t => π t a) Filter.atTop (nhds 0) := by
    refine m.tendsto_softmaxPolicy_pg_zero hγ0 hγ1 hr (fun s => (hμ s).le) hμ1 hη0 hη θ₁
      (hμ s) ?_
    simp only [pgLimitAdvantage, hlim]
    exact (sub_neg.mpr (hgap s a ha)).ne
  have hsum (t : ℕ) : π t (b s) = 1 - ∑ a ∈ Finset.univ.erase (b s), π t a := by
    have h := Finset.add_sum_erase Finset.univ (π t) (Finset.mem_univ (b s))
    rw [probability_sum] at h
    linarith
  have hrest : Filter.Tendsto (fun t => ∑ a ∈ Finset.univ.erase (b s), π t a) Filter.atTop
      (nhds 0) := by
    have := tendsto_finsetSum (Finset.univ.erase (b s)) fun a ha =>
      hzero a (Finset.ne_of_mem_erase ha)
    simpa using this
  have h := hrest.const_sub 1
  rw [sub_zero] at h
  exact h.congr fun t => (hsum t).symm

/-- **The optimal action keeps a positive probability (Mei et al., Lemma 9).** Under the
conditions of `tendsto_softmaxPolicy_pg_one`, there is `c > 0` such that every iterate gives
`b` probability at least `c` at every state. Unlike the paper, this needs only that the
probability tends to one: it is eventually at least `1 / 2`, and the finitely many earlier
probabilities are positive. -/
theorem exists_pos_le_softmaxPolicy_pg [Nonempty S] (m : MDP S A) {γ : ℝ} (hγ0 : 0 ≤ γ)
    (hγ1 : γ < 1) (hr : ∀ s a, m.reward s a ∈ Set.Icc (0 : ℝ) 1) {μ : S → ℝ}
    (hμ : ∀ s, 0 < μ s) (hμ1 : ∑ s, μ s = 1) {η : ℝ} (hη0 : 0 < η) (hη : η ≤ (1 - γ) ^ 3 / 8)
    (θ₁ : S → A → ℝ) (b : S → A) (hb : ∀ (π : StationaryPolicy S A) s,
      m.policyValue π hγ0 hγ1 s ≤ m.policyValue (fun s => PMF.pure (b s)) hγ0 hγ1 s)
    (hgap : ∀ s a, a ≠ b s → m.oneStepActionValue γ
      (m.policyValue (fun s => PMF.pure (b s)) hγ0 hγ1) s a <
        m.policyValue (fun s => PMF.pure (b s)) hγ0 hγ1 s) :
    ∃ c > 0, ∀ t s,
      c ≤ (softmaxPolicy (m.pgScores hγ0 hγ1 μ η θ₁ t) s (b s)).toReal := by
  set π : ℕ → S → ℝ := fun t s => (softmaxPolicy (m.pgScores hγ0 hγ1 μ η θ₁ t) s (b s)).toReal
  have hpos (t : ℕ) (s : S) : 0 < π t s := by
    simp only [π, softmaxPolicy_apply]
    exact div_pos (Real.exp_pos _) (Finset.sum_pos (fun a _ => Real.exp_pos _)
      Finset.univ_nonempty)
  have hev : ∀ᶠ t in Filter.atTop, ∀ s, 1 / 2 ≤ π t s :=
    Filter.eventually_all.mpr fun s =>
      ((m.tendsto_softmaxPolicy_pg_one hγ0 hγ1 hr hμ hμ1 hη0 hη θ₁ b hb hgap s).eventually
        (le_mem_nhds (by norm_num : (1 : ℝ) / 2 < 1)))
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp hev
  set f : ℕ → ℝ := fun t => Finset.univ.inf' Finset.univ_nonempty (π t)
  set g := (Finset.range (T + 1)).inf' ⟨0, Finset.mem_range.mpr (Nat.succ_pos T)⟩ f
  have hg : 0 < g := (Finset.lt_inf'_iff _).mpr fun t _ =>
    (Finset.lt_inf'_iff _).mpr fun s _ => hpos t s
  refine ⟨min (1 / 2) g, lt_min (by norm_num) hg, fun t s => ?_⟩
  rcases le_or_gt T t with ht | ht
  · exact (min_le_left _ _).trans (hT t ht s)
  · calc min (1 / 2) g ≤ g := min_le_right _ _
      _ ≤ f t := Finset.inf'_le _ (Finset.mem_range.mpr (by omega))
      _ ≤ π t s := Finset.inf'_le _ (Finset.mem_univ s)

/-- **Exact softmax policy gradient converges at rate `1 / t`, unconditionally (Mei et al.,
Theorem 4 with Lemma 9).** With rewards in `[0, 1]`, a start distribution `μ` with `μ s > 0`,
step `η = (1 - γ) ^ 3 / 8`, and an optimal deterministic policy `b` whose action is the unique
optimal action at every state, there is `c > 0` such that for every `t ≥ 1`,
`V* ρ - V θ_t ρ ≤ 16 * |S| / (c ^ 2 * (1 - γ) ^ 6 * t) * D ^ 2 * M` whenever
`d*_μ ≤ D * μ` and `1 ≤ M * μ`. -/
theorem exists_sum_sub_policyValue_pg_le [Nonempty S] (m : MDP S A) {γ : ℝ} (hγ0 : 0 ≤ γ)
    (hγ1 : γ < 1) (hr : ∀ s a, m.reward s a ∈ Set.Icc (0 : ℝ) 1) {μ ρ : S → ℝ}
    (hμ : ∀ s, 0 < μ s) (hμ1 : ∑ s, μ s = 1) (hρ : ∀ s, 0 ≤ ρ s) (hρ1 : ∑ s, ρ s = 1)
    (θ₁ : S → A → ℝ) (b : S → A)
    (hb : ∀ (π : StationaryPolicy S A) s,
      m.policyValue π hγ0 hγ1 s ≤ m.policyValue (fun s => PMF.pure (b s)) hγ0 hγ1 s)
    (hgap : ∀ s a, a ≠ b s → m.oneStepActionValue γ
      (m.policyValue (fun s => PMF.pure (b s)) hγ0 hγ1) s a <
        m.policyValue (fun s => PMF.pure (b s)) hγ0 hγ1 s)
    {D M : ℝ} (hD : ∀ s, m.weightedVisitation (fun s => PMF.pure (b s)) hγ0 hγ1 μ s ≤ D * μ s)
    (hM : ∀ s, 1 ≤ M * μ s) :
    ∃ c > 0, ∀ t : ℕ, 1 ≤ t →
      ∑ s₀, ρ s₀ * (m.policyValue (fun s => PMF.pure (b s)) hγ0 hγ1 s₀ -
        m.policyValue (softmaxPolicy (m.pgScores hγ0 hγ1 μ ((1 - γ) ^ 3 / 8) θ₁ (t - 1)))
          hγ0 hγ1 s₀) ≤
      16 * Fintype.card S / (c ^ 2 * (1 - γ) ^ 6 * t) * D ^ 2 * M := by
  have hγ : 0 < 1 - γ := sub_pos.mpr hγ1
  obtain ⟨c, hc, hπ⟩ := m.exists_pos_le_softmaxPolicy_pg hγ0 hγ1 hr hμ hμ1
    (by positivity : (0 : ℝ) < (1 - γ) ^ 3 / 8) le_rfl θ₁ b hb hgap
  exact ⟨c, hc, fun t ht => m.sum_sub_policyValue_pg_le hγ0 hγ1 hr hμ hμ1 hρ hρ1 θ₁ b hb hc hπ
    hD hM t ht⟩

end Rlib.MDP
