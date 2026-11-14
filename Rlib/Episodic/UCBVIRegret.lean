module

public import Rlib.Episodic.UCBVIConcentration

/-! # The regret of UCB-VI

This file proves Agarwal, Jiang, Kakade, and Sun, Theorem 7.1, for UCB-VI on pre-drawn successors
with the bonus `2 H √(L / N)` and `L = log (2 H |S| |A| K / δ)`:
`E [∑_{k < K} (V*_0 (s₀) - V^{π_k}_0 (s₀))] ≤ 20 H ^ 2 |S| √(|A| K L) + 2 H ^ 2 |S| |A| + 2 δ K H`.
The book states `10 H ^ 2 |S| √(|A| K L')`; the additional terms account for first visits, where
the book's bonus is undefined, and for the failure event, and the constant `20` comes from
Lemma 7.5 as stated.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Rlib

namespace EpisodicMDP

variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty A] [DecidableEq S] [DecidableEq A]
  {H K : ℕ}

omit [Fintype S] [Fintype A] [Nonempty A] [DecidableEq S] [DecidableEq A] in
/-- The empirical model of the draw table at a visited pair averages the first draws. -/
theorem expect_empiricalModel_tape [Fintype S] (ω : TapeIndex S A H K → S)
    (N : ℕ → S → A → ℕ) {h : ℕ} (hh : h < H) (s : S) (a : A) {m : ℕ} (hm : m < K)
    (hN : N h s a = m + 1) (f : S → ℝ) :
    expect (empiricalModel (tapeSamples ω) N h s a) f =
      sampleMean (fun i : Fin (m + 1) => f (ω (⟨h, hh⟩, s, a,
        ⟨i, drawIndex_lt (⟨m, hm⟩ : Fin K) i⟩))) := by
  unfold empiricalModel
  rw [hN]
  simp only
  rw [expect_empiricalPMF]
  congr 1
  funext i
  simp only [tapeSamples, hh, drawIndex_lt (⟨m, hm⟩ : Fin K) i, ↓reduceDIte]

variable [MeasurableSpace S] [MeasurableSingletonClass S]

/-- The first bad event: some empirical model errs on `V*_{h+1}` by `H √(2 L / N)` or more. -/
def badValue (M : EpisodicMDP S A) (H K : ℕ) (δ : ℝ) : Set (TapeIndex S A H K → S) :=
  {ω | ∃ _j : Unit, ∃ h : Fin H, ∃ s a, ∃ m : Fin K,
    (H : ℝ) * Real.sqrt (2 * Real.log (2 * (Fintype.card Unit * H * Fintype.card S *
      Fintype.card A * K) / δ) / (m + 1)) ≤
    |sampleMean (fun i : Fin (m + 1) => M.optValue H (h + 1) (ω (h, s, a, ⟨i, drawIndex_lt m i⟩))) -
      expect (M.transition h s a) (M.optValue H (h + 1))|}

/-- The second bad event: some empirical model errs on the mass of a set of states. -/
def badSets (M : EpisodicMDP S A) (H K : ℕ) (δ : ℝ) : Set (TapeIndex S A H K → S) :=
  {ω | ∃ T : Finset S, ∃ h : Fin H, ∃ s a, ∃ m : Fin K,
    1 * Real.sqrt (2 * Real.log (2 * (Fintype.card (Finset S) * H * Fintype.card S *
      Fintype.card A * K) / δ) / (m + 1)) ≤
    |sampleMean (fun i : Fin (m + 1) => (fun t => if t ∈ T then (1 : ℝ) else 0)
      (ω (h, s, a, ⟨i, drawIndex_lt m i⟩))) -
      expect (M.transition h s a) (fun t => if t ∈ T then (1 : ℝ) else 0)|}

omit [Nonempty A] [DecidableEq A] [MeasurableSpace S] [MeasurableSingletonClass S] in
/-- The mass of a set is the expectation of its indicator. -/
theorem expect_indicator (p : PMF S) (T : Finset S) :
    expect p (fun t => if t ∈ T then (1 : ℝ) else 0) = ∑ t ∈ T, (p t).toReal := by
  simp only [expect, mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  congr 1
  ext t
  simp

omit [MeasurableSpace S] [MeasurableSingletonClass S] in
/-- **The good event.** Off the two bad events, every episode `k < K` satisfies the bounds of
Lemmas 7.3 and 7.2 with `L = log (2 H |S| |A| K / δ)`. -/
theorem good_event (M : EpisodicMDP S A) (hH : 0 < H) (s₀ : S) {δ : ℝ} (hδ0 : 0 < δ)
    (hδ1 : δ ≤ 1) (ω : TapeIndex S A H K → S)
    (hω : ω ∉ M.badValue H K δ ∪ M.badSets H K δ) {k : ℕ} (hk : k < K) :
    let L := Real.log (2 * (H * Fintype.card S * Fintype.card A * K) / δ)
    let N := M.ucbviCounts H L s₀ (tapeSamples ω) k
    (∀ h, h < H → ∀ s a, 0 < N h s a →
      |expect (empiricalModel (tapeSamples ω) N h s a) (M.optValue H (h + 1)) -
        expect (M.transition h s a) (M.optValue H (h + 1))| ≤
        2 * H * Real.sqrt (L / N h s a)) ∧
    (∀ h, h < H → ∀ s a, 0 < N h s a → ∀ f : S → ℝ, (∀ t, f t ∈ Set.Icc 0 (H : ℝ)) →
      |expect (empiricalModel (tapeSamples ω) N h s a) f - expect (M.transition h s a) f| ≤
        8 * H * Real.sqrt (Fintype.card S * L / N h s a)) := by
  intro L N
  simp only [Set.mem_union, not_or, badValue, badSets, Set.mem_ofPred_eq, not_exists,
    not_le] at hω
  obtain ⟨hV, hT⟩ := hω
  set C : ℝ := H * Fintype.card S * Fintype.card A * K
  have hS1 : (1 : ℝ) ≤ Fintype.card S := by
    have : Nonempty S := ⟨s₀⟩; exact Nat.one_le_cast.mpr Fintype.card_pos
  have hA1 : (1 : ℝ) ≤ Fintype.card A := Nat.one_le_cast.mpr Fintype.card_pos
  have hH1 : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast (show 1 ≤ K by omega)
  have hC1 : 1 ≤ C := by
    simp only [C]
    have := mul_le_mul hH1 hS1 zero_le_one (by positivity)
    have := mul_le_mul this hA1 zero_le_one (by positivity)
    have := mul_le_mul this hK1 zero_le_one (by positivity)
    linarith
  have hLlog2 : Real.log 2 ≤ L := by
    refine Real.log_le_log (by norm_num) ?_
    rw [le_div_iff₀ hδ0]
    nlinarith
  have hL0 : 0 ≤ L := (Real.log_nonneg (by norm_num)).trans hLlog2
  -- Each count is `m + 1` with `m < K`.
  have hcount (h : ℕ) (s : S) (a : A) (hpos : 0 < N h s a) :
      ∃ m, m < K ∧ N h s a = m + 1 :=
    ⟨N h s a - 1, by
      have := M.ucbviCounts_le H L s₀ (tapeSamples ω) k h s a
      change N h s a ≤ k at this
      omega, by omega⟩
  constructor
  · intro h hh s a hpos
    obtain ⟨m, hm, hN⟩ := hcount h s a hpos
    rw [expect_empiricalModel_tape ω N hh s a hm hN, hN]
    have h1 := (hV () ⟨h, hh⟩ s a ⟨m, hm⟩).le
    simp only [Fintype.card_unit, Nat.cast_one, one_mul] at h1
    refine h1.trans ?_
    push_cast
    rw [show (2 : ℝ) * (H * Fintype.card S * Fintype.card A * K) / δ = 2 * C / δ by ring]
    have hsq : Real.sqrt (2 * L / (m + 1)) ≤ 2 * Real.sqrt (L / (m + 1)) := by
      rw [show 2 * L / (m + 1) = 2 * (L / (m + 1)) by ring, Real.sqrt_mul (by norm_num)]
      have : Real.sqrt 2 ≤ 2 := by
        rw [Real.sqrt_le_left (by norm_num)]; norm_num
      exact mul_le_mul_of_nonneg_right this (Real.sqrt_nonneg _)
    simp only [L, C] at hsq ⊢
    nlinarith [mul_le_mul_of_nonneg_left hsq (by positivity : (0 : ℝ) ≤ H)]
  · intro h hh s a hpos f hf
    obtain ⟨m, hm, hN⟩ := hcount h s a hpos
    set ε := Real.sqrt (2 * Real.log (2 * (Fintype.card (Finset S) * H * Fintype.card S *
      Fintype.card A * K) / δ) / (m + 1))
    have hsets : ∀ T : Finset S, |∑ t ∈ T, (empiricalModel (tapeSamples ω) N h s a t).toReal -
        ∑ t ∈ T, (M.transition h s a t).toReal| ≤ ε := by
      intro T
      rw [← expect_indicator, ← expect_indicator,
        expect_empiricalModel_tape ω N hh s a hm hN]
      have := (hT T ⟨h, hh⟩ s a ⟨m, hm⟩).le
      rw [one_mul] at this
      exact this
    refine (abs_expect_sub_le_of_sets _ _ hsets (by positivity) hf).trans ?_
    rw [hN]
    -- `ε ≤ 2 √(|S| L / (m + 1))`.
    have hcardF : (Fintype.card (Finset S) : ℝ) = 2 ^ Fintype.card S := by
      rw [Fintype.card_finset]; push_cast; ring
    have hlogsplit : Real.log (2 * (Fintype.card (Finset S) * H * Fintype.card S *
        Fintype.card A * K) / δ) = Fintype.card S * Real.log 2 + L := by
      rw [hcardF, show (2 : ℝ) * (2 ^ Fintype.card S * H * Fintype.card S * Fintype.card A * K) /
        δ = 2 ^ Fintype.card S * (2 * C / δ) by simp only [C]; ring,
        Real.log_mul (by positivity) (by positivity), Real.log_pow]
    have hlogle : Real.log (2 * (Fintype.card (Finset S) * H * Fintype.card S *
        Fintype.card A * K) / δ) ≤ 2 * (Fintype.card S * L) := by
      rw [hlogsplit]
      nlinarith [mul_le_mul_of_nonneg_left hLlog2 (by positivity : (0 : ℝ) ≤ Fintype.card S)]
    have hε : ε ≤ 2 * Real.sqrt (Fintype.card S * L / (m + 1)) := by
      have h4 : Real.sqrt (4 * (Fintype.card S * L / (m + 1))) =
          2 * Real.sqrt (Fintype.card S * L / (m + 1)) := by
        rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq
          (by norm_num)]
      rw [← h4]
      apply Real.sqrt_le_sqrt
      rw [show 4 * (Fintype.card S * L / (m + 1)) = 2 * (2 * (Fintype.card S * L)) / (m + 1)
        by ring]
      exact div_le_div_of_nonneg_right (by linarith) (by positivity)
    push_cast
    have hH0 : (0 : ℝ) ≤ H := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hε hH0, Real.sqrt_nonneg
      ((Fintype.card S : ℝ) * L / (m + 1))]

omit [DecidableEq A] in
/-- The two bad events together have probability at most `2 δ`. -/
theorem measure_bad_le (M : EpisodicMDP S A) (hr : ∀ h s a, M.reward h s a ∈ Set.Icc (0 : ℝ) 1)
    (hH : 0 < H) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    (M.tapeLaw H K).real (M.badValue H K δ ∪ M.badSets H K δ) ≤ 2 * δ := by
  have h1 := M.measure_tape_exists_le (H := H) (K := K) (J := Unit)
    (fun _ h t => M.optValue H (h + 1) t)
    (B := H) (by exact_mod_cast hH) (fun _ h t => by
      have h0 := M.optValue_nonneg (fun h s a => (hr h s a).1) H (h + 1) t
      rw [abs_of_nonneg h0]
      by_cases hh : h + 1 ≤ H
      · have := M.optValue_le (fun h s a => (hr h s a).2) hh t
        push_cast at this
        linarith
      · rw [M.optValue_of_le (by omega)]; positivity) hδ0 hδ1
  have h2 := M.measure_tape_exists_le (H := H) (K := K) (J := Finset S)
    (fun T _ t => if t ∈ T then (1 : ℝ) else 0) (B := 1) one_pos
    (fun T _ t => by split_ifs <;> simp) hδ0 hδ1
  calc _ ≤ (M.tapeLaw H K).real (M.badValue H K δ) + (M.tapeLaw H K).real (M.badSets H K δ) :=
        measureReal_union_le _ _
    _ ≤ δ + δ := add_le_add h1 h2
    _ = 2 * δ := by ring

omit [MeasurableSpace S] [MeasurableSingletonClass S] [DecidableEq S] [DecidableEq A]
  [Fintype A] [Nonempty A] in
theorem visitCost_nonneg (H : ℕ) (L : ℝ) (n : ℕ) : 0 ≤ visitCost S H L n := by
  unfold visitCost; split_ifs <;> positivity

omit [MeasurableSpace S] [MeasurableSingletonClass S] in
/-- **Counting the realized costs.** Along the realized trajectories, the visit costs add up to
at most `2 H ^ 2 |S| |A| + 20 H ^ 2 √(|S| L) √(|S| |A| K)`, by Lemma 7.5 and because each stage
has at most `|S| |A|` first visits. -/
theorem sum_visitCost_le (M : EpisodicMDP S A) (H : ℕ) (L : ℝ) (s₀ : S)
    (samples : ℕ → S → A → ℕ → S) (K : ℕ) :
    ∑ k ∈ Finset.range K, ∑ h ∈ Finset.range H, visitCost S H L
      (M.ucbviCounts H L s₀ samples k h (M.ucbviTrajectory H L s₀ samples k h).1
        (M.ucbviTrajectory H L s₀ samples k h).2) ≤
      2 * H * (H * (Fintype.card S * Fintype.card A)) +
        10 * H * Real.sqrt (Fintype.card S * L) *
          (2 * H * Real.sqrt (Fintype.card (S × A) * K)) := by
  set τ : ℕ → ℕ → S × A := fun k h => M.ucbviTrajectory H L s₀ samples k h
  have hN (k h : ℕ) : M.ucbviCounts H L s₀ samples k h (τ k h).1 (τ k h).2 =
      visitCount τ k h (τ k h) := rfl
  have hcost (n : ℕ) : visitCost S H L n ≤
      2 * H * (if n = 0 then 1 else 0) + 10 * H * Real.sqrt (Fintype.card S * L) *
        (1 / Real.sqrt n) := by
    unfold visitCost
    split_ifs with hn
    · subst hn; simp
    · rw [Real.sqrt_div' _ (Nat.cast_nonneg n)]
      simp only [mul_zero, zero_add]
      rw [div_eq_mul_one_div]
      ring_nf
      exact le_rfl
  have hfirst (h : ℕ) : ∑ k ∈ Finset.range K, (if visitCount τ k h (τ k h) = 0 then (1 : ℝ)
      else 0) ≤ Fintype.card S * Fintype.card A := by
    rw [sum_visitCount_eq τ h (fun j => if j = 0 then (1 : ℝ) else 0) K]
    calc ∑ x, ∑ j ∈ Finset.range (visitCount τ K h x), (if j = 0 then (1 : ℝ) else 0)
        ≤ ∑ _x : S × A, (1 : ℝ) := Finset.sum_le_sum fun x _ => by
          rw [Finset.sum_ite_eq']
          split_ifs <;> norm_num
      _ = _ := by simp [Fintype.card_prod]
  have hpig := sum_one_div_sqrt_visitCount_le τ H K
  calc ∑ k ∈ Finset.range K, ∑ h ∈ Finset.range H, visitCost S H L
        (M.ucbviCounts H L s₀ samples k h (τ k h).1 (τ k h).2)
      ≤ ∑ k ∈ Finset.range K, ∑ h ∈ Finset.range H,
        (2 * H * (if visitCount τ k h (τ k h) = 0 then 1 else 0) +
          10 * H * Real.sqrt (Fintype.card S * L) * (1 / Real.sqrt (visitCount τ k h (τ k h)))) :=
        Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun h _ => by rw [hN]; exact hcost _
    _ = 2 * H * ∑ h ∈ Finset.range H, ∑ k ∈ Finset.range K,
          (if visitCount τ k h (τ k h) = 0 then (1 : ℝ) else 0) +
        10 * H * Real.sqrt (Fintype.card S * L) * ∑ k ∈ Finset.range K, ∑ h ∈ Finset.range H,
          1 / Real.sqrt (visitCount τ k h (τ k h)) := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
        rw [Finset.sum_comm (f := fun k h => if visitCount τ k h (τ k h) = 0 then (1 : ℝ) else 0)]
    _ ≤ 2 * H * (H * (Fintype.card S * Fintype.card A)) +
        10 * H * Real.sqrt (Fintype.card S * L) *
          (2 * H * Real.sqrt (Fintype.card (S × A) * K)) := by
        gcongr
        calc ∑ h ∈ Finset.range H, ∑ k ∈ Finset.range K,
            (if visitCount τ k h (τ k h) = 0 then (1 : ℝ) else 0)
            ≤ ∑ _h ∈ Finset.range H, ((Fintype.card S : ℝ) * Fintype.card A) :=
              Finset.sum_le_sum fun h _ => hfirst h
          _ = _ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- **Regret of UCB-VI (Agarwal, Jiang, Kakade, and Sun, Theorem 7.1).** Take rewards in
`[0, 1]`, horizon `H > 0`, `K` episodes from `s₀`, `0 < δ ≤ 1`, and the bonus with
`L = log (2 H |S| |A| K / δ)`. Then the expected regret
`E [∑_{k < K} (V*_0 (s₀) - V^{π_k}_0 (s₀))]` is at most
`2 H ^ 2 |S| |A| + 20 H ^ 2 √(|S| L) √(|S| |A| K) + 2 δ K H`. -/
theorem regret_ucbvi_le (M : EpisodicMDP S A) (hr : ∀ h s a, M.reward h s a ∈ Set.Icc (0 : ℝ) 1)
    (hH : 0 < H) (s₀ : S) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    ∫ ω, ∑ k ∈ Finset.range K, (M.optValue H 0 s₀ - M.value (M.ucbviPolicyAt H
        (Real.log (2 * (H * Fintype.card S * Fintype.card A * K) / δ)) s₀ (tapeSamples ω) k)
        H 0 s₀) ∂M.tapeLaw H K ≤
      2 * H * (H * (Fintype.card S * Fintype.card A)) +
        10 * H * Real.sqrt (Fintype.card S *
          Real.log (2 * (H * Fintype.card S * Fintype.card A * K) / δ)) *
          (2 * H * Real.sqrt (Fintype.card (S × A) * K)) + 2 * δ * (K * H) := by
  set L := Real.log (2 * (H * Fintype.card S * Fintype.card A * K) / δ)
  set μ := M.tapeLaw H K
  set Bad := M.badValue H K δ ∪ M.badSets H K δ
  set π : ℕ → (TapeIndex S A H K → S) → EpisodicPolicy S A :=
    fun k ω => M.ucbviPolicyAt H L s₀ (tapeSamples ω) k
  set N : ℕ → (TapeIndex S A H K → S) → ℕ → S → A → ℕ :=
    fun k ω => M.ucbviCounts H L s₀ (tapeSamples ω) k
  set cost : ℕ → ℕ → (TapeIndex S A H K → S) → S → ℝ :=
    fun k h ω s => visitCost S H L (N k ω h s (π k ω h s))
  set C := 2 * H * (H * (Fintype.card S * Fintype.card A)) +
    10 * H * Real.sqrt (Fintype.card S * L) * (2 * H * Real.sqrt (Fintype.card (S × A) * K))
  have hVle (k : ℕ) (ω : TapeIndex S A H K → S) :
      M.optValue H 0 s₀ - M.value (π k ω) H 0 s₀ ≤ H := by
    have h1 := M.optValue_le (fun h s a => (hr h s a).2) (Nat.zero_le H) s₀
    have h2 := M.value_nonneg (fun h s a => (hr h s a).1) (π k ω) H 0 s₀
    push_cast at h1
    linarith
  have hcost0 (k h : ℕ) (ω : TapeIndex S A H K → S) (t : S) : 0 ≤ cost k h ω t :=
    visitCost_nonneg H L _
  -- Pointwise: the good event gives the per-episode bound, the bad event costs `K H`.
  have hpt (ω : TapeIndex S A H K → S) :
      ∑ k ∈ Finset.range K, (M.optValue H 0 s₀ - M.value (π k ω) H 0 s₀) ≤
        ∑ k ∈ Finset.range K, ∑ h ∈ Finset.range H,
          expect (M.stateDist (π k ω) s₀ h) (cost k h ω) +
        Bad.indicator (fun _ => (K : ℝ) * H) ω := by
    have hsum0 : 0 ≤ ∑ k ∈ Finset.range K, ∑ h ∈ Finset.range H,
        expect (M.stateDist (π k ω) s₀ h) (cost k h ω) :=
      Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun h _ => by
        have := expect_mono (M.stateDist (π k ω) s₀ h) (f := fun _ => 0) (hcost0 k h ω)
        rwa [expect_zero] at this
    by_cases hω : ω ∈ Bad
    · rw [Set.indicator_of_mem hω]
      calc _ ≤ ∑ _k ∈ Finset.range K, (H : ℝ) := Finset.sum_le_sum fun k _ => hVle k ω
        _ = K * H := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        _ ≤ _ := by linarith
    · rw [Set.indicator_of_notMem hω, add_zero]
      refine Finset.sum_le_sum fun k hk => ?_
      have hk' := Finset.mem_range.mp hk
      obtain ⟨h73, h72⟩ := M.good_event hH s₀ hδ0 hδ1 ω hω hk'
      have hL0 : 0 ≤ L := by
        refine Real.log_nonneg ?_
        rw [le_div_iff₀ hδ0]
        have hS1 : (1 : ℝ) ≤ Fintype.card S := by
          have : Nonempty S := ⟨s₀⟩; exact Nat.one_le_cast.mpr Fintype.card_pos
        have hA1 : (1 : ℝ) ≤ Fintype.card A := Nat.one_le_cast.mpr Fintype.card_pos
        have hH1 : (1 : ℝ) ≤ H := by exact_mod_cast hH
        have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast (show 1 ≤ K by omega)
        have := mul_le_mul (mul_le_mul (mul_le_mul hH1 hS1 zero_le_one (by positivity)) hA1
          zero_le_one (by positivity)) hK1 zero_le_one (by positivity)
        linarith
      exact M.optValue_sub_value_ucbviPolicy_le hr H hL0 (tapeSamples ω) (N k ω) s₀ h73 h72
  -- Integrate.
  have hint : ∫ ω, ∑ k ∈ Finset.range K, (M.optValue H 0 s₀ - M.value (π k ω) H 0 s₀) ∂μ ≤
      ∑ k ∈ Finset.range K, ∑ h ∈ Finset.range H,
        ∫ ω, expect (M.stateDist (π k ω) s₀ h) (cost k h ω) ∂μ + (K * H) * μ.real Bad := by
    calc _ ≤ ∫ ω, (∑ k ∈ Finset.range K, ∑ h ∈ Finset.range H,
          expect (M.stateDist (π k ω) s₀ h) (cost k h ω) +
          Bad.indicator (fun _ => (K : ℝ) * H) ω) ∂μ :=
          integral_mono Integrable.of_finite Integrable.of_finite hpt
      _ = _ := by
          rw [integral_add Integrable.of_finite Integrable.of_finite,
            integral_finsetSum _ fun k _ => Integrable.of_finite]
          simp only [integral_finsetSum _ fun h _ => Integrable.of_finite]
          rw [integral_indicator_const _ (MeasurableSet.of_discrete), smul_eq_mul, mul_comm]
  -- Replace the state distributions by the realized trajectories.
  have hlaw : ∑ k ∈ Finset.range K, ∑ h ∈ Finset.range H,
      ∫ ω, expect (M.stateDist (π k ω) s₀ h) (cost k h ω) ∂μ =
      ∫ ω, ∑ k ∈ Finset.range K, ∑ h ∈ Finset.range H, visitCost S H L
        (M.ucbviCounts H L s₀ (tapeSamples ω) k h
          (M.ucbviTrajectory H L s₀ (tapeSamples ω) k h).1
          (M.ucbviTrajectory H L s₀ (tapeSamples ω) k h).2) ∂μ := by
    rw [integral_finsetSum _ fun k _ => Integrable.of_finite]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [integral_finsetSum _ fun h _ => Integrable.of_finite]
    refine Finset.sum_congr rfl fun h hh => ?_
    have hpast : ∀ y, M.IsPast H K L s₀ k fun ω => cost k h ω y := by
      intro y ω ω' hagree
      obtain ⟨hN, hπ⟩ := M.ucbviCounts_policy_congr L s₀ k hagree
      simp only [cost, N, π, hN, hπ]
    rw [← M.integral_ucbviTrajectory_eq_stateDist L s₀ (Finset.mem_range.mp hk) h
      (Finset.mem_range.mp hh).le (cost k h) hpast]
    congr 1
    funext ω
    simp only [cost, N, π]
    rw [show (M.ucbviTrajectory H L s₀ (tapeSamples ω) k h).2 =
      M.ucbviPolicyAt H L s₀ (tapeSamples ω) k h
        (M.ucbviTrajectory H L s₀ (tapeSamples ω) k h).1 by rw [ucbviTrajectory_eq]]
  have hpath : ∫ ω, ∑ k ∈ Finset.range K, ∑ h ∈ Finset.range H, visitCost S H L
        (M.ucbviCounts H L s₀ (tapeSamples ω) k h
          (M.ucbviTrajectory H L s₀ (tapeSamples ω) k h).1
          (M.ucbviTrajectory H L s₀ (tapeSamples ω) k h).2) ∂μ ≤ C := by
    calc _ ≤ ∫ _ω, C ∂μ := integral_mono Integrable.of_finite Integrable.of_finite
          fun ω => M.sum_visitCost_le H L s₀ (tapeSamples ω) K
      _ = C := by simp
  have hbad := M.measure_bad_le (K := K) hr hH hδ0 hδ1
  have hKH : (0 : ℝ) ≤ K * H := by positivity
  calc _ ≤ ∑ k ∈ Finset.range K, ∑ h ∈ Finset.range H,
        ∫ ω, expect (M.stateDist (π k ω) s₀ h) (cost k h ω) ∂μ + (K * H) * μ.real Bad := hint
    _ ≤ C + (K * H) * (2 * δ) := by
        rw [hlaw]
        exact add_le_add hpath (mul_le_mul_of_nonneg_left hbad hKH)
    _ = _ := by simp only [C]; ring

/-- **Regret of UCB-VI, in the form of Theorem 7.1.** Under the conditions of
`regret_ucbvi_le`, with `L = log (2 H |S| |A| K / δ)`,
`E [∑_{k < K} (V*_0 (s₀) - V^{π_k}_0 (s₀))] ≤
20 H ^ 2 |S| √(|A| K L) + 2 H ^ 2 |S| |A| + 2 δ K H`. -/
theorem regret_ucbvi_le' (M : EpisodicMDP S A)
    (hr : ∀ h s a, M.reward h s a ∈ Set.Icc (0 : ℝ) 1) (hH : 0 < H) (s₀ : S) {δ : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    ∫ ω, ∑ k ∈ Finset.range K, (M.optValue H 0 s₀ - M.value (M.ucbviPolicyAt H
        (Real.log (2 * (H * Fintype.card S * Fintype.card A * K) / δ)) s₀ (tapeSamples ω) k)
        H 0 s₀) ∂M.tapeLaw H K ≤
      20 * H ^ 2 * Fintype.card S * Real.sqrt (Fintype.card A * K *
          Real.log (2 * (H * Fintype.card S * Fintype.card A * K) / δ)) +
        2 * H ^ 2 * Fintype.card S * Fintype.card A + 2 * δ * K * H := by
  refine (M.regret_ucbvi_le hr hH s₀ hδ0 hδ1).trans (le_of_eq ?_)
  set L := Real.log (2 * (H * Fintype.card S * Fintype.card A * K) / δ)
  set Sc : ℝ := (Fintype.card S : ℝ)
  set Ac : ℝ := (Fintype.card A : ℝ)
  have hcard : (Fintype.card (S × A) : ℝ) = Sc * Ac := by
    simp only [Fintype.card_prod, Nat.cast_mul, Sc, Ac]
  have hS0 : 0 ≤ Sc := Nat.cast_nonneg _
  by_cases hL : 0 ≤ L
  · have hsq : Real.sqrt (Sc * L) * Real.sqrt (Sc * Ac * K) = Sc * Real.sqrt (Ac * K * L) := by
      rw [← Real.sqrt_mul (by positivity), show Sc * L * (Sc * Ac * K) = Sc ^ 2 * (Ac * K * L)
        by ring, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hS0]
    rw [hcard]
    calc 2 * H * (H * (Sc * Ac)) + 10 * H * Real.sqrt (Sc * L) * (2 * H * Real.sqrt (Sc * Ac * K)) +
          2 * δ * (K * H)
        = 2 * H * (H * (Sc * Ac)) + 20 * H ^ 2 * (Real.sqrt (Sc * L) *
          Real.sqrt (Sc * Ac * K)) + 2 * δ * (K * H) := by ring
      _ = _ := by rw [hsq]; ring
  · -- A negative `L` makes both square roots vanish.
    have h1 : Real.sqrt (Sc * L) = 0 := Real.sqrt_eq_zero'.mpr
      (mul_nonpos_of_nonneg_of_nonpos hS0 (le_of_lt (not_le.mp hL)))
    have h2 : Real.sqrt (Ac * K * L) = 0 := Real.sqrt_eq_zero'.mpr
      (mul_nonpos_of_nonneg_of_nonpos (by positivity) (le_of_lt (not_le.mp hL)))
    rw [h1, h2]
    ring

end EpisodicMDP

end Rlib
