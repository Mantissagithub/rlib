module

public import Rlib.Episodic.Counting
public import Rlib.Probability.Empirical

/-! # The UCB-VI learner

This file defines UCB-VI (Agarwal, Jiang, Kakade, and Sun, Algorithm 5) on a table of
pre-drawn successors: `samples h s a n` is the successor used the `n`-th time the learner takes
`a` in `s` at stage `h`. This "stack of samples" description gives the same law of trajectories
as drawing successors on the fly, and it makes the empirical model `P̂^k_h (· | s, a)` the
empirical distribution of the first `N^k_h (s, a)` draws. The bonus is
`b^k_h (s, a) = 2 H √(L / N^k_h (s, a))`, and `H` at an unvisited pair, where the book's formula
is undefined; there the truncation at `H` makes the optimistic action value `H`.

On the event that the model errors are small, the regret of each episode is at most the
expected value, along the state distribution of the episode's policy, of `2 H` at unvisited
pairs and `10 H √(|S| L / N)` elsewhere.
-/

@[expose] public section

noncomputable section

namespace Rlib

namespace EpisodicMDP

variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty A]

/-- The empirical model from the first `N h s a` draws, and `δ_s` at an unvisited pair. -/
def empiricalModel (samples : ℕ → S → A → ℕ → S) (N : ℕ → S → A → ℕ) (h : ℕ) (s : S)
    (a : A) : PMF S :=
  match N h s a with
  | 0 => PMF.pure s
  | m + 1 => empiricalPMF (fun i : Fin (m + 1) => samples h s a i)

/-- The bonus `2 H √(L / N)`, and `H` at an unvisited pair. -/
def ucbBonus (H : ℕ) (L : ℝ) (N : ℕ → S → A → ℕ) (h : ℕ) (s : S) (a : A) : ℝ :=
  match N h s a with
  | 0 => H
  | m + 1 => 2 * H * Real.sqrt (L / (m + 1))

/-- The policy of UCB-VI given the counts `N`. -/
def ucbviPolicy (M : EpisodicMDP S A) (H : ℕ) (L : ℝ) (samples : ℕ → S → A → ℕ → S)
    (N : ℕ → S → A → ℕ) : EpisodicPolicy S A :=
  M.ucbPolicy (empiricalModel samples N) (ucbBonus H L N) H

/-- The optimistic values of UCB-VI given the counts `N`. -/
def ucbviValue (M : EpisodicMDP S A) (H : ℕ) (L : ℝ) (samples : ℕ → S → A → ℕ → S)
    (N : ℕ → S → A → ℕ) : ℕ → S → ℝ :=
  M.ucbValue (empiricalModel samples N) (ucbBonus H L N) H

omit [Fintype S] [Fintype A] [Nonempty A] in
/-- The states of one episode: the successor at stage `h` is draw number `N h s a`. -/
def episodeState (samples : ℕ → S → A → ℕ → S) (π : EpisodicPolicy S A) (N : ℕ → S → A → ℕ)
    (s₀ : S) : ℕ → S
  | 0 => s₀
  | h + 1 => samples h (episodeState samples π N s₀ h) (π h (episodeState samples π N s₀ h))
      (N h (episodeState samples π N s₀ h) (π h (episodeState samples π N s₀ h)))

variable [DecidableEq S] [DecidableEq A]

/-- The counts of a history of trajectories before episode `k`. -/
def countsOf (τ : ℕ → ℕ → S × A) (k : ℕ) (h : ℕ) (s : S) (a : A) : ℕ := visitCount τ k h (s, a)

/-- The trajectories of the episodes before `k` (and an arbitrary default beyond). -/
def ucbviHistory (M : EpisodicMDP S A) (H : ℕ) (L : ℝ) (s₀ : S)
    (samples : ℕ → S → A → ℕ → S) : ℕ → ℕ → ℕ → S × A
  | 0 => fun _ _ => (s₀, Classical.arbitrary A)
  | k + 1 =>
    let τ := ucbviHistory M H L s₀ samples k
    let N := countsOf τ k
    let π := M.ucbviPolicy H L samples N
    Function.update τ k fun h =>
      (episodeState samples π N s₀ h, π h (episodeState samples π N s₀ h))

/-- The trajectory of episode `k`. -/
def ucbviTrajectory (M : EpisodicMDP S A) (H : ℕ) (L : ℝ) (s₀ : S)
    (samples : ℕ → S → A → ℕ → S) (k : ℕ) : ℕ → S × A :=
  M.ucbviHistory H L s₀ samples (k + 1) k

/-- The counts before episode `k`. -/
def ucbviCounts (M : EpisodicMDP S A) (H : ℕ) (L : ℝ) (s₀ : S)
    (samples : ℕ → S → A → ℕ → S) (k : ℕ) : ℕ → S → A → ℕ :=
  countsOf (fun i => M.ucbviTrajectory H L s₀ samples i) k

/-- The history before episode `k` agrees with the trajectories of the earlier episodes. -/
theorem ucbviHistory_apply (M : EpisodicMDP S A) (H : ℕ) (L : ℝ) (s₀ : S)
    (samples : ℕ → S → A → ℕ → S) {i k : ℕ} (hi : i < k) :
    M.ucbviHistory H L s₀ samples k i = M.ucbviTrajectory H L s₀ samples i := by
  induction k with
  | zero => omega
  | succ k ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [ucbviHistory, Function.update_of_ne (by omega), ih hi]
    · rfl

theorem countsOf_ucbviHistory (M : EpisodicMDP S A) (H : ℕ) (L : ℝ) (s₀ : S)
    (samples : ℕ → S → A → ℕ → S) (k : ℕ) :
    countsOf (M.ucbviHistory H L s₀ samples k) k = M.ucbviCounts H L s₀ samples k := by
  funext h s a
  simp only [countsOf, ucbviCounts, visitCount]
  congr 1
  exact Finset.filter_congr fun i hi => by
    rw [M.ucbviHistory_apply H L s₀ samples (Finset.mem_range.mp hi)]

/-- The policy of episode `k`. -/
def ucbviPolicyAt (M : EpisodicMDP S A) (H : ℕ) (L : ℝ) (s₀ : S)
    (samples : ℕ → S → A → ℕ → S) (k : ℕ) : EpisodicPolicy S A :=
  M.ucbviPolicy H L samples (M.ucbviCounts H L s₀ samples k)

/-- The trajectory of episode `k` follows its policy with the draws indexed by the counts. -/
theorem ucbviTrajectory_eq (M : EpisodicMDP S A) (H : ℕ) (L : ℝ) (s₀ : S)
    (samples : ℕ → S → A → ℕ → S) (k h : ℕ) :
    M.ucbviTrajectory H L s₀ samples k h =
      (episodeState samples (M.ucbviPolicyAt H L s₀ samples k)
        (M.ucbviCounts H L s₀ samples k) s₀ h,
       M.ucbviPolicyAt H L s₀ samples k h (episodeState samples
        (M.ucbviPolicyAt H L s₀ samples k) (M.ucbviCounts H L s₀ samples k) s₀ h)) := by
  simp only [ucbviTrajectory, ucbviHistory, Function.update_self, ucbviPolicyAt,
    countsOf_ucbviHistory]

omit [DecidableEq S] [DecidableEq A] [Fintype A] [Nonempty A] in
/-- Two expectations of a function with values in `[0, B]` differ by at most `B`. -/
theorem abs_expect_sub_expect_le (p q : PMF S) {f : S → ℝ} {B : ℝ}
    (hf : ∀ t, f t ∈ Set.Icc 0 B) : |expect p f - expect q f| ≤ B := by
  have h1 (r : PMF S) : 0 ≤ expect r f := by
    have := expect_mono r (f := fun _ => 0) fun t => (hf t).1
    rwa [expect_zero] at this
  have h2 (r : PMF S) : expect r f ≤ B := by
    have := expect_mono r (g := fun _ => B) fun t => (hf t).2
    rwa [expect_const] at this
  rw [abs_le]
  constructor <;> linarith [h1 p, h1 q, h2 p, h2 q]

omit [DecidableEq S] [DecidableEq A] in
/-- With rewards in `[0, 1]` and nonnegative bonuses, optimistic values lie in `[0, H]`. -/
theorem ucbValue_mem_Icc (M : EpisodicMDP S A) (hr : ∀ h s a, M.reward h s a ∈ Set.Icc (0 : ℝ) 1)
    (Phat : ℕ → S → A → PMF S) {b : ℕ → S → A → ℝ} (hb : ∀ h s a, 0 ≤ b h s a) (H h : ℕ)
    (s : S) : M.ucbValue Phat b H h s ∈ Set.Icc 0 (H : ℝ) := by
  revert s
  refine stage_induction (P := fun h => ∀ s, M.ucbValue Phat b H h s ∈ Set.Icc 0 (H : ℝ)) H
    (fun h hh s => by rw [M.ucbValue_of_le Phat b hh]; exact ⟨le_rfl, by positivity⟩)
    (fun h hh ih s => ?_) h
  rw [M.ucbValue_of_lt Phat b hh]
  simp only [ucbQ]
  set a := M.ucbPolicy Phat b H h s
  have hE : 0 ≤ expect (Phat h s a) (M.ucbValue Phat b H (h + 1)) := by
    have := expect_mono (Phat h s a) (f := fun _ => 0) fun t => (ih t).1
    rwa [expect_zero] at this
  exact ⟨le_min (by linarith [(hr h s a).1, hb h s a]) (by positivity), min_le_right _ _⟩

omit [Fintype S] [Fintype A] [Nonempty A] [DecidableEq S] [DecidableEq A] in
theorem ucbBonus_nonneg (H : ℕ) {L : ℝ} (N : ℕ → S → A → ℕ) (h : ℕ) (s : S) (a : A) :
    0 ≤ ucbBonus H L N h s a := by
  unfold ucbBonus
  split <;> positivity

/-- The per-visit cost of an episode: `2 H` at an unvisited pair and `10 H √(|S| L / N)`
otherwise. -/
def visitCost (S : Type*) [Fintype S] (H : ℕ) (L : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 2 * H else 10 * H * Real.sqrt (Fintype.card S * L / n)

omit [DecidableEq S] [DecidableEq A] in
/-- **One episode of UCB-VI.** Suppose that at every visited pair the empirical model satisfies
the bounds of Lemma 7.3, `|(P̂ - P) V*_{h+1}| ≤ 2 H √(L / N)`, and of Lemma 7.2,
`|(P̂ - P) f| ≤ 8 H √(|S| L / N)` for every `f` with values in `[0, H]`. Then the regret of the
episode's policy `π` is at most the expected visit cost along the state distribution of `π`. -/
theorem optValue_sub_value_ucbviPolicy_le (M : EpisodicMDP S A)
    (hr : ∀ h s a, M.reward h s a ∈ Set.Icc (0 : ℝ) 1) (H : ℕ) {L : ℝ} (hL : 0 ≤ L)
    (samples : ℕ → S → A → ℕ → S) (N : ℕ → S → A → ℕ) (s₀ : S)
    (h73 : ∀ h, h < H → ∀ s a, 0 < N h s a →
      |expect (empiricalModel samples N h s a) (M.optValue H (h + 1)) -
        expect (M.transition h s a) (M.optValue H (h + 1))| ≤ 2 * H * Real.sqrt (L / N h s a))
    (h72 : ∀ h, h < H → ∀ s a, 0 < N h s a → ∀ f : S → ℝ, (∀ t, f t ∈ Set.Icc 0 (H : ℝ)) →
      |expect (empiricalModel samples N h s a) f - expect (M.transition h s a) f| ≤
        8 * H * Real.sqrt (Fintype.card S * L / N h s a)) :
    M.optValue H 0 s₀ - M.value (M.ucbviPolicy H L samples N) H 0 s₀ ≤
      ∑ h ∈ Finset.range H, expect (M.stateDist (M.ucbviPolicy H L samples N) s₀ h)
        (fun s => visitCost S H L (N h s (M.ucbviPolicy H L samples N h s))) := by
  set Phat := empiricalModel samples N
  set b := ucbBonus H L N
  set π := M.ucbviPolicy H L samples N
  have hbnn := ucbBonus_nonneg (S := S) (A := A) H (L := L) N
  have hS : (1 : ℝ) ≤ Fintype.card S := by
    have : Nonempty S := ⟨s₀⟩
    exact Nat.one_le_cast.mpr Fintype.card_pos
  have hV (h : ℕ) (t : S) : M.optValue H (h + 1) t ∈ Set.Icc 0 (H : ℝ) := by
    refine ⟨M.optValue_nonneg (fun h s a => (hr h s a).1) H (h + 1) t, ?_⟩
    by_cases hh : h + 1 ≤ H
    · have := M.optValue_le (fun h s a => (hr h s a).2) hh t
      push_cast at this
      linarith
    · rw [M.optValue_of_le (by omega)]; positivity
  -- Optimism.
  have hopt := M.optValue_le_ucbValue hr Phat b H (fun h hh s a => by
    rcases hN : N h s a with _ | m
    · simp only [b, ucbBonus, hN]
      exact abs_expect_sub_expect_le _ _ (hV h)
    · have := h73 h hh s a (by omega)
      simp only [hN] at this
      simp only [b, ucbBonus, hN]
      push_cast at this ⊢
      exact this) 0 s₀
  have hsim := M.ucbValue_sub_value_le Phat b H s₀
  have hπ : M.ucbPolicy Phat b H = π := rfl
  rw [hπ] at hsim
  refine (sub_le_sub_right hopt _).trans (hsim.trans (Finset.sum_le_sum fun h hh => ?_))
  refine expect_mono _ fun s => ?_
  have hVhat (t : S) : M.ucbValue Phat b H (h + 1) t ∈ Set.Icc 0 (H : ℝ) :=
    M.ucbValue_mem_Icc hr Phat hbnn H (h + 1) t
  simp only [visitCost]
  rcases hN : N h s (π h s) with _ | m
  · simp only [b, ucbBonus, hN, ↓reduceIte]
    have := abs_expect_sub_expect_le (Phat h s (π h s)) (M.transition h s (π h s)) hVhat
    linarith [le_abs_self (expect (Phat h s (π h s)) (M.ucbValue Phat b H (h + 1)) -
      expect (M.transition h s (π h s)) (M.ucbValue Phat b H (h + 1)))]
  · simp only [b, ucbBonus, hN, Nat.add_one_ne_zero, ↓reduceIte]
    have h1 := h72 h (Finset.mem_range.mp hh) s (π h s) (by omega) _ hVhat
    simp only [hN] at h1
    push_cast at h1 ⊢
    have hsq : Real.sqrt (L / (m + 1)) ≤ Real.sqrt (Fintype.card S * L / (m + 1)) :=
      Real.sqrt_le_sqrt (div_le_div_of_nonneg_right (le_mul_of_one_le_left hL hS)
        (by positivity))
    have hH : (0 : ℝ) ≤ H := by positivity
    nlinarith [le_abs_self (expect (Phat h s (π h s)) (M.ucbValue Phat b H (h + 1)) -
      expect (M.transition h s (π h s)) (M.ucbValue Phat b H (h + 1))),
      mul_le_mul_of_nonneg_left hsq (by positivity : (0 : ℝ) ≤ 2 * H)]

end EpisodicMDP

end Rlib
