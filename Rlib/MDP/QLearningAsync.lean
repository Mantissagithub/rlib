module

public import Rlib.MDP.QAsynchronous

/-! # Asynchronous tabular Q-learning

At each step one state-action pair is visited and only its entry is updated, from one observed
reward and successor.
-/

@[expose] public section

noncomputable section

open Filter Topology

namespace Rlib

variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty A] [DecidableEq S] [DecidableEq A]

/-- Asynchronous Q-learning: update only the visited entry from the observation at that step. -/
def qLearningAsync (α : ℕ → ℝ) (γ : ℝ) (visits : ℕ → S × A) (observations : ℕ → ℝ × S)
    (q₀ : S → A → ℝ) : ℕ → S → A → ℝ
  | 0 => q₀
  | n + 1 => qLearningUpdate (α n) γ (qLearningAsync α γ visits observations q₀ n)
    (visits n).1 (visits n).2 (observations n)

/-- The step size an entry receives: the step size at a visit, zero otherwise. -/
def visitStep (α : ℕ → ℝ) (visits : ℕ → S × A) (n : ℕ) (s : S) (a : A) : ℝ :=
  if (s, a) = visits n then α n else 0

omit [Fintype S] [Fintype A] [Nonempty A] in
theorem visitStep_nonneg {α : ℕ → ℝ} (hα0 : ∀ n, 0 ≤ α n) (visits : ℕ → S × A)
    (n : ℕ) (s : S) (a : A) : 0 ≤ visitStep α visits n s a := by
  unfold visitStep
  split_ifs
  exacts [hα0 n, le_rfl]

omit [Fintype S] [Fintype A] [Nonempty A] in
theorem visitStep_le_one {α : ℕ → ℝ} (hα1 : ∀ n, α n ≤ 1) (visits : ℕ → S × A)
    (n : ℕ) (s : S) (a : A) : visitStep α visits n s a ≤ 1 := by
  unfold visitStep
  split_ifs
  exacts [hα1 n, zero_le_one]

/-- With step sizes in `[0, 1]`, a discount in `[0, 1)`, and observed rewards bounded by `R`,
asynchronous Q-learning tables stay within `max ‖q₀‖ (R / (1 - γ))` in sup norm. -/
theorem norm_qLearningAsync_le {α : ℕ → ℝ} {γ R : ℝ}
    (hα0 : ∀ n, 0 ≤ α n) (hα1 : ∀ n, α n ≤ 1) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (visits : ℕ → S × A) (observations : ℕ → ℝ × S) (hR : ∀ n, |(observations n).1| ≤ R)
    (q₀ : S → A → ℝ) (n : ℕ) :
    ‖qLearningAsync α γ visits observations q₀ n‖ ≤ max ‖q₀‖ (R / (1 - γ)) := by
  set K := max ‖q₀‖ (R / (1 - γ))
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (le_max_left _ _)
  have hRK : R + γ * K ≤ K := by
    have h := (div_le_iff₀ (sub_pos.mpr hγ1)).1 (le_max_right ‖q₀‖ (R / (1 - γ)))
    linarith
  induction n with
  | zero => exact le_max_left _ _
  | succ n ih =>
    set q := qLearningAsync α γ visits observations q₀ n
    have hentry (s : S) (a : A) : |q s a| ≤ K := by
      have := (norm_le_pi_norm (q s) a).trans (norm_le_pi_norm q s)
      rw [Real.norm_eq_abs] at this
      exact this.trans ih
    apply (pi_norm_le_iff_of_nonneg hK0).2
    intro s
    apply (pi_norm_le_iff_of_nonneg hK0).2
    intro a
    change ‖qLearningUpdate (α n) γ q (visits n).1 (visits n).2 (observations n) s a‖ ≤ K
    rw [Real.norm_eq_abs]
    by_cases hv : (s, a) = visits n
    · have hs : s = (visits n).1 := by rw [← hv]
      have ha : a = (visits n).2 := by rw [← hv]
      subst hs ha
      rw [qLearningUpdate_apply_same]
      have hmax : |qMax q (observations n).2| ≤ K := by
        have := (norm_le_pi_norm (qMax q) (observations n).2).trans (norm_qMax_le q)
        rw [Real.norm_eq_abs] at this
        exact this.trans ih
      have htarget : |qLearningTarget γ q (observations n)| ≤ R + γ * K := by
        unfold qLearningTarget
        refine (abs_add_le _ _).trans (add_le_add (hR n) ?_)
        rw [abs_mul, abs_of_nonneg hγ0]
        exact mul_le_mul_of_nonneg_left hmax hγ0
      have hmix : q (visits n).1 (visits n).2 + α n * (qLearningTarget γ q (observations n) -
          q (visits n).1 (visits n).2) = (1 - α n) * q (visits n).1 (visits n).2 +
            α n * qLearningTarget γ q (observations n) := by ring
      rw [hmix]
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul, abs_of_nonneg (sub_nonneg.mpr (hα1 n)), abs_of_nonneg (hα0 n)]
      nlinarith [mul_le_mul_of_nonneg_left (hentry (visits n).1 (visits n).2)
        (sub_nonneg.mpr (hα1 n)), mul_le_mul_of_nonneg_left htarget (hα0 n), hα0 n]
    · rw [qLearningUpdate_apply_ne _ _ _ _ _ _ _ _ hv]
      exact hentry s a

namespace MDP

/-- Asynchronous Q-learning is the per-entry Bellman Q iteration whose step sizes are the step
size at visits and zero elsewhere, with the realized target errors. -/
theorem qLearningAsync_eq_qAsyncIteration (m : MDP S A) (α : ℕ → ℝ) (γ : ℝ)
    (visits : ℕ → S × A) (observations : ℕ → ℝ × S) (q₀ : S → A → ℝ) :
    qLearningAsync α γ visits observations q₀ =
      m.qAsyncIteration (visitStep α visits) γ
        (fun n s a => qLearningTarget γ (qLearningAsync α γ visits observations q₀ n)
            (observations n) -
          m.qBellmanOperator γ (qLearningAsync α γ visits observations q₀ n) s a) q₀ := by
  funext n
  induction n with
  | zero => rfl
  | succ n ih =>
    funext s a
    simp only [qAsyncIteration, ← ih, visitStep]
    change qLearningUpdate (α n) γ _ (visits n).1 (visits n).2 (observations n) s a = _
    by_cases hv : (s, a) = visits n
    · have hs : s = (visits n).1 := by rw [← hv]
      have ha : a = (visits n).2 := by rw [← hv]
      simp only [hv, ↓reduceIte]
      subst hs ha
      rw [qLearningUpdate_apply_same]
      ring
    · simp only [hv, ↓reduceIte]
      rw [qLearningUpdate_apply_ne _ _ _ _ _ _ _ _ hv]
      ring

/-- Asynchronous Q-learning converges to the Bellman Q fixed point when step sizes lie in
`[0, 1]`, rewards are bounded, every entry's visit step sizes are not summable, and each
entry's visit-weighted realized target errors have convergent partial sums. -/
theorem tendsto_qLearningAsync (m : MDP S A) {α : ℕ → ℝ} {γ R : ℝ}
    (hα0 : ∀ n, 0 ≤ α n) (hα1 : ∀ n, α n ≤ 1) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (visits : ℕ → S × A) (observations : ℕ → ℝ × S) (hR : ∀ n, |(observations n).1| ≤ R)
    (hvisit : ∀ s a, ¬Summable fun n => visitStep α visits n s a)
    (q₀ r : S → A → ℝ) (hr : m.qBellmanOperator γ r = r)
    (he : ∀ s a, ∃ c, Tendsto (fun n => ∑ k ∈ Finset.range n, visitStep α visits k s a *
      (qLearningTarget γ (qLearningAsync α γ visits observations q₀ k) (observations k) -
        m.qBellmanOperator γ (qLearningAsync α γ visits observations q₀ k) s a))
      atTop (𝓝 c)) :
    Tendsto (qLearningAsync α γ visits observations q₀) atTop (𝓝 r) := by
  have hbdd := norm_qLearningAsync_le hα0 hα1 hγ0 hγ1 visits observations hR q₀
  rw [m.qLearningAsync_eq_qAsyncIteration] at hbdd ⊢
  exact m.tendsto_qAsyncIteration (visitStep_nonneg hα0 visits) (visitStep_le_one hα1 visits)
    hvisit hγ0 hγ1 _ he q₀ r hr ⟨_, hbdd⟩

end MDP
end Rlib
