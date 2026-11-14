module

public import Rlib.Probability.Expectation
public import Mathlib.Data.Finset.Lattice.Fold

/-! # Episodic MDPs and optimistic value iteration

This file sets up the finite-horizon episodic setting of Agarwal, Jiang, Kakade, and Sun,
*Reinforcement Learning: Theory and Algorithms*, Section 1.2 and Chapter 7. Transitions `P_h`
and rewards `r_h` depend on the stage `h`, an episode lasts `H` stages, and policies are
deterministic and stage-dependent. It defines policy values `V^π_h`, optimal values `V*_h`, and
the optimistic value iteration of UCB-VI (their Equation 0.3) with transition estimates `P̂_h`
and bonuses `b_h`, truncated at `H`, and proves

* optimism (their Lemma 7.4): if `|(P̂_h - P_h) V*_{h+1}| ≤ b_h`, the optimistic values dominate
  `V*`;
* the truncated simulation inequality (their Equation 0.4): the optimistic value minus the value
  of the greedy policy is at most the sum over stages of the expected bonus plus the expected
  model error `(P̂_h - P_h) V̂_{h+1}` along the greedy policy.
-/

@[expose] public section

noncomputable section

namespace Rlib

/-- Downward induction over the stages: a property that holds from `H` on and passes from
`h + 1` to `h` below `H` holds at every stage. -/
theorem stage_induction {P : ℕ → Prop} (H : ℕ) (hbase : ∀ h, H ≤ h → P h)
    (hstep : ∀ h, h < H → P (h + 1) → P h) (h : ℕ) : P h := by
  induction hk : H - h generalizing h with
  | zero => exact hbase h (by omega)
  | succ k ih => exact hstep h (by omega) (ih (h + 1) (by omega))

/-- An episodic MDP with stage-dependent transitions and rewards. -/
structure EpisodicMDP (S A : Type*) where
  /-- The successor distribution at stage `h` after action `a` in state `s`. -/
  transition : ℕ → S → A → PMF S
  /-- The reward at stage `h` for action `a` in state `s`. -/
  reward : ℕ → S → A → ℝ

/-- A deterministic stage-dependent policy. -/
abbrev EpisodicPolicy (S A : Type*) := ℕ → S → A

namespace EpisodicMDP

variable {S A : Type*} [Fintype S]

/-- The value `V^π_h` of a deterministic policy over the stages `h, …, H - 1`. -/
def value (M : EpisodicMDP S A) (π : EpisodicPolicy S A) (H : ℕ) (h : ℕ) (s : S) : ℝ :=
  if h < H then M.reward h s (π h s) + expect (M.transition h s (π h s)) (M.value π H (h + 1))
  else 0
termination_by H - h

theorem value_of_lt (M : EpisodicMDP S A) (π : EpisodicPolicy S A) {H h : ℕ} (hh : h < H)
    (s : S) : M.value π H h s =
      M.reward h s (π h s) + expect (M.transition h s (π h s)) (M.value π H (h + 1)) := by
  rw [value]; simp only [hh, ↓reduceIte]

theorem value_of_le (M : EpisodicMDP S A) (π : EpisodicPolicy S A) {H h : ℕ} (hh : H ≤ h)
    (s : S) : M.value π H h s = 0 := by
  rw [value]; simp only [not_lt.mpr hh, ↓reduceIte]

/-- With nonnegative rewards, values are nonnegative. -/
theorem value_nonneg (M : EpisodicMDP S A) (hr : ∀ h s a, 0 ≤ M.reward h s a)
    (π : EpisodicPolicy S A) (H h : ℕ) (s : S) : 0 ≤ M.value π H h s := by
  revert s
  refine stage_induction (P := fun h => ∀ s, 0 ≤ M.value π H h s) H
    (fun h hh s => (M.value_of_le π hh s).ge) (fun h hh ih s => ?_) h
  rw [M.value_of_lt π hh]
  have := expect_mono (M.transition h s (π h s)) (f := fun _ => 0) ih
  rw [expect_zero] at this
  linarith [hr h s (π h s)]

variable [Fintype A] [Nonempty A]

/-- The optimal value `V*_h` over the stages `h, …, H - 1`. -/
def optValue (M : EpisodicMDP S A) (H : ℕ) (h : ℕ) (s : S) : ℝ :=
  if h < H then Finset.univ.sup' Finset.univ_nonempty fun a =>
    M.reward h s a + expect (M.transition h s a) (M.optValue H (h + 1))
  else 0
termination_by H - h

theorem optValue_of_lt (M : EpisodicMDP S A) {H h : ℕ} (hh : h < H) (s : S) :
    M.optValue H h s = Finset.univ.sup' Finset.univ_nonempty fun a =>
      M.reward h s a + expect (M.transition h s a) (M.optValue H (h + 1)) := by
  rw [optValue]; simp only [hh, ↓reduceIte]

theorem optValue_of_le (M : EpisodicMDP S A) {H h : ℕ} (hh : H ≤ h) (s : S) :
    M.optValue H h s = 0 := by
  rw [optValue]; simp only [not_lt.mpr hh, ↓reduceIte]

/-- The optimal action value `Q*_h (s, a) = r_h (s, a) + P_h V*_{h+1}`. -/
def optQ (M : EpisodicMDP S A) (H h : ℕ) (s : S) (a : A) : ℝ :=
  M.reward h s a + expect (M.transition h s a) (M.optValue H (h + 1))

theorem optQ_le_optValue (M : EpisodicMDP S A) {H h : ℕ} (hh : h < H) (s : S) (a : A) :
    M.optQ H h s a ≤ M.optValue H h s := by
  rw [M.optValue_of_lt hh]
  exact Finset.le_sup' (fun a => M.reward h s a + expect (M.transition h s a)
    (M.optValue H (h + 1))) (Finset.mem_univ a)

/-- With nonnegative rewards, optimal values are nonnegative. -/
theorem optValue_nonneg (M : EpisodicMDP S A) (hr : ∀ h s a, 0 ≤ M.reward h s a) (H h : ℕ)
    (s : S) : 0 ≤ M.optValue H h s := by
  revert s
  refine stage_induction (P := fun h => ∀ s, 0 ≤ M.optValue H h s) H
    (fun h hh s => (M.optValue_of_le hh s).ge) (fun h hh ih s => ?_) h
  obtain ⟨a₀⟩ := ‹Nonempty A›
  refine le_trans ?_ (M.optQ_le_optValue hh s a₀)
  have := expect_mono (M.transition h s a₀) (f := fun _ => 0) ih
  rw [expect_zero] at this
  simp only [optQ]
  linarith [hr h s a₀]

/-- With rewards at most one, `V*_h ≤ H - h` for `h ≤ H`. -/
theorem optValue_le (M : EpisodicMDP S A) (hr : ∀ h s a, M.reward h s a ≤ 1) {H h : ℕ}
    (hh : h ≤ H) (s : S) : M.optValue H h s ≤ (H : ℝ) - h := by
  revert hh s
  refine stage_induction (P := fun h => h ≤ H → ∀ s, M.optValue H h s ≤ (H : ℝ) - h) H
    (fun h hh hh' s => by
      rw [M.optValue_of_le hh, show h = H by omega]; simp) (fun h hh ih _ s => ?_) h
  rw [M.optValue_of_lt hh]
  refine Finset.sup'_le _ _ fun a _ => ?_
  have := expect_mono (M.transition h s a) (g := fun _ => (H : ℝ) - (h + 1 : ℕ)) (ih hh)
  rw [expect_const] at this
  push_cast at this
  linarith [hr h s a]

/-- The optimal value dominates the value of every deterministic policy. -/
theorem value_le_optValue (M : EpisodicMDP S A) (π : EpisodicPolicy S A) (H h : ℕ) (s : S) :
    M.value π H h s ≤ M.optValue H h s := by
  revert s
  refine stage_induction (P := fun h => ∀ s, M.value π H h s ≤ M.optValue H h s) H
    (fun h hh s => by rw [M.value_of_le π hh, M.optValue_of_le hh]) (fun h hh ih s => ?_) h
  rw [M.value_of_lt π hh]
  refine le_trans ?_ (M.optQ_le_optValue hh s (π h s))
  simp only [optQ]
  have := expect_mono (M.transition h s (π h s)) ih
  linarith

/-! ### Optimistic value iteration -/

/-- An action maximizing a function of the action. -/
def argmaxAction (f : A → ℝ) : A :=
  Classical.choose (Finset.exists_max_image Finset.univ f Finset.univ_nonempty)

omit [Fintype S] in
theorem le_argmaxAction (f : A → ℝ) (a : A) : f a ≤ f (argmaxAction f) :=
  (Classical.choose_spec (Finset.exists_max_image Finset.univ f Finset.univ_nonempty)).2 a
    (Finset.mem_univ a)

/-- The optimistic value `V̂_h` of UCB-VI for transition estimates `Phat` and bonuses `b`: value
iteration on `r_h + b_h` with `P̂_h`, truncated at `H`. -/
def ucbValue (M : EpisodicMDP S A) (Phat : ℕ → S → A → PMF S) (b : ℕ → S → A → ℝ) (H : ℕ)
    (h : ℕ) (s : S) : ℝ :=
  if h < H then Finset.univ.sup' Finset.univ_nonempty fun a =>
    min (M.reward h s a + b h s a + expect (Phat h s a) (M.ucbValue Phat b H (h + 1))) H
  else 0
termination_by H - h

/-- The optimistic action value `Q̂_h (s, a) = min (r_h + b_h + P̂_h V̂_{h+1}, H)`. -/
def ucbQ (M : EpisodicMDP S A) (Phat : ℕ → S → A → PMF S) (b : ℕ → S → A → ℝ) (H h : ℕ) (s : S)
    (a : A) : ℝ :=
  min (M.reward h s a + b h s a + expect (Phat h s a) (M.ucbValue Phat b H (h + 1))) H

/-- The greedy policy of the optimistic action values. -/
def ucbPolicy (M : EpisodicMDP S A) (Phat : ℕ → S → A → PMF S) (b : ℕ → S → A → ℝ) (H : ℕ) :
    EpisodicPolicy S A := fun h s => argmaxAction (M.ucbQ Phat b H h s)

theorem ucbValue_of_lt (M : EpisodicMDP S A) (Phat : ℕ → S → A → PMF S) (b : ℕ → S → A → ℝ)
    {H h : ℕ} (hh : h < H) (s : S) :
    M.ucbValue Phat b H h s = M.ucbQ Phat b H h s (M.ucbPolicy Phat b H h s) := by
  rw [ucbValue]; simp only [hh, ↓reduceIte]
  exact le_antisymm (Finset.sup'_le _ _ fun a _ => le_argmaxAction (M.ucbQ Phat b H h s) a)
    (Finset.le_sup' (M.ucbQ Phat b H h s) (Finset.mem_univ _))

theorem ucbValue_of_le (M : EpisodicMDP S A) (Phat : ℕ → S → A → PMF S) (b : ℕ → S → A → ℝ)
    {H h : ℕ} (hh : H ≤ h) (s : S) : M.ucbValue Phat b H h s = 0 := by
  rw [ucbValue]; simp only [not_lt.mpr hh, ↓reduceIte]

/-- **Optimism (Agarwal, Jiang, Kakade, and Sun, Lemma 7.4).** With rewards in `[0, 1]`, if the
bonuses dominate the model error on `V*`, `|(P̂_h - P_h) V*_{h+1}| ≤ b_h`, then the optimistic
values dominate the optimal values at every stage. -/
theorem optValue_le_ucbValue (M : EpisodicMDP S A)
    (hr : ∀ h s a, M.reward h s a ∈ Set.Icc (0 : ℝ) 1) (Phat : ℕ → S → A → PMF S)
    (b : ℕ → S → A → ℝ) (H : ℕ)
    (hb : ∀ h, h < H → ∀ s a, |expect (Phat h s a) (M.optValue H (h + 1)) -
      expect (M.transition h s a) (M.optValue H (h + 1))| ≤ b h s a) (h : ℕ) (s : S) :
    M.optValue H h s ≤ M.ucbValue Phat b H h s := by
  revert s
  refine stage_induction (P := fun h => ∀ s, M.optValue H h s ≤ M.ucbValue Phat b H h s) H
    (fun h hh s => by rw [M.optValue_of_le hh, M.ucbValue_of_le Phat b hh]) (fun h hh ih s => ?_) h
  rw [M.optValue_of_lt hh]
  refine Finset.sup'_le _ _ fun a _ => ?_
  rw [M.ucbValue_of_lt Phat b hh]
  refine le_trans ?_ (le_argmaxAction (M.ucbQ Phat b H h s) a)
  simp only [ucbQ]
  refine le_min ?_ ?_
  · have hmono := expect_mono (Phat h s a) ih
    have := (abs_le.mp (hb h hh s a)).1
    linarith
  · have := expect_mono (M.transition h s a) (g := fun _ => (H : ℝ) - (h + 1 : ℕ))
      (M.optValue_le (fun h s a => (hr h s a).2) (show h + 1 ≤ H by omega))
    rw [expect_const] at this
    push_cast at this
    linarith [(hr h s a).2]

omit [Fintype A] [Nonempty A] in
/-- The distribution of the state at stage `h` when `π` runs from `s₀`. -/
def stateDist (M : EpisodicMDP S A) (π : EpisodicPolicy S A) (s₀ : S) : ℕ → PMF S
  | 0 => PMF.pure s₀
  | h + 1 => (M.stateDist π s₀ h).bind fun s => M.transition h s (π h s)

/-- **Truncated simulation inequality (Agarwal, Jiang, Kakade, and Sun, Equation 0.4).** The
optimistic value at the start minus the value of the greedy policy `π` is at most the sum over
stages of the expected bonus plus the expected model error `(P̂_h - P_h) V̂_{h+1}` at the state
of stage `h` under `π`. -/
theorem ucbValue_sub_value_le (M : EpisodicMDP S A) (Phat : ℕ → S → A → PMF S)
    (b : ℕ → S → A → ℝ) (H : ℕ) (s₀ : S) :
    M.ucbValue Phat b H 0 s₀ - M.value (M.ucbPolicy Phat b H) H 0 s₀ ≤
      ∑ h ∈ Finset.range H, expect (M.stateDist (M.ucbPolicy Phat b H) s₀ h) (fun s =>
        b h s (M.ucbPolicy Phat b H h s) +
          (expect (Phat h s (M.ucbPolicy Phat b H h s)) (M.ucbValue Phat b H (h + 1)) -
            expect (M.transition h s (M.ucbPolicy Phat b H h s))
              (M.ucbValue Phat b H (h + 1)))) := by
  set π := M.ucbPolicy Phat b H
  set Vhat := M.ucbValue Phat b H
  set V := M.value π H
  set d := M.stateDist π s₀
  set G : ℕ → ℝ := fun h => expect (d h) (fun s => b h s (π h s) +
    (expect (Phat h s (π h s)) (Vhat (h + 1)) - expect (M.transition h s (π h s)) (Vhat (h + 1))))
  set D : ℕ → ℝ := fun h => expect (d h) (fun s => Vhat h s - V h s)
  have key : ∀ h, h ≤ H → D h ≤ ∑ j ∈ Finset.Ico h H, G j := by
    refine stage_induction (P := fun h => h ≤ H → D h ≤ ∑ j ∈ Finset.Ico h H, G j) H
      (fun h hh hh' => ?_) (fun h hh ih _ => ?_)
    · rw [show h = H by omega]
      simp only [D, Finset.Ico_self, Finset.sum_empty]
      have h0 (s : S) : Vhat H s - V H s = 0 := by
        rw [show Vhat H s = 0 from M.ucbValue_of_le Phat b le_rfl s,
          show V H s = 0 from M.value_of_le π le_rfl s, sub_zero]
      simp only [h0, expect_zero, le_refl]
    · have hpt (s : S) : Vhat h s - V h s ≤ (b h s (π h s) +
          (expect (Phat h s (π h s)) (Vhat (h + 1)) -
            expect (M.transition h s (π h s)) (Vhat (h + 1)))) +
          expect (M.transition h s (π h s)) (fun t => Vhat (h + 1) t - V (h + 1) t) := by
        rw [show Vhat h s = _ from M.ucbValue_of_lt Phat b hh s,
          show V h s = _ from M.value_of_lt π hh s, expect_sub]
        have := min_le_left (M.reward h s (π h s) + b h s (π h s) +
          expect (Phat h s (π h s)) (Vhat (h + 1))) (H : ℝ)
        simp only [ucbQ] at this ⊢
        linarith
      have hstep : D h ≤ G h + D (h + 1) := by
        have hb := expect_mono (d h) hpt
        rw [expect_add] at hb
        simp only [D, d, stateDist, expect_bind]
        exact hb
      rw [Finset.sum_eq_sum_Ico_succ_bot hh]
      linarith [ih (by omega)]
  have h0 := key 0 (Nat.zero_le H)
  simp only [D, d, stateDist, expect_pure] at h0
  rw [Finset.range_eq_Ico]
  exact h0

end EpisodicMDP

end Rlib
