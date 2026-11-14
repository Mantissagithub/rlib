module

import Rlib

open Rlib

/-- With the exact model and no bonus, optimistic value iteration dominates the optimal values
(Agarwal, Jiang, Kakade, and Sun, Lemma 7.4). -/
example {S A : Type} [Fintype S] [Fintype A] [Nonempty A] (M : EpisodicMDP S A)
    (hr : ∀ h s a, M.reward h s a ∈ Set.Icc (0 : ℝ) 1) (H h : ℕ) (s : S) :
    M.optValue H h s ≤ M.ucbValue M.transition (fun _ _ _ => 0) H h s :=
  M.optValue_le_ucbValue hr _ _ H (fun h _ s a => by simp) h s

/-- The value of any policy is at most `V*`, which is at most the horizon. -/
example {S A : Type} [Fintype S] [Fintype A] [Nonempty A] (M : EpisodicMDP S A)
    (hr : ∀ h s a, M.reward h s a ∈ Set.Icc (0 : ℝ) 1) (π : EpisodicPolicy S A) (H : ℕ) (s : S) :
    M.value π H 0 s ≤ H := by
  have h1 := M.value_le_optValue π H 0 s
  have h2 := M.optValue_le (fun h s a => (hr h s a).2) (Nat.zero_le H) s
  simp at h2
  linarith
