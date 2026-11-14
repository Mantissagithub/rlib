module

public import Rlib.Episodic.Basic
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! # Counting visits

For trajectories `τ^k = (s^k_h, a^k_h)`, `N_h^k (s, a)` counts the episodes `i < k` that visit
`(s, a)` at stage `h`. This file proves Agarwal, Jiang, Kakade, and Sun, Lemma 7.5:
`∑_{k < K} ∑_{h < H} 1 / √(N_h^k (s^k_h, a^k_h)) ≤ 2 H √(|S| |A| K)`. A first visit has count
zero, and its term is `1 / √0 = 0` here; the regret analysis accounts for first visits
separately.
-/

@[expose] public section

noncomputable section

namespace Rlib

/-- `∑_{j < n} 1 / √j ≤ 2 √n`, with the term at `j = 0` equal to zero. -/
theorem sum_range_one_div_sqrt_le (n : ℕ) :
    ∑ j ∈ Finset.range n, 1 / Real.sqrt j ≤ 2 * Real.sqrt n := by
  -- Prove the sharper `≤ 2 √(n - 1)` for `n ≥ 1`.
  have key : ∀ n : ℕ, ∑ j ∈ Finset.range (n + 1), 1 / Real.sqrt j ≤ 2 * Real.sqrt n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ]
      have hn : (0 : ℝ) < n + 1 := by positivity
      set a := Real.sqrt (n + 1 : ℕ)
      set c := Real.sqrt n
      have ha : 0 < a := Real.sqrt_pos.mpr (by exact_mod_cast Nat.succ_pos n)
      have hc0 : 0 ≤ c := Real.sqrt_nonneg _
      have hca : c ≤ a := Real.sqrt_le_sqrt (by push_cast; linarith)
      have ha2 : a ^ 2 = n + 1 := by
        simp only [a]; rw [Real.sq_sqrt (by positivity)]; push_cast; ring
      have hc2 : c ^ 2 = n := Real.sq_sqrt (by positivity)
      -- `1 / a ≤ 2 (a - c)` because `(a - c) (a + c) = 1` and `a + c ≤ 2 a`.
      have hstep : 1 / a ≤ 2 * (a - c) := by
        rw [div_le_iff₀ ha]
        nlinarith
      linarith
  rcases n with _ | n
  · simp
  · refine (key n).trans ?_
    exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by push_cast; linarith)) (by norm_num)

variable {X : Type*} [DecidableEq X]

/-- The number of episodes `i < k` whose entry at stage `h` equals `x`. -/
def visitCount (τ : ℕ → ℕ → X) (k h : ℕ) (x : X) : ℕ :=
  ((Finset.range k).filter fun i => τ i h = x).card

/-- Grouping the terms of one stage by the visited entry. -/
theorem sum_visitCount_eq [Fintype X] (τ : ℕ → ℕ → X) (h : ℕ) (f : ℕ → ℝ) (K : ℕ) :
    ∑ k ∈ Finset.range K, f (visitCount τ k h (τ k h)) =
      ∑ x, ∑ j ∈ Finset.range (visitCount τ K h x), f j := by
  induction K with
  | zero => simp [visitCount]
  | succ K ih =>
    rw [Finset.sum_range_succ, ih]
    have hcount (x : X) : visitCount τ (K + 1) h x =
        visitCount τ K h x + if τ K h = x then 1 else 0 := by
      simp only [visitCount, Finset.range_add_one, Finset.filter_insert]
      split_ifs with hx
      · rw [Finset.card_insert_of_notMem (by simp)]
      · rfl
    simp only [hcount]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (τ K h)),
      ← Finset.add_sum_erase _ _ (Finset.mem_univ (τ K h))]
    have hrest : ∑ x ∈ Finset.univ.erase (τ K h),
        ∑ j ∈ Finset.range (visitCount τ K h x + if τ K h = x then 1 else 0), f j =
        ∑ x ∈ Finset.univ.erase (τ K h), ∑ j ∈ Finset.range (visitCount τ K h x), f j :=
      Finset.sum_congr rfl fun x hx => by
        simp only [(Finset.ne_of_mem_erase hx).symm, ↓reduceIte, add_zero]
    rw [hrest]
    simp only [↓reduceIte]
    rw [Finset.sum_range_succ]
    ring

/-- The counts at one stage add up to the number of episodes. -/
theorem sum_visitCount [Fintype X] (τ : ℕ → ℕ → X) (h K : ℕ) :
    ∑ x, visitCount τ K h x = K := by
  simp only [visitCount]
  rw [← Finset.card_eq_sum_card_fiberwise (fun i _ => Finset.mem_univ (τ i h))]
  simp

/-- **Counting bound (Agarwal, Jiang, Kakade, and Sun, Lemma 7.5).** For any trajectories with
entries in a finite type `X` (state-action pairs),
`∑_{k < K} ∑_{h < H} 1 / √(N_h^k) ≤ 2 H √(|X| K)`. -/
theorem sum_one_div_sqrt_visitCount_le [Fintype X] (τ : ℕ → ℕ → X) (H K : ℕ) :
    ∑ k ∈ Finset.range K, ∑ h ∈ Finset.range H, 1 / Real.sqrt (visitCount τ k h (τ k h)) ≤
      2 * H * Real.sqrt (Fintype.card X * K) := by
  rw [Finset.sum_comm]
  have hstage (h : ℕ) : ∑ k ∈ Finset.range K, 1 / Real.sqrt (visitCount τ k h (τ k h)) ≤
      2 * Real.sqrt (Fintype.card X * K) := by
    rw [sum_visitCount_eq τ h (fun n => 1 / Real.sqrt n) K]
    calc ∑ x, ∑ j ∈ Finset.range (visitCount τ K h x), 1 / Real.sqrt j
        ≤ ∑ x, 2 * Real.sqrt (visitCount τ K h x) :=
          Finset.sum_le_sum fun x _ => sum_range_one_div_sqrt_le _
      _ = 2 * ∑ x, Real.sqrt (visitCount τ K h x) := by rw [Finset.mul_sum]
      _ ≤ 2 * Real.sqrt (Fintype.card X * K) := by
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          apply Real.le_sqrt_of_sq_le
          have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.univ)
            (f := fun x => Real.sqrt (visitCount τ K h x))
          have hsq (x : X) : Real.sqrt (visitCount τ K h x) ^ 2 = visitCount τ K h x :=
            Real.sq_sqrt (by positivity)
          simp only [hsq, Finset.card_univ] at hcs
          have hsum : (∑ x, (visitCount τ K h x : ℝ)) = K := by
            exact_mod_cast sum_visitCount τ h K
          rw [hsum] at hcs
          exact hcs
  calc ∑ h ∈ Finset.range H, ∑ k ∈ Finset.range K, 1 / Real.sqrt (visitCount τ k h (τ k h))
      ≤ ∑ _h ∈ Finset.range H, 2 * Real.sqrt (Fintype.card X * K) :=
        Finset.sum_le_sum fun h _ => hstage h
    _ = _ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

end Rlib
