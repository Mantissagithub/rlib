module

public import Rlib.MDP.FiniteHorizon
public import Rlib.MDP.PolicyEvaluation
public import Mathlib.Analysis.SpecificLimits.Normed

/-! # Infinite discounted returns and limits of finite expected returns -/

@[expose] public section

noncomputable section

open scoped Topology

namespace Rlib.MDP

variable {S A : Type*}

/-- The infinite discounted sum of stored expected rewards along a trajectory.
Summability is guaranteed below for finite types and a discount in `[0, 1)`. -/
def infiniteReturn (m : MDP S A) (γ : ℝ) (s : S) (ω : InfiniteTrajectory S A) : ℝ :=
  ∑' n, γ ^ n * m.reward (ω.stateBefore s n) (ω n).1

/-- A finite prefix return is the corresponding partial sum, for any real discount. -/
theorem discountedReturn_prefix_eq_sum (m : MDP S A) (γ : ℝ) (s : S)
    (ω : InfiniteTrajectory S A) (n : ℕ) :
    m.discountedReturn γ n s (ω.prefix n) =
      ∑ k ∈ Finset.range n, γ ^ k * m.reward (ω.stateBefore s k) (ω k).1 := by
  induction n generalizing s ω with
  | zero => simp [discountedReturn]
  | succ n ih =>
    change m.reward s (ω 0).1 +
      γ * m.discountedReturn γ n (ω 0).2 (InfiniteTrajectory.prefix n (fun k => ω (k + 1))) = _
    rw [ih, Finset.sum_range_succ']
    simp only [pow_zero, one_mul, InfiniteTrajectory.stateBefore]
    rw [Finset.mul_sum, add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    cases k <;> simp only [pow_succ] <;> ring

/-- Finite state and action spaces make the discounted reward series absolutely summable. -/
theorem summable_norm_discountedReward [Fintype S] [Fintype A] (m : MDP S A)
    {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (s : S) (ω : InfiniteTrajectory S A) :
    Summable (fun n => ‖γ ^ n * m.reward (ω.stateBefore s n) (ω n).1‖) := by
  apply ((summable_geometric_of_lt_one hγ0 hγ1).mul_right ‖m.reward‖).of_nonneg_of_le
    (fun _ => norm_nonneg _) (fun n => ?_)
  rw [norm_mul, norm_pow, Real.norm_of_nonneg hγ0]
  exact mul_le_mul_of_nonneg_left
    ((norm_le_pi_norm _ _).trans (norm_le_pi_norm _ _)) (pow_nonneg hγ0 n)

/-- Finite prefix returns converge to the infinite discounted return. -/
theorem tendsto_discountedReturn [Fintype S] [Fintype A] (m : MDP S A)
    {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (s : S) (ω : InfiniteTrajectory S A) :
    Filter.Tendsto (fun n => m.discountedReturn γ n s (ω.prefix n)) Filter.atTop
      (𝓝 (m.infiniteReturn γ s ω)) := by
  simpa only [discountedReturn_prefix_eq_sum, infiniteReturn] using
    (m.summable_norm_discountedReward hγ0 hγ1 s ω).of_norm.hasSum.tendsto_sum_nat

/-- Every finite return is bounded by the geometric reward bound. -/
theorem norm_discountedReturn_le [Fintype S] [Fintype A] (m : MDP S A)
    {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (n : ℕ) (s : S)
    (t : FiniteTrajectory S A n) :
    ‖m.discountedReturn γ n s t‖ ≤ ‖m.reward‖ / (1 - γ) := by
  have hd : 0 < 1 - γ := sub_pos.mpr hγ1
  induction n generalizing s with
  | zero => simpa [discountedReturn] using div_nonneg (norm_nonneg m.reward) hd.le
  | succ n ih =>
    calc
      ‖m.discountedReturn γ (n + 1) s t‖ ≤
          ‖m.reward s (t 0).1‖ + γ * ‖m.discountedReturn γ n (t 0).2 (Fin.tail t)‖ := by
        simpa only [discountedReturn, norm_mul, Real.norm_of_nonneg hγ0] using
          norm_add_le (m.reward s (t 0).1) (γ * m.discountedReturn γ n (t 0).2 (Fin.tail t))
      _ ≤ ‖m.reward‖ + γ * (‖m.reward‖ / (1 - γ)) :=
        add_le_add ((norm_le_pi_norm _ _).trans (norm_le_pi_norm _ _))
          (mul_le_mul_of_nonneg_left (ih _ _) hγ0)
      _ = ‖m.reward‖ / (1 - γ) := by field_simp; ring

/-- Infinite returns satisfy the same geometric reward bound as finite returns. -/
theorem norm_infiniteReturn_le [Fintype S] [Fintype A] (m : MDP S A)
    {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (s : S) (ω : InfiniteTrajectory S A) :
    ‖m.infiniteReturn γ s ω‖ ≤ ‖m.reward‖ / (1 - γ) := by
  exact le_of_tendsto (m.tendsto_discountedReturn hγ0 hγ1 s ω).norm
    (Filter.Eventually.of_forall fun n => m.norm_discountedReturn_le hγ0 hγ1 n s (ω.prefix n))

/-- Expected finite returns converge as value functions to the policy's Bellman value. -/
theorem tendsto_expectedReturn [Fintype S] [Fintype A] (m : MDP S A)
    (π : StationaryPolicy S A) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) :
    Filter.Tendsto (m.expectedReturn π γ) Filter.atTop (𝓝 (m.policyValue π hγ0 hγ1)) := by
  have h := m.oneStepValue_contractingWith π hγ0 hγ1
  rw [h.fixedPoint_unique (m.oneStepValue_policyValue π hγ0 hγ1)]
  change Filter.Tendsto (fun n => m.expectedReturn π γ n) _ _
  simpa only [expectedReturn_eq_iterate] using h.tendsto_iterate_fixedPoint (fun _ => 0)

end Rlib.MDP
