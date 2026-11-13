module

import Rlib

open Rlib

/-- The recursion lemma on `δ t = 1 / (t + 1)`, which drops by at least `δ t ^ 2 / 2` and starts
at `1 ≤ 2`. -/
example (t : ℕ) : 1 / ((t : ℝ) + 1) ≤ 1 / (1 / 2 * ((t : ℝ) + 1)) := by
  refine le_one_div_mul_of_le_sub_mul_sq (δ := fun n : ℕ => 1 / ((n : ℝ) + 1)) (κ := 1 / 2)
    (by norm_num) (fun n => ?_) (fun n _ => ?_) (by norm_num) t
  · push_cast
    gcongr
    linarith
  · push_cast
    have hx : (0 : ℝ) < n + 1 := by positivity
    rw [show 1 / ((n : ℝ) + 1) - 1 / 2 * (1 / ((n : ℝ) + 1)) ^ 2 =
      (2 * n + 1) / (2 * (n + 1) ^ 2) by field_simp; ring]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith

private noncomputable def model : MDP Unit Unit where
  transition _ _ := PMF.pure ()
  reward _ _ := 1

private theorem value_eq (π : StationaryPolicy Unit Unit) :
    model.policyValue π (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) = fun _ => 2 := by
  symm
  apply MDP.eq_policyValue_of_fixedPoint
  funext s
  change expect (π s) (fun _ => (1 : ℝ) + 1 / 2 * expect (PMF.pure ()) fun _ => (2 : ℝ)) = 2
  rw [expect_pure, expect_const]
  norm_num

private theorem prob_one (θ : Unit → Unit → ℝ) (s : Unit) :
    (softmaxPolicy θ s ()).toReal = 1 := by
  rw [softmaxPolicy_apply]
  simp

private theorem visit_one (π : StationaryPolicy Unit Unit) :
    model.weightedVisitation π (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) (fun _ => 1) () =
      1 := by
  simpa [MDP.weightedVisitation] using
    model.sum_discountedVisitation π (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) ()

/-- Mei et al., Theorem 4, with a single action: `c = D = M = 1` and `|S| = 1`. -/
example (t : ℕ) (ht : 1 ≤ t) :
    ∑ s₀ : Unit, (fun _ => (1 : ℝ)) s₀ *
        (model.policyValue (fun _ => PMF.pure ()) (by norm_num : (0 : ℝ) ≤ 1 / 2)
          (by norm_num) s₀ -
        model.policyValue (softmaxPolicy (model.pgScores (by norm_num : (0 : ℝ) ≤ 1 / 2)
          (by norm_num) (fun _ => 1) ((1 - 1 / 2) ^ 3 / 8) (fun _ _ => 0) (t - 1)))
            (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) s₀) ≤
      16 * Fintype.card Unit / (1 ^ 2 * (1 - 1 / 2) ^ 6 * t) * 1 ^ 2 * 1 :=
  model.sum_sub_policyValue_pg_le (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    (fun _ _ => by norm_num [model]) (fun _ => one_pos) (by simp) (fun _ => zero_le_one)
    (by simp) (fun _ _ => 0) (fun _ => ()) (fun π s => by rw [value_eq, value_eq])
    one_pos (fun t s => (prob_one _ s).ge) (fun s => by rw [visit_one, one_mul])
    (fun s => by norm_num) t ht
