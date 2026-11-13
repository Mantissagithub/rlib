module

import Rlib

open Rlib

/-- The recursion lemma on `δ t = 1 / (t + 1)`, which drops by at least `δ t ^ 2 / 2`. -/
example (t : ℕ) (ht : 0 < t) : 1 / ((t : ℝ) + 1) ≤ 1 / (1 / 2 * t) := by
  refine le_one_div_mul_of_le_sub_mul_sq (δ := fun n : ℕ => 1 / ((n : ℝ) + 1)) (κ := 1 / 2)
    (by norm_num) (fun n => ?_) (fun n _ => ?_) ht
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

private theorem prob_one (θ : Unit → Unit → ℝ) (s : Unit) :
    (softmaxPolicy θ s ()).toReal = 1 := by
  rw [softmaxPolicy_apply]
  simp

private theorem visit_one (π : StationaryPolicy Unit Unit) :
    model.weightedVisitation π (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) (fun _ => 1) () =
      1 := by
  simpa [MDP.weightedVisitation] using
    model.sum_discountedVisitation π (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) ()

/-- The rate theorem applies with `c = C = 1` when there is a single action. -/
example (T : ℕ) (hT : 0 < T) :
    1 * (model.policyValue (fun _ => PMF.pure ()) (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num) () -
      model.policyValue (softmaxPolicy (model.pgScores (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num) (fun _ => 1) ((1 - 1 / 2) ^ 3 / (12 * 1)) (fun _ _ => 0) T))
          (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) ()) ≤
      24 * 1 * 1 ^ 2 * 1 / ((1 - 1 / 2) ^ 3 * 1 ^ 2 * T) := by
  have h := model.sum_sub_policyValue_pg_le (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    (R := 1) one_pos (fun _ _ => by norm_num [model]) (μ := fun _ => 1)
    (fun _ => zero_le_one) (by simp) (fun _ _ => 0) (fun _ => ()) (c := 1) (C := 1) one_pos
    one_pos (fun t s => (prob_one _ s).ge) (fun t s => by rw [visit_one, visit_one, one_mul]) hT
  simpa using h
