module

import Rlib

open Rlib Filter Topology

private noncomputable def model : MDP Unit Bool where
  transition _ _ := PMF.pure ()
  reward _ a := if a then 2 else 0

private def qStar : Unit → Bool → ℝ := fun _ a => if a then 4 else 2

private theorem qStar_fixed : model.qBellmanOperator (1 / 2) qStar = qStar := by
  funext s a
  cases a <;> norm_num [MDP.qBellmanOperator, MDP.oneStepActionValue, model, qStar, qMax]

private def visits (n : ℕ) : Unit × Bool := ((), decide (n % 2 = 0))

private noncomputable def observe (n : ℕ) : ℝ × Unit :=
  (if (visits n).2 then 2 else 0, ())

private theorem visits_not_summable (s : Unit) (a : Bool) :
    ¬Summable fun n => visitStep (fun _ => (1 / 2 : ℝ)) visits n s a := by
  intro h
  have hsub : Tendsto (fun k : ℕ => 2 * k + (if a then 0 else 1)) atTop atTop :=
    tendsto_atTop_mono (fun k => by simp only [id]; split_ifs <;> omega) tendsto_id
  have hconst : (fun k : ℕ => visitStep (fun _ => (1 / 2 : ℝ)) visits
      (2 * k + (if a then 0 else 1)) s a) = fun _ => 1 / 2 := by
    funext k
    cases a <;> simp [visitStep, visits, Nat.add_mod]
  have hlim := h.tendsto_atTop_zero.comp hsub
  rw [Function.comp_def, hconst] at hlim
  have := tendsto_nhds_unique hlim tendsto_const_nhds
  norm_num at this

example (q₀ : Unit → Bool → ℝ) :
    Tendsto (qLearningAsync (fun _ => 1 / 2) (1 / 2) visits observe q₀) atTop (𝓝 qStar) := by
  refine model.tendsto_qLearningAsync (R := 2) (fun _ => by norm_num) (fun _ => by norm_num)
    (by norm_num) (by norm_num) visits observe (fun n => ?_) visits_not_summable q₀ qStar
    qStar_fixed fun s a => ⟨0, ?_⟩
  · unfold observe
    split_ifs <;> norm_num
  · have hzero (k : ℕ) : visitStep (fun _ => (1 / 2 : ℝ)) visits k s a *
        (qLearningTarget (1 / 2) (qLearningAsync (fun _ => 1 / 2) (1 / 2) visits observe q₀ k)
          (observe k) - model.qBellmanOperator (1 / 2)
            (qLearningAsync (fun _ => 1 / 2) (1 / 2) visits observe q₀ k) s a) = 0 := by
      unfold visitStep
      split_ifs with hv
      · have ha : a = (visits k).2 := congrArg Prod.snd hv
        subst ha
        simp [qLearningTarget, MDP.qBellmanOperator, MDP.oneStepActionValue, model, observe]
      · simp
    simp_rw [hzero, Finset.sum_const_zero]
    exact tendsto_const_nhds

example (n : ℕ) :
    ‖qLearningAsync (fun _ => 1 / 2) (1 / 2) visits observe (fun _ _ => 0) n‖ ≤ 4 := by
  have h := norm_qLearningAsync_le (α := fun _ => 1 / 2) (γ := 1 / 2) (R := 2)
    (fun _ => by norm_num) (fun _ => by norm_num) (by norm_num) (by norm_num) visits observe
    (fun n => by unfold observe; split_ifs <;> norm_num) (fun _ _ => 0) n
  norm_num at h
  exact h
