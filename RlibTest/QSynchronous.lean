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

private noncomputable def observe (_ : ℕ) (_ : Unit) (a : Bool) : ℝ × Unit :=
  (if a then 2 else 0, ())

example (q₀ : Unit → Bool → ℝ) :
    Tendsto (qLearningSync (fun _ => 1 / 2) (1 / 2) observe q₀) atTop (𝓝 qStar) := by
  refine model.tendsto_qLearningSync (fun _ => by norm_num) (fun _ => by norm_num)
    (by rw [summable_const_iff]; norm_num) (by norm_num) (by norm_num) observe q₀ qStar
    qStar_fixed ?_
  simp [qLearningTarget, MDP.qBellmanOperator, MDP.oneStepActionValue, model, observe]
