module

import Rlib

open Rlib MeasureTheory

example {S A : Type*} [MeasurableSpace S] [MeasurableSpace A]
    [Finite S] [MeasurableSingletonClass S] (m : MDP S A)
    (π : StationaryPolicy S A) (s : S) : IsProbabilityMeasure (m.pathMeasure π s) :=
  inferInstance

example {S A : Type*} [MeasurableSpace S] [MeasurableSpace A]
    [Finite S] [Finite A] [MeasurableSingletonClass S] [MeasurableSingletonClass A]
    (m : MDP S A) (π : StationaryPolicy S A) (s : S) :
    (m.pathMeasure π s).map (InfiniteTrajectory.prefix 0) = Measure.dirac Fin.elim0 := by
  rw [MDP.map_prefix_pathMeasure, MDP.trajectoryLaw, PMF.toMeasure_pure]

private noncomputable def nextState : PMF Bool :=
  PMF.ofFintype (fun s => ENNReal.ofReal (if s then 1 / 4 else 3 / 4)) (by
    rw [Fintype.sum_bool]
    norm_num [← ENNReal.ofReal_add])

private noncomputable def stateDependent : MDP Bool Unit where
  transition s _ := if s then PMF.pure false else nextState
  reward s _ := if s then 4 else 0

private noncomputable def onlyAction : StationaryPolicy Bool Unit := fun _ => PMF.pure ()

example : stateDependent.pathMeasure onlyAction false
    {ω | ω 0 = ((), true) ∧ ω 1 = ((), false)} = 1 / 4 := by
  let t : FiniteTrajectory Bool Unit 2 :=
    Fin.cons ((), true) (Fin.cons ((), false) Fin.elim0)
  have hevent : {ω : InfiniteTrajectory Bool Unit | ω 0 = ((), true) ∧ ω 1 = ((), false)} =
      InfiniteTrajectory.prefix 2 ⁻¹' {t} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · rintro ⟨h0, h1⟩
      funext i
      fin_cases i <;> assumption
    · intro h
      exact ⟨congrFun h 0, congrFun h 1⟩
  have hpref : Measurable (InfiniteTrajectory.prefix (S := Bool) (A := Unit) 2) :=
    measurable_pi_iff.mpr fun i => measurable_pi_apply (i : ℕ)
  rw [hevent, ← Measure.map_apply hpref
    (measurableSet_singleton t), MDP.map_prefix_pathMeasure,
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton t)]
  simp only [MDP.trajectoryLaw, onlyAction, stateDependent, PMF.pure_bind, PMF.map,
    Function.comp_apply, PMF.bind_bind]
  norm_num [t, nextState, PMF.bind_apply, tsum_fintype, PMF.pure_apply,
    ← ENNReal.ofReal_mul, Fin.cons_inj]
  norm_num [ENNReal.ofReal_div_of_pos]
