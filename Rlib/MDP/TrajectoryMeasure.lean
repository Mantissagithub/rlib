module

public import Rlib.MDP.FiniteHorizon
public import Mathlib.Probability.Kernel.IonescuTulcea.Traj

/-! # The probability law of an infinite trajectory under a fixed policy -/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Set Preorder

namespace Rlib.MDP

variable {S A : Type*}

private def stepLaw (m : MDP S A) (π : StationaryPolicy S A) (s : S) : PMF (A × S) :=
  (π s).bind fun a => (m.transition s a).map fun s' => (a, s')

private theorem trajectoryLaw_step (m : MDP S A) (π : StationaryPolicy S A)
    (n : ℕ) (s : S) :
    m.trajectoryLaw π (n + 1) s = (stepLaw m π s).bind fun e =>
      (m.trajectoryLaw π n e.2).map (Fin.cons e) := by
  simp [trajectoryLaw, stepLaw, PMF.bind_bind, Function.comp_def]

private theorem trajectoryLaw_one (m : MDP S A) (π : StationaryPolicy S A) (s : S) :
    m.trajectoryLaw π 1 s = (stepLaw m π s).map (fun e _ => e) := by
  rw [trajectoryLaw_step]
  simp only [trajectoryLaw, PMF.pure_map]
  change (stepLaw m π s).bind _ = (stepLaw m π s).bind _
  congr 1
  funext e
  congr 1
  funext i
  exact Fin.cases rfl (fun j => Fin.elim0 j) i

private theorem trajectoryLaw_append (m : MDP S A) (π : StationaryPolicy S A)
    (n : ℕ) (s : S) :
    m.trajectoryLaw π (n + 2) s = (m.trajectoryLaw π (n + 1) s).bind fun t =>
      (stepLaw m π (t (Fin.last n)).2).map (Fin.snoc t) := by
  induction n generalizing s with
  | zero =>
      rw [trajectoryLaw_step, trajectoryLaw_one, PMF.bind_map]
      congr 1
      funext e
      rw [trajectoryLaw_one, PMF.map_comp]
      congr 1
      funext e'
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp
      · have : j = 0 := Subsingleton.elim _ _
        subst j
        rfl
  | succ n ih =>
      rw [trajectoryLaw_step, trajectoryLaw_step m π (n + 1), PMF.bind_bind]
      congr 1
      funext e
      rw [ih, PMF.map_bind, PMF.bind_map]
      congr 1
      funext t
      simp only [Function.comp_apply, Fin.cons_last, PMF.map_comp]
      congr 1
      funext e'
      exact Fin.cons_snoc_eq_snoc_cons e t e'

variable [MeasurableSpace S] [MeasurableSpace A]

private def stepKernel [Finite S] [MeasurableSingletonClass S]
    (m : MDP S A) (π : StationaryPolicy S A) : Kernel S (A × S) where
  toFun s := (stepLaw m π s).toMeasure
  measurable' := measurable_of_finite _

private instance [Finite S] [MeasurableSingletonClass S]
    (m : MDP S A) (π : StationaryPolicy S A) : IsMarkovKernel (stepKernel m π) where
  isProbabilityMeasure s := by change IsProbabilityMeasure (stepLaw m π s).toMeasure; infer_instance

private def historyKernel [Finite S] [MeasurableSingletonClass S]
    (m : MDP S A) (π : StationaryPolicy S A) (n : ℕ) :
    Kernel (Finset.Iic n → A × S) (A × S) :=
  (stepKernel m π).comap (fun h => (h ⟨n, Finset.mem_Iic.mpr le_rfl⟩).2) (by fun_prop)

private instance [Finite S] [MeasurableSingletonClass S]
    (m : MDP S A) (π : StationaryPolicy S A) (n : ℕ) :
    IsMarkovKernel (historyKernel m π n) := by
  unfold historyKernel
  infer_instance

/-- The infinite trajectory law starts by sampling the first action and successor state,
then samples each next step from the last recorded state. -/
def pathMeasure [Finite S] [MeasurableSingletonClass S]
    (m : MDP S A) (π : StationaryPolicy S A) (s : S) : Measure (InfiniteTrajectory S A) := by
  let q (s : S) : PMF (A × S) :=
    (π s).bind fun a => (m.transition s a).map fun s' => (a, s')
  let K : Kernel S (A × S) := ⟨fun s => (q s).toMeasure, measurable_of_finite _⟩
  letI : IsMarkovKernel K := ⟨fun s => by
    change IsProbabilityMeasure (q s).toMeasure
    infer_instance⟩
  exact Kernel.trajMeasure (X := fun _ => A × S) (q s).toMeasure (fun n =>
    K.comap (fun h : Finset.Iic n → A × S => (h ⟨n, Finset.mem_Iic.mpr le_rfl⟩).2) (by fun_prop))

/-- The canonical infinite trajectory law has total mass one. -/
instance isProbabilityMeasure_pathMeasure [Finite S] [MeasurableSingletonClass S]
    (m : MDP S A) (π : StationaryPolicy S A) (s : S) :
    IsProbabilityMeasure (m.pathMeasure π s) := by
  unfold pathMeasure
  infer_instance

private theorem toMeasure_bind {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [Finite α] [MeasurableSingletonClass α] (p : PMF α) (q : α → PMF β) :
    (p.bind q).toMeasure = p.toMeasure.bind (fun a => (q a).toMeasure) := by
  classical
  let := Fintype.ofFinite α
  ext u hu
  rw [PMF.toMeasure_bind_apply _ _ _ hu, Measure.bind_apply hu (measurable_of_finite _).aemeasurable,
    lintegral_fintype, tsum_fintype]
  simp [mul_comm]

private theorem map_compProd {α β γ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    [Finite α] [MeasurableSingletonClass α]
    (μ : Measure α) [SFinite μ] (κ : Kernel α β) [IsSFiniteKernel κ]
    (f : α × β → γ) (hf : Measurable f) :
    (μ ⊗ₘ κ).map f = μ.bind (fun a => (κ a).map fun b => f (a, b)) := by
  ext u hu
  rw [Measure.map_apply hf hu, Measure.compProd_apply (hf hu),
    Measure.bind_apply hu (measurable_of_finite _).aemeasurable]
  congr 1
  funext a
  rw [Measure.map_apply (show Measurable (fun b => f (a, b)) from
    hf.comp (measurable_const.prodMk measurable_id)) hu]
  rfl

private def historyPrefix (n : ℕ) (h : Finset.Iic n → A × S) : FiniteTrajectory S A (n + 1) :=
  fun i => h ⟨i, Finset.mem_Iic.mpr (Nat.le_of_lt_succ i.isLt)⟩

private theorem measurable_historyPrefix (n : ℕ) :
    Measurable (historyPrefix (S := S) (A := A) n) := by
  exact measurable_pi_iff.mpr fun _ => measurable_pi_apply _

omit [MeasurableSpace S] [MeasurableSpace A] in
private theorem historyPrefix_frestrict (n : ℕ) :
    historyPrefix (S := S) (A := A) n ∘ frestrictLe n = InfiniteTrajectory.prefix (n + 1) := rfl

omit [MeasurableSpace S] [MeasurableSpace A] in
private theorem snoc_historyPrefix (n : ℕ) (ω : InfiniteTrajectory S A) :
    Fin.snoc (historyPrefix n (frestrictLe n ω)) (ω (n + 1)) =
      InfiniteTrajectory.prefix (n + 2) ω := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [InfiniteTrajectory.prefix]
  · simp [historyPrefix, InfiniteTrajectory.prefix]

private theorem map_prefix_one [Finite S] [MeasurableSingletonClass S]
    (m : MDP S A) (π : StationaryPolicy S A) (s : S) :
    (m.pathMeasure π s).map (InfiniteTrajectory.prefix 1) =
      (m.trajectoryLaw π 1 s).toMeasure := by
  rw [← historyPrefix_frestrict 0, ← Measure.map_map (measurable_historyPrefix 0)
    (measurable_frestrictLe 0)]
  change ((Kernel.trajMeasure (X := fun _ => A × S) (stepLaw m π s).toMeasure (historyKernel m π)).map
    (frestrictLe 0)).map (historyPrefix 0) = _
  rw [Kernel.trajMeasure, Measure.map_comp _ _ (measurable_frestrictLe 0),
    Kernel.traj_map_frestrictLe, Kernel.partialTraj_self, Measure.id_comp,
    Measure.map_map (measurable_historyPrefix 0) (MeasurableEquiv.measurable _),
    trajectoryLaw_one]
  rw [← PMF.toMeasure_map _ _ (by fun_prop)]
  congr 1

private theorem map_prefix_succ [Finite S] [Finite A]
    [MeasurableSingletonClass S] [MeasurableSingletonClass A]
    (m : MDP S A) (π : StationaryPolicy S A) (s : S) (n : ℕ) :
    (m.pathMeasure π s).map (InfiniteTrajectory.prefix (n + 1)) =
      (m.trajectoryLaw π (n + 1) s).toMeasure := by
  induction n with
  | zero => exact map_prefix_one m π s
  | succ n ih =>
      let F : (Finset.Iic n → A × S) × (A × S) → FiniteTrajectory S A (n + 2) :=
        fun x => Fin.snoc (historyPrefix n x.1) x.2
      let L : FiniteTrajectory S A (n + 1) → Measure (FiniteTrajectory S A (n + 2)) :=
        fun t => (stepLaw m π (t (Fin.last n)).2).toMeasure.map (Fin.snoc t)
      have hF : Measurable F := measurable_of_finite _
      have hstep := Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
        (X := fun _ => A × S) (μ₀ := (stepLaw m π s).toMeasure) (κ := historyKernel m π) (a := n)
      have hmap := congrArg (Measure.map F) hstep
      change (((m.pathMeasure π s).map (frestrictLe n)) ⊗ₘ historyKernel m π n).map F =
        ((m.pathMeasure π s).map (fun ω => (frestrictLe n ω, ω (n + 1)))).map F at hmap
      rw [Measure.map_map hF (by fun_prop)] at hmap
      have hright : F ∘ (fun ω => (frestrictLe n ω, ω (n + 1))) =
          InfiniteTrajectory.prefix (n + 2) := funext (snoc_historyPrefix n)
      rw [hright] at hmap
      rw [← hmap, map_compProd _ _ _ hF]
      have hkernel : (fun h => ((historyKernel m π n) h).map (fun e => F (h, e))) =
          fun h => L (historyPrefix n h) := by
        rfl
      rw [hkernel, ← Measure.bind_map (measurable_historyPrefix n).aemeasurable
        (measurable_of_finite L).aemeasurable,
        Measure.map_map (measurable_historyPrefix n) (measurable_frestrictLe n),
        historyPrefix_frestrict, ih, trajectoryLaw_append, toMeasure_bind]
      congr 1
      funext t
      exact PMF.toMeasure_map _ _ (measurable_of_finite _)

/-- Every finite prefix of the infinite path law has the recursively sampled finite trajectory law. -/
theorem map_prefix_pathMeasure [Finite S] [Finite A]
    [MeasurableSingletonClass S] [MeasurableSingletonClass A]
    (m : MDP S A) (π : StationaryPolicy S A) (s : S) (n : ℕ) :
    (m.pathMeasure π s).map (InfiniteTrajectory.prefix n) =
      (m.trajectoryLaw π n s).toMeasure := by
  cases n with
  | zero =>
      have hempty : InfiniteTrajectory.prefix (S := S) (A := A) 0 =
          fun _ => Fin.elim0 := funext fun _ => funext fun i => Fin.elim0 i
      rw [hempty, Measure.map_const, measure_univ, one_smul, trajectoryLaw,
        PMF.toMeasure_pure]
  | succ n => exact map_prefix_succ m π s n

end Rlib.MDP
