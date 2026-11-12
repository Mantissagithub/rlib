module

public import Rlib.MDP.QLearningConvergence
public import Mathlib.Probability.ConditionalExpectation

/-! # Synchronous Q-learning from independent fresh samples

Each step draws, for every state-action pair, an observation that is revealed at the next time,
is independent of the current information, has the model's mean reward, and has the model's
transition law as its successor law. Under this sampling model the realized target errors have
zero conditional mean, so synchronous Q-learning converges almost surely.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology

namespace Rlib.MDP

variable {S A Ω : Type*} [Fintype S] [Fintype A] [Nonempty A]
  [MeasurableSpace S] [MeasurableSingletonClass S]
  {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ] {ℱ : Filtration ℕ m0}

omit [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S] in
private theorem qMax_eq_sum [Fintype S] [DecidableEq S] (q : S → A → ℝ) (t : S) :
    qMax q t = ∑ s', (if t = s' then (1 : ℝ) else 0) * qMax q s' := by
  simp

omit [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S] [IsProbabilityMeasure μ] in
private theorem condExp_sum_eq_zero {ι : Type*} (I : Finset ι) (f : ι → Ω → ℝ)
    (m : MeasurableSpace Ω) (hint : ∀ i, Integrable (f i) μ)
    (hzero : ∀ i, μ[f i | m] =ᵐ[μ] 0) :
    μ[fun ω => ∑ i ∈ I, f i ω | m] =ᵐ[μ] 0 := by
  classical
  induction I using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    rw [show (fun _ : Ω => (0 : ℝ)) = 0 from rfl, condExp_zero]
  | insert i I hi ih =>
    have hsum : (fun ω => ∑ j ∈ insert i I, f j ω) = f i + fun ω => ∑ j ∈ I, f j ω := by
      funext ω
      simp [Finset.sum_insert hi]
    rw [hsum]
    refine (condExp_add (hint i) (integrable_finsetSum I fun j _ => hint j) m).trans ?_
    filter_upwards [hzero i, ih] with ω h1 h2
    simp [h1, h2]

omit [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S] in
private theorem measurable_qMax_apply {mΩ : MeasurableSpace Ω} {q : Ω → S → A → ℝ} (s' : S)
    (hq : ∀ b, Measurable fun ω => q ω s' b) : Measurable fun ω => qMax (q ω) s' := by
  have h := Finset.measurable_sup' Finset.univ_nonempty (f := fun b ω => q ω s' b)
    fun b _ => hq b
  convert h using 1
  funext ω
  simp [qMax, Finset.sup'_apply]

/-- If each observation is revealed by the next time, every entry of the synchronous
Q-learning table is known at the current time. -/
theorem measurable_qLearningSync_apply {α : ℕ → ℝ} {γ : ℝ}
    (observations : Ω → ℕ → S → A → ℝ × S)
    (hobs : ∀ n s a, Measurable[ℱ (n + 1)] fun ω => observations ω n s a)
    (q₀ : S → A → ℝ) (n : ℕ) (s : S) (a : A) :
    Measurable[ℱ n] fun ω => qLearningSync α γ (observations ω) q₀ n s a := by
  classical
  induction n generalizing s a with
  | zero => exact measurable_const
  | succ n ih =>
    have hq (s : S) (a : A) :
        Measurable[ℱ (n + 1)] fun ω => qLearningSync α γ (observations ω) q₀ n s a :=
      (ih s a).mono (ℱ.mono (Nat.le_succ n)) le_rfl
    have hmax (s' : S) :
        Measurable[ℱ (n + 1)] fun ω => qMax (qLearningSync α γ (observations ω) q₀ n) s' :=
      measurable_qMax_apply s' fun b => hq s' b
    have hnext : Measurable[ℱ (n + 1)] fun ω => (observations ω n s a).2 :=
      measurable_snd.comp (hobs n s a)
    have hreward : Measurable[ℱ (n + 1)] fun ω => (observations ω n s a).1 :=
      measurable_fst.comp (hobs n s a)
    have htarget : Measurable[ℱ (n + 1)] fun ω =>
        qMax (qLearningSync α γ (observations ω) q₀ n) (observations ω n s a).2 := by
      rw [show (fun ω => qMax (qLearningSync α γ (observations ω) q₀ n)
          (observations ω n s a).2) = fun ω => ∑ s', (if (observations ω n s a).2 = s' then
            (1 : ℝ) else 0) * qMax (qLearningSync α γ (observations ω) q₀ n) s' from
        funext fun ω => qMax_eq_sum _ _]
      refine Finset.measurable_sum _ fun s' _ => Measurable.mul ?_ (hmax s')
      exact Measurable.ite (hnext (measurableSet_singleton s')) measurable_const
        measurable_const
    simp only [qLearningSync, qLearningTarget]
    exact (hq s a).add (measurable_const.mul ((hreward.add (measurable_const.mul htarget)).sub
      (hq s a)))

omit [MeasurableSpace S] [MeasurableSingletonClass S] in
private theorem qLearningSyncError_eq_sum [DecidableEq S] (m : MDP S A) (α : ℕ → ℝ) (γ : ℝ)
    (observations : ℕ → S → A → ℝ × S) (q₀ : S → A → ℝ) (n : ℕ) (s : S) (a : A) :
    m.qLearningSyncError α γ observations q₀ n s a =
      ((observations n s a).1 - m.reward s a) +
        ∑ s', γ * ((if (observations n s a).2 = s' then (1 : ℝ) else 0) -
          (m.transition s a s').toReal) * qMax (qLearningSync α γ observations q₀ n) s' := by
  simp only [qLearningSyncError, qLearningTarget, qBellmanOperator, oneStepActionValue,
    expect]
  rw [qMax_eq_sum _ (observations n s a).2]
  simp only [sub_mul, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
  ring_nf

/-- **Fresh samples have unbiased targets.** Suppose each observation is revealed by the next
time, is independent of the current information, has the model's mean reward, and has the
model's transition law as its successor law. With bounded rewards and step sizes in `[0, 1]`,
each realized target error of synchronous Q-learning has zero conditional mean given the
current time. -/
theorem condExp_qLearningSyncError_eq_zero (m : MDP S A) {α : ℕ → ℝ} {γ R : ℝ}
    (hα0 : ∀ n, 0 ≤ α n) (hα1 : ∀ n, α n ≤ 1) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (observations : Ω → ℕ → S → A → ℝ × S)
    (hobs : ∀ n s a, Measurable[ℱ (n + 1)] fun ω => observations ω n s a)
    (hindep : ∀ n s a,
      Indep (MeasurableSpace.comap (fun ω => observations ω n s a) inferInstance) (ℱ n) μ)
    (hreward : ∀ n s a, ∫ ω, (observations ω n s a).1 ∂μ = m.reward s a)
    (hnext : ∀ n s a,
      μ.map (fun ω => (observations ω n s a).2) = (m.transition s a).toMeasure)
    (hR : ∀ ω n s a, |(observations ω n s a).1| ≤ R) (q₀ : S → A → ℝ) (n : ℕ) (s : S) (a : A) :
    μ[fun ω => m.qLearningSyncError α γ (observations ω) q₀ n s a | ℱ n] =ᵐ[μ] 0 := by
  classical
  set X : Ω → ℝ × S := fun ω => observations ω n s a
  set K := max ‖q₀‖ (R / (1 - γ))
  have hX : Measurable X := (hobs n s a).mono (ℱ.le _) le_rfl
  have hcomap : MeasurableSpace.comap X inferInstance ≤ m0 := hX.comap_le
  have hreward_meas : Measurable[MeasurableSpace.comap X inferInstance] fun ω => (X ω).1 :=
    measurable_fst.comp (comap_measurable X)
  have hind_meas (s' : S) : Measurable[MeasurableSpace.comap X inferInstance]
      fun ω => (if (X ω).2 = s' then (1 : ℝ) else 0) - (m.transition s a s').toReal :=
    (Measurable.ite ((measurable_snd.comp (comap_measurable X)) (measurableSet_singleton s'))
      measurable_const measurable_const).sub measurable_const
  have hfsti : Integrable (fun ω => (X ω).1) μ :=
    Integrable.of_bound hX.fst.aestronglyMeasurable R
      (Eventually.of_forall fun ω => by simpa [Real.norm_eq_abs, X] using hR ω n s a)
  have hrewardi : Integrable (fun ω => (X ω).1 - m.reward s a) μ :=
    hfsti.sub (integrable_const _)
  have hreward0 : ∫ ω, ((X ω).1 - m.reward s a) ∂μ = 0 := by
    rw [integral_sub hfsti (integrable_const _)]
    simp [X, hreward n s a]
  have hindi (s' : S) : Integrable
      (fun ω => (if (X ω).2 = s' then (1 : ℝ) else 0) - (m.transition s a s').toReal) μ :=
    Integrable.of_bound ((hind_meas s').mono hcomap le_rfl).aestronglyMeasurable
      (1 + (m.transition s a s').toReal) (Eventually.of_forall fun ω => by
        have hp := ENNReal.toReal_nonneg (a := m.transition s a s')
        split_ifs <;> rw [Real.norm_eq_abs, abs_le] <;> constructor <;> linarith)
  have hQ (s' : S) : StronglyMeasurable[ℱ n]
      fun ω => qMax (qLearningSync α γ (observations ω) q₀ n) s' :=
    (measurable_qMax_apply s' fun b =>
      measurable_qLearningSync_apply observations hobs q₀ n s' b).stronglyMeasurable
  have hQb (ω : Ω) (s' : S) : |qMax (qLearningSync α γ (observations ω) q₀ n) s'| ≤ K := by
    have := (norm_le_pi_norm (qMax (qLearningSync α γ (observations ω) q₀ n)) s').trans
      ((norm_qMax_le _).trans
        (norm_qLearningSync_le hα0 hα1 hγ0 hγ1 (observations ω) (hR ω) q₀ n))
    rwa [Real.norm_eq_abs] at this
  have hterm (s' : S) : Integrable (fun ω => γ * ((if (X ω).2 = s' then (1 : ℝ) else 0) -
      (m.transition s a s').toReal) * qMax (qLearningSync α γ (observations ω) q₀ n) s') μ := by
    have h := ((hindi s').const_mul γ).mul_bdd (c := K)
      ((hQ s').mono (ℱ.le n)).aestronglyMeasurable
      (Eventually.of_forall fun ω => by simpa [Real.norm_eq_abs] using hQb ω s')
    exact h.congr (Eventually.of_forall fun ω => rfl)
  have hzero_reward : μ[fun ω => (X ω).1 - m.reward s a | ℱ n] =ᵐ[μ] 0 := by
    refine (condExp_indep_eq hcomap (ℱ.le n)
      (hreward_meas.sub measurable_const).stronglyMeasurable (hindep n s a)).trans ?_
    refine Eventually.of_forall fun _ => ?_
    simpa using hreward0
  have hzero_term (s' : S) : μ[fun ω => γ * ((if (X ω).2 = s' then (1 : ℝ) else 0) -
      (m.transition s a s').toReal) * qMax (qLearningSync α γ (observations ω) q₀ n) s' |
        ℱ n] =ᵐ[μ] 0 := by
    have hmean : ∫ ω, ((if (X ω).2 = s' then (1 : ℝ) else 0) -
        (m.transition s a s').toReal) ∂μ = 0 := by
      have hset : MeasurableSet {ω | (X ω).2 = s'} :=
        hX.snd (measurableSet_singleton s')
      have hprob : μ.real {ω | (X ω).2 = s'} = (m.transition s a s').toReal := by
        have h := congrArg (fun ν : Measure S => ν.real {s'}) (hnext n s a)
        simp only [measureReal_def] at h
        rw [Measure.map_apply hX.snd (measurableSet_singleton s'),
          PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton s')] at h
        rw [measureReal_def]
        exact h
      have hite : (fun ω => if (X ω).2 = s' then (1 : ℝ) else 0) =
          {ω | (X ω).2 = s'}.indicator 1 := by
        funext ω
        simp [Set.indicator_apply]
      have hitei : Integrable (fun ω => if (X ω).2 = s' then (1 : ℝ) else 0) μ := by
        rw [hite]
        exact (integrable_const 1).indicator hset
      rw [integral_sub hitei (integrable_const _), hite, integral_indicator_one hset, hprob]
      simp
    have hpull := condExp_mul_of_stronglyMeasurable_left (m := ℱ n) (hQ s')
      ((hterm s').congr (Eventually.of_forall fun ω => by simp only [Pi.mul_apply]; ring))
      ((hindi s').const_mul γ)
    have hcomm : (fun ω => γ * ((if (X ω).2 = s' then (1 : ℝ) else 0) -
        (m.transition s a s').toReal) * qMax (qLearningSync α γ (observations ω) q₀ n) s') =
        (fun ω => qMax (qLearningSync α γ (observations ω) q₀ n) s') *
          fun ω => γ * ((if (X ω).2 = s' then (1 : ℝ) else 0) -
            (m.transition s a s').toReal) := by
      funext ω
      simp only [Pi.mul_apply]
      ring
    rw [hcomm]
    refine hpull.trans ?_
    have hinner : μ[fun ω => γ * ((if (X ω).2 = s' then (1 : ℝ) else 0) -
        (m.transition s a s').toReal) | ℱ n] =ᵐ[μ] 0 := by
      refine (condExp_indep_eq hcomap (ℱ.le n)
        ((hind_meas s').const_mul γ).stronglyMeasurable (hindep n s a)).trans ?_
      refine Eventually.of_forall fun _ => ?_
      rw [integral_const_mul, hmean]
      simp
    filter_upwards [hinner] with ω h
    simp [h]
  have hsplit : (fun ω => m.qLearningSyncError α γ (observations ω) q₀ n s a) =
      (fun ω => (X ω).1 - m.reward s a) + fun ω => ∑ s', γ *
        ((if (X ω).2 = s' then (1 : ℝ) else 0) - (m.transition s a s').toReal) *
          qMax (qLearningSync α γ (observations ω) q₀ n) s' := by
    funext ω
    exact qLearningSyncError_eq_sum m α γ (observations ω) q₀ n s a
  rw [hsplit]
  refine (condExp_add hrewardi (integrable_finsetSum _ fun s' _ => hterm s') _).trans ?_
  filter_upwards [hzero_reward,
    condExp_sum_eq_zero Finset.univ _ (ℱ n) hterm hzero_term] with ω h1 h2
  simp [h1, h2]

/-- **Almost sure convergence of Q-learning from fresh samples.** Suppose every state-action
pair is updated at every step from an observation that is revealed by the next time, is
independent of the current information, has the model's mean reward and transition law, and
has reward bounded by `R`. With step sizes in `[0, 1]` that are not summable but have summable
squares and a discount in `[0, 1)`, synchronous Q-learning converges almost surely to the
Bellman Q fixed point. -/
theorem ae_tendsto_qLearningSync_of_indep (m : MDP S A) {α : ℕ → ℝ} {γ R : ℝ}
    (hα0 : ∀ n, 0 ≤ α n) (hα1 : ∀ n, α n ≤ 1) (hαsum : ¬Summable α)
    (hαsq : Summable fun n => α n ^ 2) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (observations : Ω → ℕ → S → A → ℝ × S)
    (hobs : ∀ n s a, Measurable[ℱ (n + 1)] fun ω => observations ω n s a)
    (hindep : ∀ n s a,
      Indep (MeasurableSpace.comap (fun ω => observations ω n s a) inferInstance) (ℱ n) μ)
    (hreward : ∀ n s a, ∫ ω, (observations ω n s a).1 ∂μ = m.reward s a)
    (hnext : ∀ n s a,
      μ.map (fun ω => (observations ω n s a).2) = (m.transition s a).toMeasure)
    (hR : ∀ ω n s a, |(observations ω n s a).1| ≤ R) (q₀ r : S → A → ℝ)
    (hr : m.qBellmanOperator γ r = r) :
    ∀ᵐ ω ∂μ, Tendsto (qLearningSync α γ (observations ω) q₀) atTop (𝓝 r) := by
  classical
  refine m.ae_tendsto_qLearningSync (ℱ := ℱ) hα0 hα1 hαsum hαsq hγ0 hγ1 observations hR q₀ r hr
    (fun n s a => ?_)
    (fun n s a => m.condExp_qLearningSyncError_eq_zero hα0 hα1 hγ0 hγ1 observations hobs
      hindep hreward hnext hR q₀ n s a)
  have hq (s' : S) (b : A) :
      Measurable[ℱ (n + 1)] fun ω => qLearningSync α γ (observations ω) q₀ n s' b :=
    (measurable_qLearningSync_apply observations hobs q₀ n s' b).mono
      (ℱ.mono (Nat.le_succ n)) le_rfl
  have hmax (s' : S) : Measurable[ℱ (n + 1)]
      fun ω => qMax (qLearningSync α γ (observations ω) q₀ n) s' :=
    measurable_qMax_apply s' fun b => hq s' b
  have hnextm : Measurable[ℱ (n + 1)] fun ω => (observations ω n s a).2 :=
    measurable_snd.comp (hobs n s a)
  refine Measurable.stronglyMeasurable ?_
  simp_rw [qLearningSyncError_eq_sum]
  refine ((measurable_fst.comp (hobs n s a)).sub measurable_const).add
    (Finset.measurable_sum _ fun s' _ => ?_)
  exact (measurable_const.mul ((Measurable.ite (hnextm (measurableSet_singleton s'))
    measurable_const measurable_const).sub measurable_const)).mul (hmax s')

end Rlib.MDP
