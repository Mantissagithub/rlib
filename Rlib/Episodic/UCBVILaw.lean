module

public import Rlib.Episodic.UCBVI
public import Rlib.Probability.ProductResample

/-! # The law of UCB-VI episodes

The draws are coordinates of a product: `ω (h, s, a, n) ∼ P_h (· | s, a)` independently for
`h < H` and `n < K`. Episode `k < K` reads the draws counted before it and, at stage `h`, the
draw `(h, s^k_h, a^k_h, N^k_h (s^k_h, a^k_h))`, which no earlier step has read. So, given the
past, the state of episode `k` at stage `h` has the law `d^{π_k}_h` of the episode's policy: for
every function `φ` of the past and a state, `E [φ (s^k_h)] = E [E_{s ∼ d^{π_k}_h} φ (s)]`. This is
the step in Agarwal, Jiang, Kakade, and Sun, proof of Theorem 7.1, that conditions on the history
`H_{<k}`.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace Rlib

namespace EpisodicMDP

variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty A] [DecidableEq S] [DecidableEq A]
  {H K : ℕ}

/-- Indices of the draws: stage, state, action, and visit number. -/
abbrev TapeIndex (S A : Type*) (H K : ℕ) := Fin H × S × A × Fin K

omit [Fintype S] [Fintype A] [Nonempty A] [DecidableEq S] [DecidableEq A] in
/-- The draw table read by UCB-VI; out-of-range reads stay at the current state. -/
def tapeSamples (ω : TapeIndex S A H K → S) : ℕ → S → A → ℕ → S := fun h s a n =>
  if hh : h < H then if hn : n < K then ω (⟨h, hh⟩, s, a, ⟨n, hn⟩) else s else s

omit [Fintype S] [Fintype A] [Nonempty A] in
theorem tapeSamples_update_of_ne (ω : TapeIndex S A H K → S) (c : TapeIndex S A H K) (z : S)
    {h : ℕ} {s : S} {a : A} {i : ℕ} (hne : ¬ (h = c.1 ∧ s = c.2.1 ∧ a = c.2.2.1 ∧ i = c.2.2.2)) :
    tapeSamples (Function.update ω c z) h s a i = tapeSamples ω h s a i := by
  unfold tapeSamples
  split_ifs with hh hi
  · rw [Function.update_of_ne]
    rintro rfl
    exact hne ⟨rfl, rfl, rfl, rfl⟩
  · rfl
  · rfl

variable [MeasurableSpace S] [MeasurableSingletonClass S]

/-- The law of the draws: independent successors `ω (h, s, a, n) ∼ P_h (· | s, a)`. -/
def tapeLaw (M : EpisodicMDP S A) (H K : ℕ) : Measure (TapeIndex S A H K → S) :=
  Measure.pi fun i => (M.transition i.1 i.2.1 i.2.2.1).toMeasure

instance (M : EpisodicMDP S A) (H K : ℕ) : IsProbabilityMeasure (M.tapeLaw H K) := by
  unfold tapeLaw; infer_instance

/-- A function of the draws is determined by the past of episode `k` if it agrees on any two
draw tables that agree on the draws counted before episode `k` under the first. -/
def IsPast (M : EpisodicMDP S A) (H K : ℕ) (L : ℝ) (s₀ : S) (k : ℕ)
    (φ : (TapeIndex S A H K → S) → ℝ) : Prop :=
  ∀ ω ω', (∀ h s a i, i < M.ucbviCounts H L s₀ (tapeSamples ω) k h s a →
    tapeSamples ω' h s a i = tapeSamples ω h s a i) → φ ω' = φ ω

omit [MeasurableSpace S] [MeasurableSingletonClass S] in
/-- Counts before episode `k` are at most `k`. -/
theorem ucbviCounts_le (M : EpisodicMDP S A) (H : ℕ) (L : ℝ) (s₀ : S)
    (samples : ℕ → S → A → ℕ → S) (k h : ℕ) (s : S) (a : A) :
    M.ucbviCounts H L s₀ samples k h s a ≤ k := by
  simp only [ucbviCounts, countsOf, visitCount]
  exact (Finset.card_filter_le _ _).trans (by simp)

omit [MeasurableSpace S] [MeasurableSingletonClass S] in
/-- Draw tables that agree on the past of episode `k` give the same counts and policy. -/
theorem ucbviCounts_policy_congr (M : EpisodicMDP S A) (L : ℝ) (s₀ : S) (k : ℕ)
    {samples samples' : ℕ → S → A → ℕ → S}
    (hagree : ∀ h s a i, i < M.ucbviCounts H L s₀ samples k h s a →
      samples' h s a i = samples h s a i) :
    M.ucbviCounts H L s₀ samples' k = M.ucbviCounts H L s₀ samples k ∧
      M.ucbviPolicyAt H L s₀ samples' k = M.ucbviPolicyAt H L s₀ samples k := by
  have hhist := M.ucbviHistory_congr H L s₀ (samples := samples) (samples' := samples') k
    (fun h s a i hi => hagree h s a i (by rwa [countsOf_ucbviHistory] at hi))
  have hN : M.ucbviCounts H L s₀ samples' k = M.ucbviCounts H L s₀ samples k := by
    rw [← countsOf_ucbviHistory, ← countsOf_ucbviHistory, hhist]
  refine ⟨hN, ?_⟩
  simp only [ucbviPolicyAt, hN]
  exact M.ucbviPolicy_congr H L hagree

omit [MeasurableSpace S] [MeasurableSingletonClass S] in
/-- The trajectory of episode `k` in terms of its policy and counts. -/
theorem ucbviTrajectory_succ_fst (M : EpisodicMDP S A) (L : ℝ) (s₀ : S)
    (samples : ℕ → S → A → ℕ → S) (k h : ℕ) :
    (M.ucbviTrajectory H L s₀ samples k (h + 1)).1 =
      samples h (M.ucbviTrajectory H L s₀ samples k h).1
        (M.ucbviTrajectory H L s₀ samples k h).2
        (M.ucbviCounts H L s₀ samples k h (M.ucbviTrajectory H L s₀ samples k h).1
          (M.ucbviTrajectory H L s₀ samples k h).2) := by
  rw [ucbviTrajectory_eq, ucbviTrajectory_eq]
  rfl

/-- The draw read by episode `k` at stage `h`. -/
def readIndex (M : EpisodicMDP S A) (L : ℝ) (s₀ : S) {k h : ℕ} (hk : k < K) (hh : h < H)
    (ω : TapeIndex S A H K → S) : TapeIndex S A H K :=
  (⟨h, hh⟩, (M.ucbviTrajectory H L s₀ (tapeSamples ω) k h).1,
    (M.ucbviTrajectory H L s₀ (tapeSamples ω) k h).2,
    ⟨M.ucbviCounts H L s₀ (tapeSamples ω) k h (M.ucbviTrajectory H L s₀ (tapeSamples ω) k h).1
      (M.ucbviTrajectory H L s₀ (tapeSamples ω) k h).2,
      lt_of_le_of_lt (M.ucbviCounts_le H L s₀ _ k h _ _) hk⟩)

omit [MeasurableSpace S] [MeasurableSingletonClass S] in
/-- **Unread draws.** Changing the draw that episode `k` reads at stage `h` changes neither the
past of episode `k` nor its states up to stage `h`. -/
theorem update_readIndex (M : EpisodicMDP S A) (L : ℝ) (s₀ : S) {k h : ℕ} (hk : k < K)
    (hh : h < H) (ω : TapeIndex S A H K → S) (z : S) :
    (∀ h' s' a' i, i < M.ucbviCounts H L s₀ (tapeSamples ω) k h' s' a' →
      tapeSamples (Function.update ω (M.readIndex L s₀ hk hh ω) z) h' s' a' i =
        tapeSamples ω h' s' a' i) ∧
    ∀ j, j ≤ h → M.ucbviTrajectory H L s₀
      (tapeSamples (Function.update ω (M.readIndex L s₀ hk hh ω) z)) k j =
        M.ucbviTrajectory H L s₀ (tapeSamples ω) k j := by
  set c := M.readIndex L s₀ hk hh ω
  set N := M.ucbviCounts H L s₀ (tapeSamples ω) k
  have hagree : ∀ h' s' a' i, i < N h' s' a' →
      tapeSamples (Function.update ω c z) h' s' a' i = tapeSamples ω h' s' a' i := by
    intro h' s' a' i hi
    refine tapeSamples_update_of_ne ω c z ?_
    rintro ⟨rfl, rfl, rfl, rfl⟩
    exact lt_irrefl _ hi
  refine ⟨hagree, fun j hj => ?_⟩
  obtain ⟨hN, hπ⟩ := M.ucbviCounts_policy_congr L s₀ k hagree
  rw [ucbviTrajectory_eq, ucbviTrajectory_eq, hN, hπ]
  have hstates := episodeState_congr (samples := tapeSamples ω)
    (samples' := tapeSamples (Function.update ω c z)) (M.ucbviPolicyAt H L s₀ (tapeSamples ω) k)
    N s₀ (h := h) (fun j' hj' => by
      refine tapeSamples_update_of_ne ω c z ?_
      rintro ⟨h1, -, -, -⟩
      simp only [c, readIndex] at h1
      omega) j hj
  rw [hstates]

omit [MeasurableSpace S] [MeasurableSingletonClass S] in
/-- The read index is unchanged by changing the draw at any index `c`, when it equals `c`
before or after the change. -/
theorem readIndex_update_iff (M : EpisodicMDP S A) (L : ℝ) (s₀ : S) {k h : ℕ} (hk : k < K)
    (hh : h < H) (ω : TapeIndex S A H K → S) (c : TapeIndex S A H K) (z : S) :
    M.readIndex L s₀ hk hh (Function.update ω c z) = c ↔ M.readIndex L s₀ hk hh ω = c := by
  have key : ∀ ω : TapeIndex S A H K → S, ∀ z, M.readIndex L s₀ hk hh ω = c →
      M.readIndex L s₀ hk hh (Function.update ω c z) = c := by
    intro ω z hc
    obtain ⟨hagree, htraj⟩ := M.update_readIndex L s₀ hk hh ω z
    obtain ⟨hN, -⟩ := M.ucbviCounts_policy_congr L s₀ k hagree
    have h1 := htraj h le_rfl
    generalize hω' : Function.update ω (M.readIndex L s₀ hk hh ω) z = ω' at h1 hN
    rw [← hc, hω']
    simp only [readIndex, Prod.mk.injEq, Fin.mk.injEq, true_and]
    rw [h1, hN]
    exact ⟨rfl, rfl, rfl⟩
  constructor
  · intro h1
    have := key (Function.update ω c z) (ω c) h1
    simpa using this
  · exact key ω z

/-- **One step of an episode.** For `k < K`, `h < H`, and `ψ` such that every `ψ · y` depends
only on the past of episode `k`, `E [ψ (s^k_{h+1})] = E [E_{s' ∼ P_h (s^k_h, a^k_h)} ψ (s')]`. -/
theorem integral_ucbviTrajectory_succ (M : EpisodicMDP S A) (L : ℝ) (s₀ : S) {k h : ℕ}
    (hk : k < K) (hh : h < H) (ψ : (TapeIndex S A H K → S) → S → ℝ)
    (hψ : ∀ y, M.IsPast H K L s₀ k fun ω => ψ ω y) :
    ∫ ω, ψ ω (M.ucbviTrajectory H L s₀ (tapeSamples ω) k (h + 1)).1 ∂M.tapeLaw H K =
      ∫ ω, expect (M.transition h (M.ucbviTrajectory H L s₀ (tapeSamples ω) k h).1
        (M.ucbviTrajectory H L s₀ (tapeSamples ω) k h).2) (ψ ω) ∂M.tapeLaw H K := by
  set ν : TapeIndex S A H K → PMF S := fun i => M.transition i.1 i.2.1 i.2.2.1
  set cI := M.readIndex L s₀ hk hh
  have hread (ω : TapeIndex S A H K → S) :
      (M.ucbviTrajectory H L s₀ (tapeSamples ω) k (h + 1)).1 = ω (cI ω) := by
    rw [ucbviTrajectory_succ_fst]
    simp only [tapeSamples, hh, lt_of_le_of_lt (M.ucbviCounts_le H L s₀ _ k h _ _) hk,
      ↓reduceDIte, cI, readIndex]
  set G : TapeIndex S A H K → (TapeIndex S A H K → S) → S → ℝ :=
    fun c ω y => if cI ω = c then ψ ω y else 0
  have hG (c : TapeIndex S A H K) (ω : TapeIndex S A H K → S) (z y : S) :
      G c (Function.update ω c z) y = G c ω y := by
    have hiff : cI (Function.update ω c z) = c ↔ cI ω = c := M.readIndex_update_iff L s₀ hk hh ω c z
    simp only [G]
    by_cases hc : cI ω = c
    · have hc' := hiff.mpr hc
      simp only [hc, hc', ↓reduceIte]
      obtain ⟨hagree, -⟩ := M.update_readIndex L s₀ hk hh ω z
      have hupd : Function.update ω c z = Function.update ω (cI ω) z := by rw [hc]
      rw [hupd]
      exact hψ y ω _ hagree
    · have hc' : ¬ cI (Function.update ω c z) = c := fun h => hc (hiff.mp h)
      simp only [hc, hc', ↓reduceIte]
  have hlhs (ω : TapeIndex S A H K → S) :
      ψ ω (M.ucbviTrajectory H L s₀ (tapeSamples ω) k (h + 1)).1 = ∑ c, G c ω (ω c) := by
    rw [hread]
    simp only [G]
    rw [Finset.sum_ite_eq]
    simp
  have hrhs (ω : TapeIndex S A H K → S) :
      expect (M.transition h (M.ucbviTrajectory H L s₀ (tapeSamples ω) k h).1
        (M.ucbviTrajectory H L s₀ (tapeSamples ω) k h).2) (ψ ω) =
        ∑ c, expect (ν c) (G c ω) := by
    have hν : ν (cI ω) = M.transition h (M.ucbviTrajectory H L s₀ (tapeSamples ω) k h).1
        (M.ucbviTrajectory H L s₀ (tapeSamples ω) k h).2 := rfl
    rw [← hν]
    have hterm (c : TapeIndex S A H K) : expect (ν c) (G c ω) =
        if cI ω = c then expect (ν c) (ψ ω) else 0 := by
      simp only [G]
      split_ifs <;> simp
    simp only [hterm]
    rw [Finset.sum_ite_eq]
    simp
  simp only [hlhs, hrhs]
  rw [integral_finsetSum _ fun c _ => Integrable.of_finite,
    integral_finsetSum _ fun c _ => Integrable.of_finite]
  exact Finset.sum_congr rfl fun c _ => integral_pi_resample ν c (G c) (hG c)

/-- **The law of an episode given the past.** For `k < K`, `h ≤ H`, and `φ` such that every
`φ · y` depends only on the past of episode `k`,
`E [φ (s^k_h)] = E [E_{s ∼ d^{π_k}_h} φ (s)]`. -/
theorem integral_ucbviTrajectory_eq_stateDist (M : EpisodicMDP S A) (L : ℝ) (s₀ : S) {k : ℕ}
    (hk : k < K) : ∀ h, h ≤ H → ∀ φ : (TapeIndex S A H K → S) → S → ℝ,
      (∀ y, M.IsPast H K L s₀ k fun ω => φ ω y) →
      ∫ ω, φ ω (M.ucbviTrajectory H L s₀ (tapeSamples ω) k h).1 ∂M.tapeLaw H K =
        ∫ ω, expect (M.stateDist (M.ucbviPolicyAt H L s₀ (tapeSamples ω) k) s₀ h) (φ ω)
          ∂M.tapeLaw H K := by
  intro h
  induction h with
  | zero =>
    intro _ φ _
    congr 1
    funext ω
    rw [ucbviTrajectory_eq]
    simp [episodeState, stateDist]
  | succ h ih =>
    intro hh φ hφ
    rw [M.integral_ucbviTrajectory_succ L s₀ hk (by omega) φ hφ]
    set ψ : (TapeIndex S A H K → S) → S → ℝ := fun ω s =>
      expect (M.transition h s (M.ucbviPolicyAt H L s₀ (tapeSamples ω) k h s)) (φ ω)
    have hψ : ∀ y, M.IsPast H K L s₀ k fun ω => ψ ω y := by
      intro y ω ω' hagree
      obtain ⟨-, hπ⟩ := M.ucbviCounts_policy_congr L s₀ k hagree
      simp only [ψ, hπ]
      congr 1
      funext t
      exact hφ t ω ω' hagree
    have hact (ω : TapeIndex S A H K → S) : (M.ucbviTrajectory H L s₀ (tapeSamples ω) k h).2 =
        M.ucbviPolicyAt H L s₀ (tapeSamples ω) k h
          (M.ucbviTrajectory H L s₀ (tapeSamples ω) k h).1 := by
      rw [ucbviTrajectory_eq]
    simp only [hact]
    rw [show (fun ω => expect (M.transition h (M.ucbviTrajectory H L s₀ (tapeSamples ω) k h).1
        (M.ucbviPolicyAt H L s₀ (tapeSamples ω) k h
          (M.ucbviTrajectory H L s₀ (tapeSamples ω) k h).1)) (φ ω)) =
        fun ω => ψ ω (M.ucbviTrajectory H L s₀ (tapeSamples ω) k h).1 from rfl,
      ih (by omega) ψ hψ]
    congr 1
    funext ω
    simp only [ψ, stateDist, expect_bind]

end EpisodicMDP

end Rlib
