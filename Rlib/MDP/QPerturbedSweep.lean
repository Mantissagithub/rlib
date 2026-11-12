module

public import Rlib.MDP.QSampling

/-! # Ordered Bellman Q sweeps with bounded target errors -/

@[expose] public section

noncomputable section

namespace Rlib.MDP

variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty A]
  [DecidableEq S] [DecidableEq A]

/-- Update one entry toward its exact Bellman Q target plus a supplied target error. -/
def qPerturbedUpdate (m : MDP S A) (α γ : ℝ) (q : S → A → ℝ)
    (visit : (S × A) × ℝ) : S → A → ℝ :=
  m.qBellmanUpdate α γ q visit.1 + Pi.single visit.1.1 (Pi.single visit.1.2 (α * visit.2))

/-- A sampled update is the exact Bellman update perturbed by its realized target error. -/
theorem qLearningUpdate_eq_qPerturbedUpdate (m : MDP S A) (α γ : ℝ) (q : S → A → ℝ)
    (s : S) (a : A) (observation : ℝ × S) :
    qLearningUpdate α γ q s a observation =
      m.qPerturbedUpdate α γ q
        ((s, a), qLearningTarget γ q observation - m.qBellmanOperator γ q s a) := by
  rw [qPerturbedUpdate, ← m.qLearningUpdate_sub_qBellmanUpdate, add_sub_cancel]

/-- Apply perturbed coordinate updates in list order, using the current table at each step. -/
def qPerturbedSweep (m : MDP S A) (α γ : ℝ) (q : S → A → ℝ)
    (visits : List ((S × A) × ℝ)) : S → A → ℝ :=
  visits.foldl (m.qPerturbedUpdate α γ) q

omit [Nonempty A] [DecidableEq S] [DecidableEq A] in
private theorem norm_entry_le' (q : S → A → ℝ) (p : S × A) :
    ‖q p.1 p.2‖ ≤ ‖q‖ :=
  (norm_le_pi_norm (q p.1) p.2).trans (norm_le_pi_norm q p.1)

private theorem norm_qPerturbedUpdate_entry_sub_le (m : MDP S A) {α γ : ℝ}
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hγ0 : 0 ≤ γ) (q r : S → A → ℝ)
    (hr : m.qBellmanOperator γ r = r) (visit : (S × A) × ℝ) :
    ‖m.qPerturbedUpdate α γ q visit visit.1.1 visit.1.2 - r visit.1.1 visit.1.2‖ ≤
      (1 - α * (1 - γ)) * ‖q - r‖ + α * ‖visit.2‖ := by
  obtain ⟨⟨s, a⟩, e⟩ := visit
  have htarget : ‖m.qBellmanOperator γ q s a - r s a‖ ≤ γ * ‖q - r‖ := by
    have h := (norm_entry_le' (m.qBellmanOperator γ q - m.qBellmanOperator γ r) (s, a)).trans
      (m.norm_qBellmanOperator_sub_le γ q r)
    rwa [Real.norm_of_nonneg hγ0, hr] at h
  have hentry :
      m.qPerturbedUpdate α γ q ((s, a), e) s a - r s a =
        (1 - α) * (q s a - r s a) + α * (m.qBellmanOperator γ q s a - r s a) + α * e := by
    simp [qPerturbedUpdate, qBellmanUpdate]
    ring
  simp only [hentry]
  refine norm_add₃_le.trans ?_
  rw [norm_mul, norm_mul, norm_mul, Real.norm_of_nonneg (sub_nonneg.mpr hα1),
    Real.norm_of_nonneg hα0]
  have hq : ‖q s a - r s a‖ ≤ ‖q - r‖ := norm_entry_le' (q - r) (s, a)
  nlinarith [mul_le_mul_of_nonneg_left hq (sub_nonneg.mpr hα1),
    mul_le_mul_of_nonneg_left htarget hα0]

private theorem qPerturbedSweep_bounds (m : MDP S A) {α γ ε : ℝ}
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (q r : S → A → ℝ) (hr : m.qBellmanOperator γ r = r)
    (visits : List ((S × A) × ℝ)) (herr : ∀ v ∈ visits, ‖v.2‖ ≤ ε) :
    ‖m.qPerturbedSweep α γ q visits - r‖ ≤ max ‖q - r‖ (ε / (1 - γ)) ∧
      ∀ v ∈ visits,
        ‖m.qPerturbedSweep α γ q visits v.1.1 v.1.2 - r v.1.1 v.1.2‖ ≤
          (1 - α * (1 - γ)) * max ‖q - r‖ (ε / (1 - γ)) + α * ε := by
  set M := max ‖q - r‖ (ε / (1 - γ))
  have hρ0 : 0 ≤ 1 - α * (1 - γ) := by nlinarith [mul_nonneg hα0 hγ0]
  have hslack : α * ε = α * (1 - γ) * (ε / (1 - γ)) := by
    field_simp [(sub_pos.mpr hγ1).ne']
  have hstay : (1 - α * (1 - γ)) * M + α * ε ≤ M := by
    rw [hslack]
    nlinarith [le_max_right ‖q - r‖ (ε / (1 - γ)), mul_nonneg hα0 (sub_pos.mpr hγ1).le]
  induction visits using List.reverseRecOn with
  | nil => simp [qPerturbedSweep, M]
  | append_singleton visits v ih =>
    have ih := ih fun w hw => herr w (List.mem_append_left _ hw)
    simp only [qPerturbedSweep, List.foldl_append, List.foldl_cons, List.foldl_nil]
    let Q := m.qPerturbedSweep α γ q visits
    change ‖m.qPerturbedUpdate α γ Q v - r‖ ≤ M ∧
      ∀ w ∈ visits ++ [v],
        ‖m.qPerturbedUpdate α γ Q v w.1.1 w.1.2 - r w.1.1 w.1.2‖ ≤
          (1 - α * (1 - γ)) * M + α * ε
    have hv : ‖m.qPerturbedUpdate α γ Q v v.1.1 v.1.2 - r v.1.1 v.1.2‖ ≤
        (1 - α * (1 - γ)) * M + α * ε :=
      (m.norm_qPerturbedUpdate_entry_sub_le hα0 hα1 hγ0 Q r hr v).trans
        (add_le_add (mul_le_mul_of_nonneg_left ih.1 hρ0)
          (mul_le_mul_of_nonneg_left (herr v (by simp)) hα0))
    have hne (t : S × A) (ht : t ≠ v.1) :
        m.qPerturbedUpdate α γ Q v t.1 t.2 = Q t.1 t.2 := by
      obtain ⟨⟨s, a⟩, e⟩ := v
      obtain ⟨t, b⟩ := t
      by_cases hts : t = s
      · subst hts
        have hba : b ≠ a := fun h => ht (by rw [h])
        simp [qPerturbedUpdate, qBellmanUpdate, hba]
      · simp [qPerturbedUpdate, qBellmanUpdate, hts]
    have hM : 0 ≤ M := (norm_nonneg _).trans (le_max_left _ _)
    constructor
    · apply (pi_norm_le_iff_of_nonneg hM).2
      intro s
      apply (pi_norm_le_iff_of_nonneg hM).2
      intro a
      change ‖m.qPerturbedUpdate α γ Q v s a - r s a‖ ≤ M
      by_cases heq : (s, a) = v.1
      · obtain ⟨p, e⟩ := v
        subst heq
        exact hv.trans hstay
      · rw [hne (s, a) heq]
        exact (norm_entry_le' (Q - r) (s, a)).trans ih.1
    · intro w hw
      by_cases heq : w.1 = v.1
      · obtain ⟨⟨s, a⟩, e⟩ := w
        obtain ⟨p, e'⟩ := v
        subst heq
        exact hv
      · rw [hne w.1 heq]
        exact ih.2 w (by simpa [heq, Prod.ext_iff] using hw)

/-- A sweep that visits every entry with target errors at most `ε` contracts the distance to
the Bellman Q fixed point by the relaxation factor, up to the error floor `ε / (1 - γ)`. -/
theorem norm_qPerturbedSweep_sub_le (m : MDP S A) {α γ ε : ℝ}
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (hε : 0 ≤ ε)
    (q r : S → A → ℝ) (hr : m.qBellmanOperator γ r = r)
    (visits : List ((S × A) × ℝ)) (herr : ∀ v ∈ visits, ‖v.2‖ ≤ ε)
    (hcover : ∀ p, ∃ e, (p, e) ∈ visits) :
    ‖m.qPerturbedSweep α γ q visits - r‖ ≤
      (1 - α * (1 - γ)) * max ‖q - r‖ (ε / (1 - γ)) + α * ε := by
  have hρ0 : 0 ≤ 1 - α * (1 - γ) := by nlinarith [mul_nonneg hα0 hγ0]
  have hnonneg : 0 ≤ (1 - α * (1 - γ)) * max ‖q - r‖ (ε / (1 - γ)) + α * ε :=
    add_nonneg (mul_nonneg hρ0 ((norm_nonneg _).trans (le_max_left _ _)))
      (mul_nonneg hα0 hε)
  apply (pi_norm_le_iff_of_nonneg hnonneg).2
  intro s
  apply (pi_norm_le_iff_of_nonneg hnonneg).2
  intro a
  obtain ⟨e, he⟩ := hcover (s, a)
  exact (m.qPerturbedSweep_bounds hα0 hα1 hγ0 hγ1 q r hr visits herr).2 ((s, a), e) he

/-- Apply successive perturbed sweeps from a schedule, counting completed sweeps. -/
def qPerturbedSweepIteration (m : MDP S A) (α γ : ℝ) (q₀ : S → A → ℝ)
    (schedule : ℕ → List ((S × A) × ℝ)) : ℕ → S → A → ℝ
  | 0 => q₀
  | n + 1 => m.qPerturbedSweep α γ (m.qPerturbedSweepIteration α γ q₀ schedule n) (schedule n)

/-- Complete sweeps with target errors at most `ε` approach the Bellman Q fixed point
geometrically, up to the error floor `ε / (1 - γ)`. -/
theorem norm_qPerturbedSweepIteration_sub_le (m : MDP S A) {α γ ε : ℝ}
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (hε : 0 ≤ ε)
    (q₀ r : S → A → ℝ) (hr : m.qBellmanOperator γ r = r)
    (schedule : ℕ → List ((S × A) × ℝ)) (herr : ∀ n, ∀ v ∈ schedule n, ‖v.2‖ ≤ ε)
    (hcover : ∀ n p, ∃ e, (p, e) ∈ schedule n) (n : ℕ) :
    ‖m.qPerturbedSweepIteration α γ q₀ schedule n - r‖ ≤
      (1 - α * (1 - γ)) ^ n * ‖q₀ - r‖ + ε / (1 - γ) := by
  have hρ0 : 0 ≤ 1 - α * (1 - γ) := by nlinarith [mul_nonneg hα0 hγ0]
  have hslack : α * ε = α * (1 - γ) * (ε / (1 - γ)) := by
    field_simp [(sub_pos.mpr hγ1).ne']
  induction n with
  | zero => simp [qPerturbedSweepIteration, div_nonneg hε (sub_pos.mpr hγ1).le]
  | succ n ih =>
    have h := m.norm_qPerturbedSweep_sub_le hα0 hα1 hγ0 hγ1 hε
      (m.qPerturbedSweepIteration α γ q₀ schedule n) r hr (schedule n) (herr n) (hcover n)
    refine h.trans ?_
    rw [hslack, pow_succ]
    have hpow := mul_nonneg (pow_nonneg hρ0 n) (norm_nonneg (q₀ - r))
    rcases le_total ‖m.qPerturbedSweepIteration α γ q₀ schedule n - r‖ (ε / (1 - γ)) with hle | hle
    · rw [max_eq_right hle]
      nlinarith [mul_nonneg hα0 (sub_pos.mpr hγ1).le, mul_nonneg hpow hρ0]
    · rw [max_eq_left hle]
      nlinarith [mul_le_mul_of_nonneg_left ih hρ0]

end Rlib.MDP
