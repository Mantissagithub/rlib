module

public import Rlib.MDP.QLearning
public import Mathlib.Analysis.SpecificLimits.Normed

/-! # Ordered coordinate sweeps with exact Bellman Q targets -/

@[expose] public section

noncomputable section

open scoped Topology

namespace Rlib.MDP

variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty A]
  [DecidableEq S] [DecidableEq A]

/-- Update one entry by mixing its old value with its exact Bellman Q target. -/
def qBellmanUpdate (m : MDP S A) (α γ : ℝ) (q : S → A → ℝ)
    (p : S × A) : S → A → ℝ :=
  fun s a => Function.update (Function.uncurry q) p
    ((1 - α) * q p.1 p.2 + α * m.qBellmanOperator γ q p.1 p.2) (s, a)

/-- Apply coordinate updates in list order, using the current table at each step. -/
def qBellmanSweep (m : MDP S A) (α γ : ℝ) (q : S → A → ℝ)
    (visits : List (S × A)) : S → A → ℝ :=
  visits.foldl (m.qBellmanUpdate α γ) q

omit [Nonempty A] [DecidableEq S] [DecidableEq A] in
private theorem norm_entry_le (q : S → A → ℝ) (p : S × A) :
    ‖q p.1 p.2‖ ≤ ‖q‖ :=
  (norm_le_pi_norm (q p.1) p.2).trans (norm_le_pi_norm q p.1)

private theorem norm_qBellmanUpdate_entry_sub_le (m : MDP S A) {α γ : ℝ}
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hγ0 : 0 ≤ γ) (q r : S → A → ℝ)
    (p : S × A) :
    ‖m.qBellmanUpdate α γ q p p.1 p.2 - m.qBellmanUpdate α γ r p p.1 p.2‖ ≤
      (1 - α * (1 - γ)) * ‖q - r‖ := by
  have htarget : ‖m.qBellmanOperator γ q p.1 p.2 - m.qBellmanOperator γ r p.1 p.2‖ ≤
      γ * ‖q - r‖ := by
    refine (norm_entry_le (m.qBellmanOperator γ q - m.qBellmanOperator γ r) p).trans ?_
    simpa only [Real.norm_of_nonneg hγ0] using m.norm_qBellmanOperator_sub_le γ q r
  have hmix :
      (1 - α) * q p.1 p.2 + α * m.qBellmanOperator γ q p.1 p.2 -
          ((1 - α) * r p.1 p.2 + α * m.qBellmanOperator γ r p.1 p.2) =
        (1 - α) * (q p.1 p.2 - r p.1 p.2) +
          α * (m.qBellmanOperator γ q p.1 p.2 - m.qBellmanOperator γ r p.1 p.2) := by
    ring
  simp only [qBellmanUpdate, Prod.eta, Function.update_self, hmix]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul, Real.norm_of_nonneg (sub_nonneg.mpr hα1), Real.norm_of_nonneg hα0]
  calc
    _ ≤ (1 - α) * ‖q - r‖ + α * (γ * ‖q - r‖) :=
      add_le_add (mul_le_mul_of_nonneg_left (norm_entry_le (q - r) p) (sub_nonneg.mpr hα1))
        (mul_le_mul_of_nonneg_left htarget hα0)
    _ = _ := by ring

private theorem qBellmanSweep_bounds (m : MDP S A) {α γ : ℝ}
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (q r : S → A → ℝ) (visits : List (S × A)) :
    ‖m.qBellmanSweep α γ q visits - m.qBellmanSweep α γ r visits‖ ≤ ‖q - r‖ ∧
      ∀ p ∈ visits,
        ‖m.qBellmanSweep α γ q visits p.1 p.2 - m.qBellmanSweep α γ r visits p.1 p.2‖ ≤
          (1 - α * (1 - γ)) * ‖q - r‖ := by
  have hρ0 : 0 ≤ 1 - α * (1 - γ) := by nlinarith [mul_nonneg hα0 hγ0]
  have hρ1 : 1 - α * (1 - γ) ≤ 1 := by
    linarith [mul_nonneg hα0 (sub_nonneg.mpr hγ1)]
  induction visits using List.reverseRecOn with
  | nil => simp [qBellmanSweep]
  | append_singleton visits p ih =>
    simp only [qBellmanSweep, List.foldl_append, List.foldl_cons, List.foldl_nil]
    let Q := m.qBellmanSweep α γ q visits
    let R := m.qBellmanSweep α γ r visits
    change ‖m.qBellmanUpdate α γ Q p - m.qBellmanUpdate α γ R p‖ ≤ ‖q - r‖ ∧
      ∀ t ∈ visits ++ [p],
        ‖m.qBellmanUpdate α γ Q p t.1 t.2 - m.qBellmanUpdate α γ R p t.1 t.2‖ ≤
          (1 - α * (1 - γ)) * ‖q - r‖
    have hp := (m.norm_qBellmanUpdate_entry_sub_le hα0 hα1 hγ0 Q R p).trans
      (mul_le_mul_of_nonneg_left ih.1 hρ0)
    have hne (t : S × A) (ht : t ≠ p) :
        m.qBellmanUpdate α γ Q p t.1 t.2 - m.qBellmanUpdate α γ R p t.1 t.2 =
          Q t.1 t.2 - R t.1 t.2 := by
      simp [qBellmanUpdate, Function.uncurry, ht]
    constructor
    · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2
      intro s
      apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2
      intro a
      change ‖m.qBellmanUpdate α γ Q p s a - m.qBellmanUpdate α γ R p s a‖ ≤ ‖q - r‖
      by_cases heq : (s, a) = p
      · subst p
        exact hp.trans (mul_le_of_le_one_left (norm_nonneg _) hρ1)
      · exact (congrArg norm (hne (s, a) heq)).le.trans ((norm_entry_le (Q - R) (s, a)).trans ih.1)
    · intro t ht
      by_cases heq : t = p
      · subst t
        exact hp
      · rw [hne t heq]
        exact ih.2 t (by simpa [heq] using ht)

/-- A sweep that visits every entry reduces the sup-norm distance by the relaxation factor. -/
theorem norm_qBellmanSweep_sub_le (m : MDP S A) {α γ : ℝ}
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (q r : S → A → ℝ) (visits : List (S × A)) (hcover : ∀ p, p ∈ visits) :
    ‖m.qBellmanSweep α γ q visits - m.qBellmanSweep α γ r visits‖ ≤
      (1 - α * (1 - γ)) * ‖q - r‖ := by
  have hρ0 : 0 ≤ 1 - α * (1 - γ) := by nlinarith [mul_nonneg hα0 hγ0]
  have hnonneg := mul_nonneg hρ0 (norm_nonneg (q - r))
  apply (pi_norm_le_iff_of_nonneg hnonneg).2
  intro s
  apply (pi_norm_le_iff_of_nonneg hnonneg).2
  intro a
  exact (m.qBellmanSweep_bounds hα0 hα1 hγ0 hγ1 q r visits).2 (s, a) (hcover (s, a))

private theorem qBellmanSweep_fixed (m : MDP S A) (α γ : ℝ) (q : S → A → ℝ)
    (hq : m.qBellmanOperator γ q = q) (visits : List (S × A)) :
    m.qBellmanSweep α γ q visits = q := by
  have hupdate (p : S × A) : m.qBellmanUpdate α γ q p = q := by
    have hm : (1 - α) * q p.1 p.2 + α * q p.1 p.2 = q p.1 p.2 := by ring
    funext s a
    simp only [qBellmanUpdate, hq, hm]
    exact congrFun (Function.update_eq_self p (Function.uncurry q)) (s, a)
  induction visits with
  | nil => rfl
  | cons p ps ih => simpa only [qBellmanSweep, List.foldl_cons, hupdate] using ih

/-- Apply successive sweeps from a schedule, counting completed sweeps. -/
def qBellmanSweepIteration (m : MDP S A) (α γ : ℝ) (q₀ : S → A → ℝ)
    (schedule : ℕ → List (S × A)) : ℕ → S → A → ℝ
  | 0 => q₀
  | n + 1 => m.qBellmanSweep α γ (m.qBellmanSweepIteration α γ q₀ schedule n) (schedule n)

/-- Each complete sweep contributes one relaxation factor to the fixed-point error bound. -/
theorem norm_qBellmanSweepIteration_sub_le (m : MDP S A) {α γ : ℝ}
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (q₀ q : S → A → ℝ) (hq : m.qBellmanOperator γ q = q)
    (schedule : ℕ → List (S × A)) (hcover : ∀ n p, p ∈ schedule n) (n : ℕ) :
    ‖m.qBellmanSweepIteration α γ q₀ schedule n - q‖ ≤
      (1 - α * (1 - γ)) ^ n * ‖q₀ - q‖ := by
  have hρ0 : 0 ≤ 1 - α * (1 - γ) := by nlinarith [mul_nonneg hα0 hγ0]
  induction n with
  | zero => simp [qBellmanSweepIteration]
  | succ n ih =>
    have h := m.norm_qBellmanSweep_sub_le hα0 hα1 hγ0 hγ1
      (m.qBellmanSweepIteration α γ q₀ schedule n) q (schedule n) (hcover n)
    rw [m.qBellmanSweep_fixed α γ q hq] at h
    calc
      ‖m.qBellmanSweepIteration α γ q₀ schedule (n + 1) - q‖ ≤
          (1 - α * (1 - γ)) * ‖m.qBellmanSweepIteration α γ q₀ schedule n - q‖ := h
      _ ≤ (1 - α * (1 - γ)) * ((1 - α * (1 - γ)) ^ n * ‖q₀ - q‖) :=
        mul_le_mul_of_nonneg_left ih hρ0
      _ = _ := by rw [pow_succ']; ring

/-- Complete ordered sweeps converge to the Bellman Q fixed point. -/
theorem tendsto_qBellmanSweepIteration (m : MDP S A) {α γ : ℝ}
    (hα0 : 0 < α) (hα1 : α ≤ 1) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (q₀ q : S → A → ℝ) (hq : m.qBellmanOperator γ q = q)
    (schedule : ℕ → List (S × A)) (hcover : ∀ n p, p ∈ schedule n) :
    Filter.Tendsto (m.qBellmanSweepIteration α γ q₀ schedule) Filter.atTop (𝓝 q) := by
  have hρ0 : 0 ≤ 1 - α * (1 - γ) := by nlinarith [mul_nonneg hα0.le hγ0]
  have hρ1 : 1 - α * (1 - γ) < 1 := by
    linarith [mul_pos hα0 (sub_pos.mpr hγ1)]
  apply tendsto_iff_norm_sub_tendsto_zero.2
  apply squeeze_zero (fun _ => norm_nonneg _)
    (m.norm_qBellmanSweepIteration_sub_le hα0.le hα1 hγ0 hγ1.le q₀ q hq schedule hcover)
  simpa only [zero_mul] using
    (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1).mul_const ‖q₀ - q‖

end Rlib.MDP
